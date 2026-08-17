# Phase-1 heuristic search for 4-player counterexample candidates.
#
# Usage:  julia --project=julia julia/scripts/run_phase1.jl [--seed N] [--gens N] [--pop N]
#                                               [--rmats N] [--out DIR]
#                                               [--escape-tol X] [--no-escape]
#
# Two-level architecture (motivated by the theory: the unilateral matrix R
# alone determines the directional margin m2 and the filters F6/F7/F8, while
# the multi-quit payoffs govern discrete-jump structure, m1 and m3):
#
#   Stage A: sample zero-diagonal unilateral matrices R in the FRONTIER GAP —
#            LCP(R,0) trivial-only, R standard-Q (no Monte-Carlo witness),
#            some principal minor certified non-AKRS-Q. (~2% of random draws.)
#   Stage B: for each gap R, differential evolution over the 44 multi-quit
#            payoffs, maximizing fitness = min(m1, m2, m3, m4) under the filter
#            battery AND under the escape gate below.
#
# Normalization of this campaign: r_{i},i = 1 for every player.
#
# THE ESCAPE GATE (new on 7 Aug 2026; P2 of planning/plan.md). Simon (2007)
# Theorem 4 gives every ESCAPE game approximate equilibria, and a game is one
# as soon as "w^j > v^j for all j" forces the only equilibrium of Γ_w to be
# all-continue. So a counterexample must admit some ξ ≠ 0 and some x with
# x_j > v^j for all j making ξ an exact equilibrium of Γ_x. That is `m5`
# (`escape_margin`): it must be positive — comfortably, see `--escape-tol` —
# before m1…m4 are looked at at all.
#
# Why this is at the front and not at the back. The previous campaigns did not
# have this screen, and the two games that came out of them and carried the
# whole exact ladder for months are BOTH escape games (certified,
# docs/G3_ROUTE_3.md §4.3a) — they could never have been counterexamples. The
# gate costs about a millisecond per evaluation.
#
# Where the gate bites, concretely. On a two-element support the criterion is
# closed-form: K_j = ξ_k·M[j,k] with M[j,k] = r^{jk}_j − r^{k}_j, so a witness
# needs a positive 2-CYCLE in M. The diagonal blocks of M are fixed by R (which
# Stage A samples), but its off-diagonal is exactly what Stage B optimises, so
# the gate is a condition differential evolution can actually climb — and `m5`
# is signed, so the score below hands it a gradient instead of a flat -Inf.

using QuittingGames
using Random
using Printf

include(joinpath(@__DIR__, "paths.jl"))

const N = 4
const LO, HI = -2.0, 2.0
const QQ = Rational{BigInt}
const SINGLE_MASKS = [1 << (i - 1) for i in 1:N]
const MULTI_MASKS = [m for m in 1:(2^N - 1) if count_ones(m) >= 2]

function parse_args()
    seed, gens, pop, rmats = 1, 40, 32, 6
    out = CANDIDATES
    # 1/16: snapping to denominator 32 moves a payoff by up to 1/64, and an
    # entry of the pair matrix M is a difference of two such entries, so a
    # witness below 1/32 need not survive the snap at all. 1/16 leaves room.
    escape_tol = 1 / 16
    escape = true
    args = copy(ARGS)
    while !isempty(args)
        a = popfirst!(args)
        a == "--seed" && (seed = parse(Int, popfirst!(args)); continue)
        a == "--gens" && (gens = parse(Int, popfirst!(args)); continue)
        a == "--pop" && (pop = parse(Int, popfirst!(args)); continue)
        a == "--rmats" && (rmats = parse(Int, popfirst!(args)); continue)
        a == "--out" && (out = popfirst!(args); continue)
        a == "--escape-tol" && (escape_tol = parse(Float64, popfirst!(args)); continue)
        a == "--no-escape" && (escape = false; continue)
        error("unknown argument $a")
    end
    (; seed, gens, pop, rmats, out, escape_tol, escape)
end

# --- Stage A: gap matrices -------------------------------------------------

"""
Sample a shifted unilateral matrix R (zero diagonal, rational entries) in the
frontier gap AND with certified absence of sequentially perfect FAPs (no
continuous equilibria, which depend on R only).
Returns (R, minor_players, witness_q) or nothing.
"""
function sample_gap_matrix(rng)
    R = Matrix{QQ}(undef, N, N)
    for i in 1:N, j in 1:N
        R[i, j] = i == j ? QQ(0) : QQ(rand(rng, -6:6), rand(rng, 1:3))
    end
    lcp0_nontrivial(R) === nothing || return nothing
    q_matrix_witness(R; trials = 60, rng = rng) === nothing || return nothing
    hit = nothing
    for mask in 1:(2^N - 2)
        players = [i for i in 1:N if (mask >> (i - 1)) & 1 == 1]
        length(players) >= 2 || continue
        M = R[players, players]
        lcp0_nontrivial(M) === nothing || continue
        w = q_matrix_witness(M; trials = 30, rng = rng)
        if w !== nothing
            hit = (players, w)
            break
        end
    end
    hit === nothing && return nothing
    # APS screen: continuous equilibria are determined by R alone; require a
    # certified :no_fap so every candidate on this R has none.
    r = zeros(QQ, 2^N - 1, N)
    for j in 1:N, i in 1:N
        r[SINGLE_MASKS[j], i] = R[i, j]
    end
    st, _, _ = aps_fap_analysis(QuittingGame(N, r); maxiter = 40)
    st == :no_fap || return nothing
    (R, hit[1], hit[2])
end

# --- genome (Stage B): the 44 multi-quit payoffs ---------------------------

genome_length() = length(MULTI_MASKS) * N

function build_game(R::Matrix{QQ}, v::Vector{Float64})
    r = Matrix{Float64}(undef, 2^N - 1, N)
    for j in 1:N, i in 1:N            # unilateral rows from R (unshift by c=1)
        r[SINGLE_MASKS[j], i] = i == j ? 1.0 : Float64(R[i, j]) + 1.0
    end
    idx = 1
    for m in MULTI_MASKS, j in 1:N
        r[m, j] = v[idx]
        idx += 1
    end
    QuittingGame(N, r)
end

function evaluate(R, v, cfg; rng)
    fitness(build_game(R, v); K = 3, qtrials = 24, starts = 40, rng = rng,
            escape = cfg.escape, escape_starts = 32, escape_tol = cfg.escape_tol)
end

# --- Stage B: differential evolution over multi-quit payoffs ---------------

function optimize_multiquit(R, minor_info, cfg, rng, out, rindex::Int = 1)
    L = genome_length()
    pop = [ (HI - LO) .* rand(rng, L) .+ LO for _ in 1:cfg.pop ]
    # seed a few structured members: multi-quit payoffs low (near punishment)
    pop[1] = fill(-1.0, L)
    pop[2] = fill(0.0, L)
    fit = fill(-Inf, cfg.pop)
    det = Vector{Any}(undef, cfg.pop)
    for p in 1:cfg.pop
        f = evaluate(R, pop[p], cfg; rng)
        fit[p] = f.value
        det[p] = f
    end
    F, CR = 0.7, 0.9
    bestever = -Inf
    for gen in 1:cfg.gens
        for p in 1:cfg.pop
            a, b, c = rand(rng, 1:cfg.pop), rand(rng, 1:cfg.pop), rand(rng, 1:cfg.pop)
            trial = copy(pop[p])
            jrand = rand(rng, 1:L)
            for j in 1:L
                if j == jrand || rand(rng) < CR
                    trial[j] = clamp(pop[a][j] + F * (pop[b][j] - pop[c][j]), LO, HI)
                end
            end
            f = evaluate(R, trial, cfg; rng)
            if f.value > fit[p] || (!isfinite(fit[p]) && isfinite(f.value))
                pop[p], fit[p], det[p] = trial, f.value, f
            end
        end
        b = argmax(fit)
        # `escaped` counts the members that are through the escape gate — the
        # DE first has to climb out of the escape class, and a run where this
        # column stays at 0 is a run that never had a candidate at all.
        nesc = count(p -> isfinite(fit[p]) && fit[p] > 0, 1:cfg.pop)
        @printf("    gen %3d  best %.5f  viable %d/%d  escaped %d/%d\n", gen, fit[b],
                count(isfinite, fit), cfg.pop, nesc, cfg.pop)
        flush(stdout)
        if fit[b] > 0 && isfinite(fit[b]) && fit[b] > bestever
            bestever = fit[b]
            save_candidate(out, cfg.seed, gen, R, minor_info, pop[b], det[b], cfg.escape,
                           rindex)
        end
    end
    bestever
end

"""
`rindex` is the index of the R skeleton within this campaign, and it is in the
FILENAME on purpose. Without it a candidate from R skeleton 2 silently
overwrites one from skeleton 1 whenever the generation number and the
four-decimal fitness happen to agree — which is exactly what they do in the
early generations, where the fitness prints as 0.0000 for every skeleton. The
runs `run1`…`run8` on disk were written without it.
"""
function save_candidate(dir, seed, gen, R, minor_info, v, f, escape_gate::Bool = true,
                        rindex::Int = 1)
    g = build_game(R, v)
    gq = rationalize_game(g; denom = 32)
    # The escape verdict of the SNAPPED game is the one that counts: everything
    # exact downstream sees the snapped table, and snapping can destroy a thin
    # witness. Screened exactly here, and the witness is confirmed against the
    # bare definition of a one-stage equilibrium inside `escape_screen`.
    esc = escape_screen(convert(QuittingGame{Rational{BigInt}}, gq); starts = 256)
    if escape_gate && esc.status !== :violates
        @printf("    NOT saved (gen %d): the snapped game has no escape witness (float m5 = %.5f)\n",
                gen, f.m5)
        return
    end
    path = joinpath(dir, @sprintf("cand_seed%d_r%02d_gen%03d_%.4f.jl",
                                  seed, rindex, gen, f.value))
    open(path, "w") do io
        println(io, "# Phase-1 candidate  fitness=$(f.value)")
        println(io, "#   m1(stationary)=$(f.m1)  m2(directional)=$(f.m2)  m3(periodic)=$(f.m3)  m4(corner)=$(f.m4)")
        println(io, "#   m5(escape, float)=$(f.m5)")
        if esc.status === :violates
            println(io, "# escape screen on the SNAPPED game: violates Simon's criterion, ",
                    "witness kind $(esc.witness.kind) on support $(esc.witness.support), ",
                    "exact margin $(esc.margin)")
            println(io, "#   xi = $(esc.witness.ξ)")
            println(io, "#   x  = $(esc.witness.x)   (every x_j > v^j; confirmed against the bare definition)")
        else
            println(io, "# escape screen on the SNAPPED game: NO witness — presumed escape game, ",
                    "presumed to have approximate equilibria, NOT a counterexample candidate ",
                    "(saved only because the escape gate was switched off)")
        end
        println(io, "# gap matrix minor: players=$(minor_info[1]) witness_q=$(minor_info[2])")
        println(io, "# R (shifted unilateral) = $(repr(R))")
        println(io, "using QuittingGames")
        println(io, "candidate() = QuittingGame(4, Matrix{Rational{Int}}(")
        println(io, "    ", repr(Matrix{Rational{Int}}(gq.r)), "))")
    end
    println("    saved ", basename(path))
end

function main()
    cfg = parse_args()
    rng = Random.Xoshiro(cfg.seed)
    mkpath(cfg.out)
    println("escape gate: ", cfg.escape ? "ON (m5 > $(cfg.escape_tol))" :
            "OFF — pre-P2 behaviour, candidates may be escape games")
    nfound = 0
    attempts = 0
    while nfound < cfg.rmats && attempts < 200_000
        attempts += 1
        s = sample_gap_matrix(rng)
        s === nothing && continue
        nfound += 1
        R, players, w = s
        println("R matrix $nfound (attempt $attempts): non-AKRS-Q minor $players, witness $w")
        show(stdout, "text/plain", R); println()
        optimize_multiquit(R, (players, w), cfg, rng, cfg.out, nfound)
    end
    println("done: $nfound gap matrices processed after $attempts attempts")
end

# PROGRAM_FILE guard — added 14 Aug 2026, after `n1_carrier_dmod_lp.jl` was
# `include`d for a syntax check and silently ran its full master for 40 minutes
# with no log and no reader. `include` is only a safe syntax check when this
# guard is present. Do not remove it.
if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
