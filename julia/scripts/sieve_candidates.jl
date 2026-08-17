# Family-stratified sieve over the Phase-1 candidate corpus.
#
# Usage: julia --project=julia julia/scripts/sieve_candidates.jl [dir ...]
#            [--denom 32] [--families 4] [--per-family 3] [--full-per-family 5]
#            [--starts 4000] [--out artifacts/candidates/sieved] [--report artifacts/results/sieve]
#            [--no-escape]      (turn OFF the escape screen of stage S3b; only
#                                for reproducing a pre-7-Aug-2026 verdict)
#
# WHY THIS EXISTS — the thing it replaces.
#
# `resnap_candidates.jl` sorts every candidate by one Float64 margin and keeps
# the global top ten. Those ten come from a single R: the four payoff rows of
# the singleton coalitions {1}..{N}, i.e. the matrix of unilateral quit
# payoffs. Candidates sharing an R are called a FAMILY here, and the corpus
# that the whole exact ladder ran on — twenty games — turned out to be two
# families of ten. That was never a design decision; it is what `--top 10`
# does when one R dominates the float score.
#
# It matters because R alone decides the directional margin, LCP(R,0), the
# Q-matrix filters and the FAP/APS analysis (`run_phase1.jl` stage A). For
# every one of those rungs, ten members of a family give ten identical
# answers. Breadth in R is the only breadth those rungs can see.
#
# So: sieve wide and cheap here (Float64, seconds per game, many families),
# and let the expensive exact ladder — period 3, the Fritz John margin runs,
# the certificate export — see only a finalist and a reserve.
#
# WHAT THE SIEVE DOES, cheapest gate first.
#
#   S0  exact deduplication on `game_key`. Phase 1 saves a snapshot on every
#       fitness improvement, and two successive improvements can snap to the
#       same game; gen004/gen009 did, and were certified twice.
#   S1  group by `family_key` (the R skeleton of the SNAPPED game — snapping is
#       what the exact ladder sees, and two distinct float R's can land on one
#       rational R).
#   S2  degenerate-indifference scan. Pairs r_S,i = r_{S∖i},i turn a player's
#       indifference equation into 0 = 0, leaving period-3 support systems
#       positive-dimensional and unsolvable by msolve at any time budget. Free
#       to compute, so never pay for it in msolve hours again.
#   S3b THE ESCAPE SCREEN (on by default, off with
#       --no-escape). Simon (2007) Theorem 4 gives every ESCAPE game
#       approximate equilibria, and both Simon papers state a sufficient
#       membership criterion: if `w^j > v^j` for all j forces the only
#       equilibrium of Γ_w to be all-continue, the game is an escape game. So a
#       counterexample MUST admit some ξ ≠ 0 and some x with x_j > v^j for all j
#       making ξ an exact equilibrium of Γ_x. `escape_screen` looks for such a
#       ξ. No witness ⇒ the game (presumably) has approximate equilibria and
#       cannot be a counterexample, whatever it scores below.
#
#       This screen did not exist until 7 Aug 2026 and was never applied to the
#       corpus. Both finalists — the two games the whole exact ladder ran on —
#       fail it, certified (docs/G3_ROUTE_3.md §4.3a). The cost of not having
#       had it is the reason it now runs before the margin battery.
#
#   S3  the Float64 margin battery. m1/m2/m3 are GATES (must be positive);
#       the ranking key is m4.
#   S4  snap to the denominator cap and re-check — a candidate that loses its
#       properties on the coarse grid is dropped here, not in Phase 2.
#   S5  the R-only exact gates, ONCE PER FAMILY: `lcp0_nontrivial` and
#       `aps_fap_analysis`.
#   S6  keep the best `--per-family` of the best `--families`.
#
# WHY FAMILIES ARE RANKED ON m4 AND NOT ON m1. m1 (`min_stationary_violation`)
# only samples profiles with absorption ≥ 0.05. The provable margin δ is set by
# the thin corner at absorption ≈ 1/100, which m1 never visits: gen025 scores
# m1 = 0.214 while its true stratified-domain margin sits in (1/8, 13/100].
# m4 (`min_corner_violation`) searches exactly that corner. It ORDERS, it does
# not bound: its domain has no xmin floor, so it reaches profiles the
# certificate domain excludes, and m4 = 0.1228 for gen025 next to a proved
# δ > 1/8 is not a contradiction. As an ordering it is right where it counts —
# family 2 scores 0.152-0.154 against family 1's 0.123 and duly proved δ = 1/7
# against gen025's 1/8.
#
# WHY THE WITHIN-FAMILY ORDER IS NOT m4. Measured over the twenty certified
# candidates at 16000 multistarts: m4 spans 0.1226-0.1232 across all of family
# 1 and 0.1521-0.1544 across all of family 2, while the gap BETWEEN the two
# families is 0.031 — fifty times the within-family spread. The corner score is
# effectively a property of R, so sorting members of one family by it is
# fitting noise (at 300 starts the order inside a family is not even stable).
# What does vary between siblings, and does decide how expensive they are:
#
#   1. the degenerate-indifference count (0 to 4 among the twenty) — zero
#      first, because a nonzero count is the known period-3 blocker;
#   2. m3, the periodic margin (0.08 to 0.23 among the twenty) — highest
#      first, since period 3 is the rung that costs hours;
#   3. m4 only as a tie-break.
#
# WHY SIX FAMILIES BY DEFAULT, NOT FOUR. Measured on the run of 2 Aug 2026 over
# all 60 R skeletons on disk: the best corner score per family goes 0.156,
# 0.123, 0.073, 0.062, 0.058, 0.050, and on down. Only the first two are
# strong. The temptation is to widen only until the score collapses — but that
# reads the score as if layer 1 needed it, and layer 1 is entirely QUALITATIVE:
# LCP(R,0) trivial, no stationary equilibrium, no periodic equilibrium of
# period 2, no sequentially perfect absorption path. Not one of those carries a
# margin. A family at 0.06 supports the robustness statement exactly as well as
# one at 0.15. The one thing a low score does predict is RISK: the float search
# is finding near-equilibria, so the exact emptiness proof is harder and the
# family may drop out at layer 1 altogether. That argues for more families, not
# stronger ones — six so that a dropout still leaves five.
#
# And it cannot be fixed by searching harder. Correlation between the number of
# candidates an R produced and its best corner score: 0.213. The three most
# searched skeletons (19, 17 and 15 candidates) score 0.027, 0.026 and 0.013;
# the fourth-best family has two candidates. Quality is in R, not in the
# campaign. Getting a THIRD family of the top two's calibre means new draws at
# a base rate of 2 in 60.
#
# Nothing here is a proof. Every number is a Float64 heuristic whose only job
# is to decide what deserves exact certification.

using QuittingGames
using Printf

include(joinpath(@__DIR__, "paths.jl"))
const ROOT = REPO_ROOT

# ---------------------------------------------------------------------------
# arguments

dirs = String[]
denom, nfamilies, per_family, full_per_family, starts = 32, 6, 3, 5, 4000
outdir, reportdir = "artifacts/candidates/sieved", "artifacts/results/sieve"
escape_screen_on = true
let i = 1
    global denom, nfamilies, per_family, full_per_family, starts, outdir, reportdir,
           escape_screen_on
    while i <= length(ARGS)
        a = ARGS[i]
        if     a == "--no-escape";       escape_screen_on = false;                i += 1
        elseif a == "--denom";           denom           = parse(Int, ARGS[i+1]); i += 2
        elseif a == "--families";        nfamilies       = parse(Int, ARGS[i+1]); i += 2
        elseif a == "--per-family";      per_family      = parse(Int, ARGS[i+1]); i += 2
        elseif a == "--full-per-family"; full_per_family = parse(Int, ARGS[i+1]); i += 2
        elseif a == "--starts";          starts          = parse(Int, ARGS[i+1]); i += 2
        elseif a == "--out";             outdir          = ARGS[i+1];             i += 2
        elseif a == "--report";          reportdir       = ARGS[i+1];             i += 2
        else   push!(dirs, a); i += 1
        end
    end
end
if isempty(dirs)
    if isdir(CANDIDATES)
        append!(dirs, sort(["artifacts/candidates/" * d for d in readdir(CANDIDATES)
                            if isdir(joinpath(CANDIDATES, d))]))
    end
    filter!(d -> isdir(joinpath(ROOT, d)), dirs)
end

# ---------------------------------------------------------------------------
# helpers

"Load a candidate file into a throwaway module (the batch scripts' convention)."
function load_candidate(f)
    m = Module(:SieveSandbox)
    Core.eval(m, :(using QuittingGames))
    Base.include(m, abspath(f))
    Base.invokelatest(() -> getglobal(m, :candidate)())
end

"""
Provenance rank of a source directory: lower wins a deduplication tie. Files
already in a certified corpus are preferred, so a game that also appears as a
raw Phase-1 snapshot keeps the name its existing results are filed under.
"""
provenance(path) = occursin("resnapped", path) ? 0 : 1

qstr(c::Rational) = denominator(c) == 1 ? string(numerator(c)) :
                    string(numerator(c), "//", denominator(c))

rmatrix_str(g) = join([join([qstr(Rational{BigInt}(g.r[1 << (j - 1), i]))
                             for i in 1:g.N], " ") for j in 1:g.N], "; ")

# ---------------------------------------------------------------------------
# S0-S2: load, snap, deduplicate, group, scan

files = String[]
for d in dirs
    dd = joinpath(ROOT, d)
    isdir(dd) || continue
    append!(files, sort([joinpath(dd, f) for f in readdir(dd) if endswith(f, ".jl")]))
end
isempty(files) && (println("no candidate files in ", join(dirs, ", ")); exit(0))

println("sieving ", length(files), " files from ", length(dirs), " directories",
        " (snap denominator <= ", denom, ")\n")

mutable struct Cand
    path::String
    game::QuittingGame{Rational{Int}}   # SNAPPED: what the exact ladder sees
    key::String
    fam::String
    degen::Int
    degen_full::Int
    viable::Bool
    reason::String
    escape::Symbol                      # :violates (keep) / :no_witness (drop) / :off
    escape_kind::Symbol
    m1::Float64
    m2::Float64
    m3::Float64
    m4::Float64
    full::Bool                          # heavy battery ran on this one
end

bykey = Dict{String,Cand}()
ndup = 0
duplicates = Vector{Tuple{String,String}}()
for f in files
    global ndup            # soft scope: `ndup += 1` below would make a local
    local gs
    try
        gs = rationalize_game(convert(QuittingGame{Float64}, load_candidate(f)); denom = denom)
    catch e
        @printf("  skipped %s: %s\n", basename(f), sprint(showerror, e))
        continue
    end
    gq = convert(QuittingGame{Rational{BigInt}}, gs)
    k = game_key(gq)
    if haskey(bykey, k)
        ndup += 1
        old = bykey[k]
        if provenance(f) < provenance(old.path)
            push!(duplicates, (relpath(old.path, ROOT), relpath(f, ROOT)))
            old.path = f
        else
            push!(duplicates, (relpath(f, ROOT), relpath(old.path, ROOT)))
        end
        continue
    end
    # `family_key`, not `family_fingerprint`: grouping is an equality question
    # and digests collide. The digest is for the report only.
    bykey[k] = Cand(f, gs, k, family_key(gq),
                    length(degenerate_indifference_pairs(gq)),
                    full_coalition_degeneracies(gq),
                    false, "", :off, :none, NaN, NaN, NaN, NaN, false)
end
# sorted, not in Dict order, so two runs on the same input agree byte for byte
cands = sort(collect(values(bykey)); by = c -> c.path)
@printf("S0  %d distinct games (%d duplicate files collapsed)\n", length(cands), ndup)

fams = Dict{String,Vector{Cand}}()
for c in cands
    push!(get!(fams, c.fam, Cand[]), c)
end
@printf("S1  %d families (R skeletons); sizes %d..%d\n",
        length(fams), minimum(length.(values(fams))), maximum(length.(values(fams))))

# ---------------------------------------------------------------------------
# S3 (cheap pass): filters + m1 + m2 + m4 on every distinct game

print("S3  cheap battery ")
nfilter_viable = 0
nescape_dropped = 0
for c in cands
    global nfilter_viable, nescape_dropped   # soft scope, like `ndup`
    gq = convert(QuittingGame{Rational{BigInt}}, c.game)
    gf = convert(QuittingGame{Float64}, c.game)
    # F1-F8 only: the escape screen is stage S3b below, so that the report can
    # say how many candidates EACH of the two removes.
    rep = filter_report(gq; qtrials = 200, escape = false)
    c.viable = rep.viable
    c.reason = rep.viable ? "" : first(rep.reasons)
    nfilter_viable += rep.viable
    # S3b: Simon's escape criterion. A game with no witness has approximate
    # equilibria (presumed) and can never be a counterexample.
    if escape_screen_on && c.viable
        sc = escape_screen(gq; starts = 128)
        c.escape = sc.status
        c.escape_kind = sc.status === :violates ? sc.witness.kind : :none
        if sc.status === :no_witness
            c.viable = false
            c.reason = "F9: no escape-criterion witness (presumed escape game, Simon 2007 Thm 4)"
            nescape_dropped += 1
        end
    end
    if c.viable
        c.m1, _ = min_stationary_violation(gf; starts = 300)
        c.m2, _ = min_directional_violation_grid(gf)
        c.m4, _ = min_corner_violation(gf; starts = 300)
    end
end
@printf("\n    %d of %d survive the existence filters F1-F8\n", nfilter_viable, length(cands))
escape_screen_on &&
    @printf("    S3b escape screen: %d of those %d dropped (no witness against Simon's criterion), %d violate it and stay\n",
            nescape_dropped, nfilter_viable, nfilter_viable - nescape_dropped)

# ---------------------------------------------------------------------------
# S3/S4 (heavy pass): the periodic margins and high-multistart scores, only for
# the best few per family. m3 at k = 3 costs ~2.5 s and is the reason this is
# not run on everything.

print("S4  heavy battery ")
for fkey in sort(collect(keys(fams)))
    cs = fams[fkey]
    # Preselect on what actually distinguishes siblings — see the header: the
    # degeneracy count first, the cheap corner score only as a tie-break.
    pool = sort(filter(c -> c.viable && c.m1 > 1e-6 && c.m2 > 1e-6, cs);
                by = c -> (c.degen, -c.m4))
    for c in pool[1:min(full_per_family, end)]
        gf = convert(QuittingGame{Float64}, c.game)
        c.m1, _ = min_stationary_violation(gf; starts = starts)
        c.m4, _ = min_corner_violation(gf; starts = starts)
        p2, _ = min_periodic_violation(gf, 2; starts = 300)
        p3, _ = min_periodic_violation(gf, 3; starts = 300)
        c.m3 = min(p2, p3)
        c.full = true
        print(".")
    end
end
println()

surv(c) = c.full && c.viable && c.m1 > 1e-6 && c.m2 > 1e-6 && c.m3 > 1e-6 && c.m4 > 1e-6

# ---------------------------------------------------------------------------
# S5: the R-only exact gates, once per family instead of once per candidate

struct FamInfo
    id::String
    rmat::String
    n::Int
    best::Float64
    lcp_trivial::Bool
    aps::Symbol
    members::Vector{Cand}
end

print("S5  family gates ")
infos = FamInfo[]
for fkey in sort(collect(keys(fams)))
    cs = fams[fkey]
    ok = filter(surv, cs)
    isempty(ok) && continue
    best = maximum(c -> c.m4, ok)             # families are ranked on this
    sort!(ok; by = c -> (c.degen, -c.m3, -c.m4))   # members are not — see header
    rep = convert(QuittingGame{Rational{BigInt}}, first(ok).game)
    lcp = lcp0_nontrivial(unilateral_matrix(rep)) === nothing
    aps = first(aps_fap_analysis(rep; maxiter = 60))
    push!(infos, FamInfo(family_fingerprint(rep), rmatrix_str(rep), length(cs),
                         best, lcp, aps, ok))
    print(".")
end
println()
sort!(infos; by = f -> (-f.best, f.id))       # id breaks ties reproducibly
@printf("    %d families have at least one surviving candidate\n", length(infos))

# ---------------------------------------------------------------------------
# S6: selection and output

passing = filter(f -> f.lcp_trivial && f.aps == :no_fap, infos)
chosen = passing[1:min(nfamilies, end)]

wide = joinpath(ROOT, outdir, "wide")
mkpath(wide)
for f in readdir(wide; join = true)
    endswith(f, ".jl") && rm(f)
end
written = String[]
for f in chosen, c in f.members[1:min(per_family, end)]
    name = @sprintf("f%s_m4-%.4f_%s", f.id, c.m4, basename(c.path))
    name = replace(name, r"^f([0-9a-f]+)_m4-([0-9.]+)_(resnap_d\d+_[0-9.]+_)?" => s"f\1_m4-\2_")
    path = joinpath(wide, name)
    open(path, "w") do io
        println(io, "# sieved from ", relpath(c.path, ROOT), " (snap denominator <= ", denom, ")")
        println(io, "# family ", f.id, "  game ", game_fingerprint(c.game))
        println(io, "# float scores: m1=", c.m1, " m2=", c.m2, " m3=", c.m3, " m4=", c.m4)
        println(io, "# escape screen (S3b): ", c.escape,
                c.escape === :violates ? string(" (witness kind: ", c.escape_kind, ")") : "")
        println(io, "# degenerate indifference pairs: ", c.degen,
                " (", c.degen_full, " at the full coalition)")
        println(io, "using QuittingGames")
        println(io, "candidate() = QuittingGame(", c.game.N, ", Matrix{Rational{Int}}(")
        println(io, "    ", repr(Matrix{Rational{Int}}(c.game.r)), "))")
    end
    push!(written, name)
end
@printf("S6  wrote %d candidates from %d families to %s\n",
        length(written), length(chosen), joinpath(outdir, "wide"))

# ---------------------------------------------------------------------------
# report

mkpath(joinpath(ROOT, reportdir))
open(joinpath(ROOT, reportdir, "report.md"), "w") do io
    println(io, "# Candidate sieve report")
    println(io)
    println(io, "GENERATED by `julia/scripts/sieve_candidates.jl` -- do not edit.")
    println(io, "Every number here is a Float64 heuristic; nothing is proved.")
    println(io)
    println(io, "Sources: ", join(["`" * d * "`" for d in dirs], ", "))
    println(io, "Snap denominator: ", denom, ". Multistarts (heavy pass): ", starts, ".")
    println(io)
    println(io, "| stage | outcome |")
    println(io, "|---|---|")
    println(io, "| files read | ", length(files), " |")
    println(io, "| S0 distinct games | ", length(cands), " (", ndup, " duplicate files) |")
    println(io, "| S1 families | ", length(fams), " |")
    println(io, "| S3 survive the filters F1-F8 | ", nfilter_viable, " |")
    escape_screen_on &&
        println(io, "| S3b survive the escape screen | ", nfilter_viable - nescape_dropped,
                " (", nescape_dropped, " dropped) |")
    println(io, "| S5 families with a survivor | ", length(infos), " |")
    println(io, "| S5 families passing the R gates | ", length(passing), " |")
    println(io, "| S6 selected | ", length(written), " games from ",
            length(chosen), " families |")
    println(io)

    if escape_screen_on
        println(io, "## The escape screen (S3b)")
        println(io)
        println(io, "Simon (2007) Theorem 4: every **escape game** has approximate ",
                "equilibria. Both Simon papers give a sufficient membership criterion — ",
                "if `w^j > v^j` for all players forces the only equilibrium of `Γ_w` to ",
                "be all-continue, the game is an escape game — so a counterexample MUST ",
                 "admit some `ξ ≠ 0` and some `x` with `x_j > v^j` for every `j` such that ",
                 "`ξ` is an exact equilibrium of `Γ_x`.")
        println(io)
        println(io, "**Read the two verdicts differently.** A witness is a PROOF (exact ",
                "rational `ξ`, re-checked against the bare definition of a one-stage ",
                "equilibrium). \"No witness\" is a SCREEN, not a proof: supports of size ",
                "≥ 3 are searched in Float64.")
        println(io)
        println(io, "| escape verdict | games | of which |")
        println(io, "|---|---|---|")
        nviol = count(c -> c.escape === :violates, cands)
        println(io, "| violates the criterion (kept) | ", nviol, " | ",
                join([string(k, ": ", count(c -> c.escape === :violates && c.escape_kind === k, cands))
                      for k in (:pair, :mixed, :quitter)], ", "), " |")
        println(io, "| no witness found (dropped) | ", nescape_dropped, " | screen only |")
        println(io, "| not screened (F1-F8 already fired) | ",
                length(cands) - nviol - nescape_dropped, " | — |")
        println(io)
        println(io, "This screen was applied to the corpus for the first time on ",
                "7 Aug 2026. Both games then furthest along the ladder failed it.")
        println(io)
    end

    if !isempty(duplicates)
        println(io, "## Duplicate games")
        println(io)
        println(io, "Distinct files, identical payoff tables after snapping. ",
                "The kept file is the one with certified provenance.")
        println(io)
        println(io, "| dropped | same game as |")
        println(io, "|---|---|")
        for (a, b) in duplicates
            println(io, "| `", a, "` | `", b, "` |")
        end
        println(io)
    end

    println(io, "## Families")
    println(io)
    println(io, "Ranked by the best corner score `m4` among their surviving members. ")
    println(io, "`LCP` and `APS` are exact and depend on R only, so they are one ",
            "verdict per family, not per candidate.")
    println(io)
    println(io, "**Coverage cap:** at most ", full_per_family, " members per family got the ",
            "heavy battery (the periodic margins cost ~3 s each), so `survivors` counts ",
            "those, not the whole family. A family with 0 survivors had its ",
            min(full_per_family, 99), " best-looking members tested and all of them fail a ",
            "gate — it is not silently untested.")
    println(io)
    println(io, "| family | cands | survivors | best m4 | LCP(R,0) trivial | APS | selected |")
    println(io, "|---|---|---|---|---|---|---|")
    for f in infos
        sel = f in chosen ? min(per_family, length(f.members)) : 0
        @printf(io, "| `%s` | %d | %d | %.4f | %s | %s | %d |\n",
                f.id, f.n, length(f.members), f.best,
                f.lcp_trivial ? "yes" : "**no**", f.aps, sel)
    end
    println(io)

    println(io, "## Selected candidates")
    println(io)
    println(io, "Ordered WITHIN a family by degenerate-indifference count (ascending), ",
            "then by the periodic margin m3 (descending). Not by m4: that score barely ",
            "moves between siblings — it is a property of R — so ordering on it would ",
            "be fitting noise. See the header of `scripts/sieve_candidates.jl`.")
    println(io)
    println(io, "| family | file | m1 | m2 | m3 | m4 | escape | degen | degen(full) |")
    println(io, "|---|---|---|---|---|---|---|---|---|")
    for f in chosen, c in f.members[1:min(per_family, end)]
        @printf(io, "| `%s` | `%s` | %.4f | %.4f | %.4f | %.4f | %s | %d | %d |\n",
                f.id, basename(c.path), c.m1, c.m2, c.m3, c.m4,
                c.escape === :violates ? string("violates (", c.escape_kind, ")") :
                    string(c.escape), c.degen, c.degen_full)
    end
    println(io)
    println(io, "Calibration: two games known to have no stationary equilibrium score ",
            "0.1738 (Flesch-Thuijsman-Vrieze 1997) and 0.0502 (Solan-Vieille 4p) on ",
            "the m1 scale.")
    println(io)
    println(io, "## What happens next")
    println(io)
    println(io, "The files in `", joinpath(outdir, "wide"), "` are a shortlist. ",
            "They still have to be certified. This script does not certify.")
    println(io)
    println(io, "Best of the top two families from this run:")
    println(io)
    for f in chosen[1:min(2, end)]
        c = first(f.members)
        println(io, "  - `", relpath(c.path, ROOT), "` (family `", f.id,
                "`, m4 = ", @sprintf("%.4f", c.m4), ")")
    end
end

open(joinpath(ROOT, reportdir, "families.json"), "w") do io
    println(io, "{")
    println(io, "  \"denom\": ", denom, ",")
    println(io, "  \"families\": [")
    for (n, f) in enumerate(infos)
        println(io, "    {")
        println(io, "      \"id\": \"", f.id, "\",")
        println(io, "      \"r\": \"", f.rmat, "\",")
        println(io, "      \"candidates\": ", f.n, ",")
        println(io, "      \"survivors\": ", length(f.members), ",")
        println(io, "      \"best_m4\": ", f.best, ",")
        println(io, "      \"lcp0_trivial\": ", f.lcp_trivial, ",")
        println(io, "      \"aps\": \"", f.aps, "\",")
        println(io, "      \"selected\": ", f in chosen)
        println(io, "    }", n == length(infos) ? "" : ",")
    end
    println(io, "  ]")
    println(io, "}")
end

println("\nreport: ", joinpath(reportdir, "report.md"), " and families.json")
