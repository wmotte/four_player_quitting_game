# Existence-class filters. Every filter, when it FIRES, certifies (by a known
# theorem) that the game possesses some equilibrium, so the game is rejected
# as a counterexample candidate. See docs/VERIFICATION_TARGET.md for sources.
#
# All Solan–Solan ([SS]) conditions are evaluated on the SS-shifted payoffs
# r̃^S_j = r^S_j − c_j with c_j = r_{j},j (so r̃_{j},j = 0 and the never-quit
# payoff becomes −c).

"""
    ss_shifted(g) -> (c, rt)

Per-player shift `c_j = r_{j},j` and the shifted payoff matrix `rt`.
"""
function ss_shifted(g::QuittingGame{T}) where {T}
    N = g.N
    c = [g.r[1 << (i - 1), i] for i in 1:N]
    rt = copy(g.r)
    for m in 1:(2^N - 1), j in 1:N
        rt[m, j] -= c[j]
    end
    c, rt
end

"""
    normal_players(g) -> Vector{Int}

The set `I_*` of normal players ([SS] Def. 2.5): the largest fixed point of
`I ↦ {i ∈ I : ∃ j ∈ I, j ≠ i, r̃^{j}_i ≤ 0}`.
"""
function normal_players(g::QuittingGame)
    _, rt = ss_shifted(g)
    N = g.N
    active = trues(N)
    while true
        changed = false
        for i in 1:N
            active[i] || continue
            ok = any(j -> j != i && active[j] && rt[1 << (j - 1), i] <= 0, 1:N)
            if !ok
                active[i] = false
                changed = true
            end
        end
        changed || break
    end
    findall(active)
end

"""
    unilateral_matrix(g, players = 1:g.N) -> Matrix

The matrix whose (k,l) entry is `r̃^{players[l]}_{players[k]}` — column `l` is
the shifted unilateral-quit payoff vector of player `players[l]`, restricted
to `players`. With `players = normal_players(g)` this is [SS]'s `R̂`; with all
players it is [AKRS]'s `R(Γ)` (transposed convention: our columns are their
columns — entry (i,j) = payoff to i when j quits alone).
"""
function unilateral_matrix(g::QuittingGame{T}, players::AbstractVector{<:Integer} = 1:g.N) where {T}
    _, rt = ss_shifted(g)
    n = length(players)
    R = Matrix{T}(undef, n, n)
    for (l, j) in enumerate(players), (k, i) in enumerate(players)
        R[k, l] = rt[1 << (j - 1), i]
    end
    R
end

# ---------------------------------------------------------------------------
# Exact homogeneous linear feasibility via Fourier–Motzkin (small dimensions).
# Decides whether ∃ y: a·y ≥ 0 for all (a, false) and a·y > 0 for all (a, true).
# ---------------------------------------------------------------------------

function _fm_feasible(cons::Vector{Tuple{Vector{T},Bool}}, nvars::Int) where {T}
    if nvars == 0
        return all(!strict for (_, strict) in cons)   # each row reduced to 0 ≥/> 0
    end
    k = nvars
    pos = Tuple{Vector{T},Bool}[]
    neg = Tuple{Vector{T},Bool}[]
    rest = Tuple{Vector{T},Bool}[]
    for (a, s) in cons
        if a[k] > 0
            push!(pos, (a, s))
        elseif a[k] < 0
            push!(neg, (a, s))
        else
            push!(rest, (a, s))
        end
    end
    # If no positive (or no negative) rows, var k is unbounded in one direction:
    # those constraints can always be satisfied; keep only the k-free rows.
    if !isempty(pos) && !isempty(neg)
        for (a, sa) in pos, (b, sb) in neg
            comb = (-b[k]) .* a .+ a[k] .* b
            push!(rest, (comb, sa || sb))
        end
    end
    _fm_feasible([(a[1:k-1], s) for (a, s) in rest], k - 1)
end

"Exact reduced row echelon form; returns (rref matrix, pivot columns)."
function _rref(A::Matrix{T}) where {T}
    A = copy(A)
    m, n = size(A)
    pivots = Int[]
    row = 1
    for col in 1:n
        row > m && break
        piv = findfirst(i -> !iszero(A[i, col]), row:m)
        piv === nothing && continue
        piv += row - 1
        A[row, :], A[piv, :] = A[piv, :], A[row, :]
        A[row, :] ./= A[row, col]
        for i in 1:m
            i == row && continue
            iszero(A[i, col]) && continue
            A[i, :] .-= A[i, col] .* A[row, :]
        end
        push!(pivots, col)
        row += 1
    end
    A, pivots
end

"Exact kernel basis of A (columns span the nullspace)."
function _nullspace(A::Matrix{T}) where {T}
    m, n = size(A)
    R, pivots = _rref(A)
    free = setdiff(1:n, pivots)
    K = zeros(T, n, length(free))
    for (j, f) in enumerate(free)
        K[f, j] = one(T)
        for (i, p) in enumerate(pivots)
            K[p, j] = -R[i, f]
        end
    end
    K
end

"""
    lcp0_nontrivial(R) -> Union{Nothing, Vector{Int}}

Decide exactly (rational arithmetic) whether `LCP(R, 0)` has a nontrivial
solution: `z ≥ 0, z ≠ 0, w = Rz ≥ 0, z_i w_i = 0`. Returns the support of a
solution, or `nothing`. ([SS] Lemma 2.10: nontrivial ⇒ stationary
ε-equilibria exist. Equivalently: a consistent vanishing-approach direction.)
"""
function lcp0_nontrivial(R::Matrix{T}) where {T}
    n = size(R, 1)
    for mask in 1:(2^n - 1)
        α = [i for i in 1:n if (mask >> (i - 1)) & 1 == 1]
        αc = setdiff(1:n, α)
        K = _nullspace(R[α, α])                       # z_α = K y
        size(K, 2) == 0 && continue
        d = size(K, 2)
        cons = Tuple{Vector{T},Bool}[]
        for (idx, _) in enumerate(α)                  # z_i > 0 on the support
            push!(cons, (Vector{T}(K[idx, :]), true))
        end
        W = R[αc, α] * K                              # w off support ≥ 0
        for i in 1:length(αc)
            push!(cons, (Vector{T}(W[i, :]), false))
        end
        _fm_feasible(cons, d) && return α
    end
    nothing
end

# ---------------------------------------------------------------------------
# Q-matrix testing.
# ---------------------------------------------------------------------------

"""
    lcp_solvable(R, q) -> Bool

Decide `LCP(R, q)` solvability by exact support enumeration (complete when
the relevant principal submatrices are nonsingular; degenerate singular
supports fall back to a kernel + FM feasibility check).
"""
function lcp_solvable(R::Matrix{T}, q::Vector{T}) where {T}
    n = size(R, 1)
    for mask in 0:(2^n - 1)
        α = [i for i in 1:n if (mask >> (i - 1)) & 1 == 1]
        αc = setdiff(1:n, α)
        if isempty(α)
            all(q .>= 0) && return true
            continue
        end
        A = R[α, α]
        Rr, pivots = _rref(hcat(A, -q[α]))
        # solve A z_α = -q_α exactly; if inconsistent, skip
        ncols = length(α)
        inconsistent = any(i -> all(iszero, Rr[i, 1:ncols]) && !iszero(Rr[i, ncols + 1]), 1:size(Rr, 1))
        inconsistent && continue
        if length(pivots) == ncols                     # unique solution
            z = zeros(T, ncols)
            for (i, p) in enumerate(pivots)
                p <= ncols || continue
                z[p] = Rr[i, ncols + 1]
            end
            all(z .>= 0) || continue
            w = R[αc, α] * z .+ q[αc]
            all(w .>= 0) && return true
        else
            # affine solution set: z = z0 + K y; check feasibility with FM on
            # the homogenized system (append 1 as last coordinate).
            K = _nullspace(A)
            z0 = zeros(T, ncols)
            for (i, p) in enumerate(pivots)
                p <= ncols || continue
                z0[p] = Rr[i, ncols + 1]
            end
            d = size(K, 2)
            cons = Tuple{Vector{T},Bool}[]
            for i in 1:ncols                            # z ≥ 0
                push!(cons, (vcat(Vector{T}(K[i, :]), z0[i]), false))
            end
            W = R[αc, α]
            for (i, _) in enumerate(αc)                 # w ≥ 0
                row = Vector{T}((W[i:i, :] * K)[1, :])
                push!(cons, (vcat(row, (W[i:i, :]*z0)[1] + q[αc][i]), false))
            end
            push!(cons, (vcat(zeros(T, d), one(T)), true))   # homogenizer > 0
            _fm_feasible(cons, d + 1) && return true
        end
    end
    false
end

"""
    q_matrix_witness(R; trials = 200, rng) -> Union{Nothing, Vector}

Search for a rational vector `q` with `LCP(R, q)` unsolvable — an exact
certificate that `R` is NOT a Q-matrix. Returns the witness or `nothing`
(absence of a witness is Monte-Carlo evidence only that R IS a Q-matrix;
exact Q-certification is Phase-2 work). Deterministic given `rng`.

The deterministic sweep starts with the negative unit vectors `−e_i`. That is
not an arbitrary choice: by the singleton-corner theorem (see
[`singleton_corner_status`](@ref)) an `R` whose singleton corner set is empty
has `LCP(R, −e_i)` infeasible, so this sweep catches EVERY such `R`
deterministically — the Monte-Carlo trials below cannot be trusted to find an
open ball of witnesses, the four unit vectors can be. The corner-sieve
campaign (`scripts/corner_campaign.jl`) relies on this: with the unit vectors
in the sweep, no corner-empty `R` can pass the screen, by proof rather than by
base rate.
"""
function q_matrix_witness(R::Matrix{T}; trials::Int = 200,
                          rng::AbstractRNG = Random.Xoshiro(20260730)) where {T}
    n = size(R, 1)
    # the four negative unit vectors (the corner-emptiness witnesses)
    for i in 1:n
        q = T[-(i == j) for j in 1:n]
        lcp_solvable(R, q) || return q
    end
    # deterministic sweep of sign patterns (q on the unit cube corners)
    for mask in 0:(2^n - 1)
        q = T[(mask >> (i - 1)) & 1 == 1 ? one(T) : -one(T) for i in 1:n]
        lcp_solvable(R, q) || return q
    end
    for _ in 1:trials
        q = T[T(rand(rng, -12:12)) / T(rand(rng, 1:7)) for _ in 1:n]
        lcp_solvable(R, q) || return q
    end
    nothing
end

# ---------------------------------------------------------------------------
# F9: Simon's escape-class screen.
# ---------------------------------------------------------------------------
#
# Simon (2007) Theorem 4: every ESCAPE game has approximate equilibria. Both
# Simon papers state a sufficient membership criterion (Simon 2012 §2.2,
# verbatim):
#
#   "The class of escape games includes any quitting game such that whenever
#    w^j > v^j for all players then the only equilibrium of Γ_w is defined by
#    all players choosing to continue with certainty."
#
# with `v^j = r^{j}_j` the payoff for quitting alone. So a candidate
# counterexample MUST fail this criterion: it must admit some ξ ≠ 0 and some
# continuation vector x with x_j > v^j for every j such that ξ is an EXACT
# equilibrium of the one-stage game Γ_x. A game for which no such (ξ, x) exists
# is an escape game, has approximate equilibria, and can never be a
# counterexample — however well it scores on every other margin in this
# package. See docs/G3_ROUTE_3.md §4.3/§4.3a; the two games the project spent
# months on both fell here, and this screen was never applied to them.
#
# THE CRITERION IN CLOSED FORM. With D_j(ξ,x) = A_j(ξ) − z_j(ξ)·x_j,
# A_j(ξ) = D_j(ξ,0) and z_j(ξ) = ∏_{k≠j}(1−ξ_k), D_j depends on x only through
# x_j and is strictly decreasing in it when z_j > 0. Writing
#
#     K_j(ξ) := D_j(ξ, v) = A_j(ξ) − z_j(ξ)·v^j                (`escape_gap`)
#
# an admissible x with x_j > v^j for all j exists for a given ξ exactly when
#
#   * z_j(ξ) > 0 and ξ_j > 0        ⇒  K_j(ξ) > 0   (a mixer needs
#     x_j = A_j/z_j, a certain quitter x_j ≤ A_j/z_j, and both want x_j > v^j);
#   * z_j(ξ) = 0                    ⇒  K_j ≥ 0 if ξ_j > 0 and K_j ≤ 0 if
#     ξ_j < 1  (x_j has dropped out of j's comparison altogether; note A_j = K_j
#     when z_j = 0);
#   * z_j(ξ) > 0 and ξ_j = 0        ⇒  nothing: a large x_j accommodates j.
#
# K_j is multilinear, has no constant term and does not depend on ξ_j. Two
# consequences make the screen dirt cheap and give it exact closed forms at the
# bottom, which is what `test/runtests.jl` pins it against:
#
#   |supp ξ| = 1:  K_j ≡ 0 identically, in EVERY quitting game. A lone mixer is
#                  indifferent exactly at x_j = v^j and never above it.
#   |supp ξ| = 2:  K_j(ξ) = ξ_k·M[j,k] with M[j,k] = r^{jk}_j − r^{k}_j
#                  (`escape_pair_matrix`), so a witness on {j,k} exists exactly
#                  when M[j,k] > 0 AND M[k,j] > 0 — a positive 2-cycle in M.
#
# WHAT THE VERDICTS MEAN, and the asymmetry that matters. `:violates` is a
# PROOF (an exact rational ξ, re-checked against the bare definition of a
# one-stage equilibrium by `escape_bare_violation`, which never touches K).
# `:no_witness` is a SCREEN, not a proof: supports of size ≥ 3 are searched in
# Float64 and the certain-quitter patterns with three mixers are not solved at
# all. Certifying `:no_witness` is what `scripts/simon_escape_class.jl` and
# `scripts/simon_escape_annulus.jl` do, and it costs half a minute per game
# instead of milliseconds. The screen is for throwing candidates away, and a
# game it throws away is one for which a witness could not be found cheaply.

"""
    escape_gap(g, j, ξ) -> K_j(ξ)

`K_j(ξ) = D_j(ξ, v) = A_j(ξ) − z_j(ξ)·v^j` with `v^j = r^{j}_j`: how much
player `j` prefers quitting to continuing when the others mix as in `ξ` and the
continuation vector is exactly `v`. Positive means `j`'s indifference
continuation lies strictly above `v^j`. Multilinear, no constant term,
independent of `ξ_j`.
"""
escape_gap(g::QuittingGame, j::Integer, ξ::AbstractVector) =
    deviation_gain(g, j, ξ, unilateral_diag(g))

"""
    escape_pair_matrix(g) -> M

`M[j,k] = r^{jk}_j − r^{k}_j` off the diagonal, `0` on it: the coefficient of
`ξ_k` in `K_j` restricted to a two-element support. A positive 2-cycle
(`M[j,k] > 0` and `M[k,j] > 0`) is an exact escape-criterion witness; it is
also the first-order part of `K_j` at `ξ = 0` on any support.
"""
function escape_pair_matrix(g::QuittingGame{T}) where {T}
    N = g.N
    M = zeros(T, N, N)
    for j in 1:N, k in 1:N
        j == k && continue
        M[j, k] = g.r[(1 << (j - 1)) | (1 << (k - 1)), j] - g.r[1 << (k - 1), j]
    end
    M
end

"""
    escape_pair_witness(g) -> Union{Nothing, Tuple{Int,Int}}

The lexicographically first positive 2-cycle `(j,k)` of `escape_pair_matrix`,
or `nothing`. Exact, `O(N²)`, and complete for two-element supports.
"""
function escape_pair_witness(g::QuittingGame)
    M = escape_pair_matrix(g)
    for j in 1:g.N, k in (j + 1):g.N
        M[j, k] > 0 && M[k, j] > 0 && return (j, k)
    end
    nothing
end

"""
    escape_admissible(g, ξ) -> (ok, x)

Decide the criterion at a single profile `ξ`: is there a continuation vector
`x` with `x_j > v^j` for every `j` making `ξ` an exact equilibrium of `Γ_x`?
Returns the prescribed `x` when there is (`x_j = A_j/z_j` for a participant,
comfortably large for a non-participant), `nothing` otherwise. Exact in the
number type of `ξ`.
"""
function escape_admissible(g::QuittingGame, ξ::AbstractVector{T}) where {T<:Real}
    N = g.N
    v = unilateral_diag(g)
    z = [prod(T[one(T) - ξ[k] for k in 1:N if k != j]; init = one(T)) for j in 1:N]
    K = [escape_gap(g, j, ξ) for j in 1:N]
    x = Vector{promote_type(T, eltype(g.r))}(undef, N)
    for j in 1:N
        if iszero(z[j])
            ξ[j] > 0 && K[j] < 0 && return (false, nothing)
            ξ[j] < 1 && K[j] > 0 && return (false, nothing)
            x[j] = v[j] + one(T)                 # x_j does not enter j's comparison
        elseif ξ[j] > 0
            K[j] > 0 || return (false, nothing)
            A = K[j] + z[j] * v[j]
            x[j] = A / z[j]                      # indifference; > v^j since K_j > 0
        else
            A = K[j] + z[j] * v[j]
            x[j] = max(A / z[j], v[j] + one(T))  # continuing must stay weakly best
        end
    end
    (true, x)
end

"""
    escape_bare_violation(g, ξ, x) -> value

How far `ξ` is from being an equilibrium of `Γ_x`, written straight from the
definition through `stage_value`, with no reference to `K_j`, `A_j` or `z_j`:
a player who quits with positive probability must not strictly prefer to
continue, and vice versa. Zero iff `ξ` is an exact equilibrium.

This is the SECOND ROUTINE of the two-routines rule (`planning/plan.md` §2):
every witness this file reports is confirmed here before it is believed.
"""
function escape_bare_violation(g::QuittingGame, ξ::AbstractVector{T}, x::AbstractVector) where {T}
    worst = zero(promote_type(T, eltype(x), eltype(g.r)))
    for j in 1:g.N
        xq = collect(ξ); xq[j] = one(T)
        xc = collect(ξ); xc[j] = zero(T)
        d = stage_value(g, xq, x)[j] - stage_value(g, xc, x)[j]     # quit − continue
        ξ[j] > 0 && d < 0 && (worst = max(worst, -d))
        ξ[j] < 1 && d > 0 && (worst = max(worst,  d))
    end
    worst
end

"""
    escape_confirm(g, ξ) -> (ok, x, violation)

Confirm a claimed witness `ξ` end to end and exactly: build the continuation
`x` the criterion prescribes, check `x_j > v^j` for every player, and verify
with `escape_bare_violation` that `ξ` really is an equilibrium of `Γ_x`.
"""
function escape_confirm(g::QuittingGame, ξ::AbstractVector{T}) where {T<:Real}
    gq = convert(QuittingGame{Rational{BigInt}}, g)
    ξq = Rational{BigInt}.(ξ)
    any(!iszero, ξq) || return (false, nothing, Rational{BigInt}(0))
    (ok, x) = escape_admissible(gq, ξq)
    ok || return (false, nothing, Rational{BigInt}(0))
    v = unilateral_diag(gq)
    all(x[j] > v[j] for j in 1:gq.N) || return (false, x, Rational{BigInt}(0))
    viol = escape_bare_violation(gq, ξq, x)
    (iszero(viol), x, viol)
end

# Local ascent of `f` on the open box `[lo, 1-lo]^J`, coordinates outside `J`
# held at zero. Deliberately its own routine and not `_coordinate_descent!`:
# that one lives on the closed cube, and both cube faces are exactly where this
# objective changes meaning (z_j = 0 on ξ_k = 1, smaller support on ξ_k = 0).
#
# `step` is halved only on a sweep with no MEANINGFUL gain, and `maxsweeps` is a
# hard backstop — exactly as in `_coordinate_descent!`, and for the same
# measured reason: a sweep that keeps creeping by ~1e-16 holds `step` at `step0`
# forever and the loop never terminates.
function _escape_ascent!(f, ξ::Vector{Float64}, J::Vector{Int}; lo = 1e-9,
                         step0 = 0.25, tol = 1e-12, minrel = 1e-12,
                         maxsweeps::Int = 2_000)
    best = f(ξ)
    step = step0
    sweeps = 0
    while step > tol && sweeps < maxsweeps
        sweeps += 1
        improved = false
        thresh = isfinite(best) ? minrel * max(1.0, abs(best)) : 0.0
        for j in J, s in (-step, step)
            old = ξ[j]
            ξ[j] = clamp(old + s, lo, 1 - lo)
            ξ[j] == old && continue
            val = f(ξ)
            if val > best + thresh
                best = val
                improved = true
            elseif val > best
                best = val            # better point, but not counted as progress
            else
                ξ[j] = old
            end
        end
        improved || (step /= 2)
    end
    best
end

"""
    escape_margin(g; starts = 64, rng) -> (value, ξ)

Float64 search for the best escape-criterion witness on supports WITHOUT a
certain quitter: the largest `min_{j ∈ J} K_j(ξ)` over every support `J` and
every `ξ` in the open cube. Positive ⇒ a witness exists (and `escape_witness`
will hand you an exact one); ≤ 0 ⇒ none was found on those supports.

Two-element supports are settled by the closed form `K_j = ξ_k·M[j,k]` and cost
nothing; only supports of size ≥ 3 are searched, and they are the only reason
this is a heuristic. Singletons are skipped because `K_j ≡ 0` there in every
quitting game.
"""
function escape_margin(g::QuittingGame{Float64}; starts::Int = 64,
                       rng::AbstractRNG = Random.Xoshiro(20260807))
    N = g.N
    best, bestξ = -Inf, zeros(N)
    M = escape_pair_matrix(g)
    for j in 1:N, k in (j + 1):N                     # closed form, exact in float
        m = min(M[j, k], M[k, j]) / 2                # attained at ξ_j = ξ_k = 1/2
        if m > best
            best = m
            bestξ = zeros(N); bestξ[j] = 0.5; bestξ[k] = 0.5
        end
    end
    ξ = zeros(N)
    for S in 1:((1 << N) - 1)
        J = [j for j in 1:N if (S >> (j - 1)) & 1 == 1]
        length(J) >= 3 || continue
        f = function (y)
            m = Inf
            for j in J
                m = min(m, escape_gap(g, j, y))
            end
            m
        end
        for s in 1:starts
            fill!(ξ, 0.0)
            for j in J
                # biased towards small ξ: the corner ξ → 0 is where the
                # first-order part decides, and it is where witnesses hide
                ξ[j] = rand(rng)^(s % 2 == 0 ? 3.0 : 1.0)
                ξ[j] = clamp(ξ[j], 1e-9, 1 - 1e-9)
            end
            val = _escape_ascent!(f, ξ, J)
            if val > best
                best, bestξ = val, copy(ξ)
            end
        end
    end
    (best, bestξ)
end

escape_margin(g::QuittingGame; kwargs...) =
    escape_margin(convert(QuittingGame{Float64}, g); kwargs...)

"""
    escape_witness(g; starts = 64, denom = 4096, rng) -> Union{Nothing, NamedTuple}

Search for an EXACT rational witness that `g` violates Simon's escape
criterion. Returns `(ξ, x, support, kind, margin)` — confirmed by
`escape_confirm`, i.e. re-checked against the bare definition — or `nothing`.

Three sources, cheapest first:

* `:pair` — a positive 2-cycle of `escape_pair_matrix`. Exact and complete for
  two-element supports; `ξ_j = ξ_k = 1/2`.
* `:mixed` — a Float64 search on supports of size ≥ 3, snapped to denominator
  `denom` and then verified exactly. The strict inequalities `K_j > 0` are an
  open condition, so a snapped rational either verifies or is discarded; no
  equation is ever solved.
* `:quitter` — patterns with at least one certain quitter and at most two
  strict mixers, solved exactly (with `≤ 2` mixers the system `K_j = 0` is
  triangular and rational). Patterns with three mixers are bilinear and are NOT
  searched here — the one place this routine is knowingly incomplete beyond the
  Float64 search.
"""
function escape_witness(g::QuittingGame; starts::Int = 64, denom::Integer = 4096,
                        rng::AbstractRNG = Random.Xoshiro(20260807))
    Qb = Rational{BigInt}
    gq = convert(QuittingGame{Qb}, g)
    gf = convert(QuittingGame{Float64}, g)
    N = g.N

    # (1) two-element supports: closed form, exact.
    pw = escape_pair_witness(gq)
    if pw !== nothing
        (j, k) = pw
        ξ = zeros(Qb, N); ξ[j] = Qb(1, 2); ξ[k] = Qb(1, 2)
        (ok, x, _) = escape_confirm(gq, ξ)
        ok && return (ξ = ξ, x = x, support = [j, k], kind = :pair,
                      margin = minimum(escape_gap(gq, i, ξ) for i in (j, k)))
    end

    # (2) supports of size ≥ 3, no certain quitter: search in float, verify exactly.
    (m, ξf) = escape_margin(gf; starts = starts, rng = rng)
    if m > 1e-9
        J = [j for j in 1:N if ξf[j] > 0]
        if length(J) >= 3
            ξ = zeros(Qb, N)
            for j in J
                ξ[j] = clamp(Qb(round(BigInt, ξf[j] * denom), denom), Qb(1, denom),
                             Qb(denom - 1, denom))
            end
            (ok, x, _) = escape_confirm(gq, ξ)
            ok && return (ξ = ξ, x = x, support = J, kind = :mixed,
                          margin = minimum(escape_gap(gq, j, ξ) for j in J))
        end
    end

    # (3) at least one certain quitter, at most two strict mixers: exact solve.
    for Pm in 1:((1 << N) - 1)
        P = [j for j in 1:N if (Pm >> (j - 1)) & 1 == 1]
        rest = [j for j in 1:N if !(j in P)]
        for Mm in 0:((1 << length(rest)) - 1)
            Mx = [rest[b] for b in 1:length(rest) if (Mm >> (b - 1)) & 1 == 1]
            length(Mx) <= 2 || continue
            ξ = zeros(Qb, N)
            for p in P
                ξ[p] = Qb(1)
            end
            if length(Mx) == 1
                # K_j does not depend on ξ_j and no other mixer moves: constant.
                j = Mx[1]
                ξ[j] = Qb(1, 2)
                iszero(escape_gap(gq, j, ξ)) || continue
            elseif length(Mx) == 2
                (j, k) = Mx
                sol = Qb[]
                bad = false
                for (u, w) in ((j, k), (k, j))     # K_u is affine in ξ_w
                    y0 = copy(ξ); y1 = copy(ξ); y1[w] = Qb(1)
                    a0 = escape_gap(gq, u, y0); a1 = escape_gap(gq, u, y1)
                    if a0 == a1 || !(0 < a0 / (a0 - a1) < 1)
                        bad = true; break
                    end
                    push!(sol, a0 / (a0 - a1))
                end
                bad && continue
                ξ[k] = sol[1]; ξ[j] = sol[2]
            end
            (ok, x, _) = escape_confirm(gq, ξ)
            ok && return (ξ = ξ, x = x, support = [j for j in 1:N if ξ[j] > 0],
                          kind = :quitter,
                          margin = minimum(escape_gap(gq, j, ξ)
                                           for j in 1:N if ξ[j] > 0))
        end
    end
    nothing
end

"""
    escape_screen(g; starts = 64, rng) -> NamedTuple

The P2 screen. `(status, witness, margin, note)` with

* `status = :violates` — an exact confirmed witness exists, so `g` is NOT known
  to be an escape game by Simon's criterion and stays a candidate. **Proved.**
* `status = :no_witness` — no witness found. `g` is presumed to be an escape
  game and is therefore presumed to have approximate equilibria, so it can be
  dropped. **Measured, not proved:** see the asymmetry note in the section
  header of this file.
"""
function escape_screen(g::QuittingGame; starts::Int = 64,
                       rng::AbstractRNG = Random.Xoshiro(20260807))
    w = escape_witness(g; starts = starts, rng = rng)
    if w === nothing
        (status = :no_witness, witness = nothing,
         margin = first(escape_margin(convert(QuittingGame{Float64}, g);
                                      starts = starts, rng = rng)),
         note = "no ξ ≠ 0 admits a continuation x with x_j > v^j making ξ an equilibrium of Γ_x (screen)")
    else
        (status = :violates, witness = w, margin = w.margin,
         note = "exact witness on support $(w.support) ($(w.kind)), confirmed against the bare definition")
    end
end

# ---------------------------------------------------------------------------
# The filter battery.
# ---------------------------------------------------------------------------

"""
    filter_report(g; qtrials = 200, escape = true, escape_starts = 64) -> NamedTuple

Run all existence-class filters. `viable == true` means no filter fired,
i.e. the game is *not yet excluded* as a counterexample candidate.
Each fired filter records the theorem that kills the candidate.

`escape` switches on F9, the Simon escape-class screen (P2 of
`planning/plan.md`). It is ON by default: the rule since 7 Aug 2026 is that no
candidate enters the expensive pipeline without it. Unlike F1–F8, F9 fires on
the ABSENCE of a witness, which is a screen and not a proof — pass
`escape = false` to reproduce a pre-P2 verdict, and read `report.escape` for
what the screen actually found.
"""
function filter_report(g::QuittingGame{T}; qtrials::Int = 200, escape::Bool = true,
                       escape_starts::Int = 64) where {T}
    reasons = String[]
    c, _ = ss_shifted(g)

    # F1: all-continue is an equilibrium (r_{i},i ≤ 0 for every i)
    all(ci -> ci <= 0, c) &&
        push!(reasons, "F1: all-continue is a stationary equilibrium (r_{i},i ≤ 0 ∀i)")

    # F2: Flesch/Solan–Vieille preference condition ⇒ cyclic subgame-perfect ε-eq
    flesch = true
    for i in 1:g.N, m in 1:(2^g.N - 1)
        if (m >> (i - 1)) & 1 == 1 && g.r[m, i] > g.r[1 << (i - 1), i]
            flesch = false
            break
        end
    end
    flesch && push!(reasons, "F2: r_{i},i ≥ r_S,i ∀S∋i ⇒ cyclic ε-equilibrium (SV01 Thm 1.2)")

    # F3: symmetric game ⇒ pure stationary 0-equilibrium (SV01 Thm 1.3).
    # Symmetric = payoff depends only on |S| and on whether i ∈ S. Reference
    # values from the coalition {1,…,k}: quitter payoff a_k = r_{1..k},1 and
    # (for k < N) non-quitter payoff b_k = r_{1..k},N.
    issym = true
    for m in 1:(2^g.N - 1), i in 1:g.N
        k = count_ones(m)
        expected = (m >> (i - 1)) & 1 == 1 ? g.r[(1 << k) - 1, 1] : g.r[(1 << k) - 1, g.N]
        if g.r[m, i] != expected
            issym = false
            break
        end
    end
    issym && push!(reasons, "F3: symmetric game ⇒ pure stationary 0-equilibrium (SV01 Thm 1.3)")

    # F4/F5/F6/F7: Solan–Solan battery on normal players
    np = normal_players(g)
    if isempty(np)
        push!(reasons, "F4: no normal players ⇒ stationary ε-equilibria (SS Lemma 2.6)")
    else
        _, rt = ss_shifted(g)
        for i in np
            if all(j -> rt[1 << (i - 1), j] >= 0, 1:g.N)
                push!(reasons, "F5: normal player $i has r̃^{$i} ≥ 0 ⇒ stationary ε-eq (SS Lemma 2.2)")
                break
            end
        end
        Rhat = unilateral_matrix(g, np)
        α = lcp0_nontrivial(Rhat)
        α !== nothing &&
            push!(reasons, "F6: LCP(R̂,0) nontrivial (support $(np[α])) ⇒ stationary ε-eq (SS Lemma 2.10)")
        w = q_matrix_witness(Rhat; trials = qtrials)
        w !== nothing &&
            push!(reasons, "F7: R̂ not a Q-matrix (witness q = $w) ⇒ stationary ε-eq (SS Thm 2.11(1))")
    end

    # F8: R(Γ) and all principal minors Q-matrices ⇒ continuous equilibrium
    # (AKRS Thm 5.2). CAVEAT: AKRS's LCP (their Def. 5.1) is the compactified
    # problem with a z₀ simplex weight; a matrix M is "Q" in their sense iff
    # LCP(M, 0) has a nontrivial solution (a q-independent z₀=0 solution) OR
    # M is a standard Q-matrix. We reject when EVERY principal minor
    # (including R itself) is AKRS-Q (Monte-Carlo in the standard-Q direction).
    R = unilateral_matrix(g)
    minor_witness = nothing
    for mask in 1:(2^g.N - 1)
        players = [i for i in 1:g.N if (mask >> (i - 1)) & 1 == 1]
        M = R[players, players]
        lcp0_nontrivial(M) === nothing || continue        # AKRS-Q via z₀ = 0
        w = q_matrix_witness(M; trials = length(players) == g.N ? qtrials : qtrials ÷ 4)
        if w !== nothing
            minor_witness = (players, w)                  # certified non-AKRS-Q
            break
        end
    end
    if minor_witness === nothing
        push!(reasons, "F8: R(Γ) and all principal minors appear to be Q-matrices (AKRS sense) ⇒ continuous equilibrium (AKRS Thm 5.2)")
    end

    # F9: the escape-class screen. Fires when NO witness against Simon's
    # criterion is found — then the game is presumed an escape game and has
    # approximate equilibria by Simon (2007) Thm 4. Screen, not proof.
    esc = escape ? escape_screen(g; starts = escape_starts) : nothing
    if esc !== nothing && esc.status === :no_witness
        push!(reasons, "F9: no escape-criterion witness found ⇒ presumed escape game ⇒ approximate equilibria (Simon 2007 Thm 4) [SCREEN, not a proof]")
    end

    (viable = isempty(reasons), reasons = reasons, normal = np,
     minor_witness = minor_witness, escape = esc)
end

"""
    degenerate_indifference_pairs(g) -> Vector{@NamedTuple{mask::Int, player::Int, value}}

Pairs `(S, i)` with `i ∈ S`, `S ∖ {i} ≠ ∅` and `r_S,i == r_{S∖{i}},i`.

WHY THIS IS WORTH SCREENING FOR. In a stage where the coalition `S ∖ {i}` quits
for sure, player `i` gets `r_S,i` by quitting along with them and `r_{S∖{i}},i`
by continuing. When those coincide his indifference equation degenerates to
`0 = 0`: his probability is a free variable, the periodic support-pattern
system is positive-dimensional, and msolve cannot conclude anything about it —
no matter how long it is given. What still bounds that probability are the
OTHER players' inequalities, and msolve does not see inequalities.

This is measured, not hypothetical. The four undecided period-3 patterns of
`gen015` all share the final stage "players 2, 3 and 4 quit for sure, player 1
mixes", and `gen015` has `r_{1234},1 = r_{234},1 = -2`. Counting over all `S`
reproduces the hand-made survey of Sun 2026-08-02 exactly — 6 of the
10 first-family candidates carry at least one pair, with `gen054` four,
`gen015` three, `gen041`/`gen027`/`gen010`/`gen048` one each, and `gen001`,
`gen004`, `gen009`, `gen025` none — so this list, not the full-coalition
sub-count, is the quantity that survey measured. Screen on it. The
full-coalition sub-count (`full_coalition_degeneracies`) is reported alongside
because that is the case observed to blow up, but it is a strictly smaller
number: `gen015` has 2 of its 3 pairs at the full coalition.

Likely cause: snapping payoffs to a coarse denominator manufactures exact
equalities that the Float64 search never had.

Exact comparison, so run it on a rational game: two Float64 payoffs that merely
print the same are not the same equation.
"""
function degenerate_indifference_pairs(g::QuittingGame{T}) where {T}
    out = @NamedTuple{mask::Int, player::Int, value::T}[]
    for m in 1:(2^g.N - 1), i in 1:g.N
        (m >> (i - 1)) & 1 == 1 || continue
        rest = m & ~(1 << (i - 1))
        rest == 0 && continue
        g.r[m, i] == g.r[rest, i] && push!(out, (mask = m, player = i, value = g.r[m, i]))
    end
    out
end

"""
    full_coalition_degeneracies(g) -> Int

How many players are indifferent in the stage where everybody else quits for
sure — the specific configuration observed to leave period-3 patterns
positive-dimensional (see `degenerate_indifference_pairs`). A sub-count of that
list, reported next to it; screen on the full list.
"""
full_coalition_degeneracies(g::QuittingGame) =
    count(p -> p.mask == 2^g.N - 1, degenerate_indifference_pairs(g))
