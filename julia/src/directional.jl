# Directional (limit-stationary) analysis.
#
# If a uniform ε-equilibrium family exists in which quit-probabilities vanish
# with limit direction d ∈ Δ^{N-1} (d_j = relative quitting rate of player j),
# then the continuation values converge to
#   y*(d)_i = Σ_j d_j r_{{j}},i / Σ_j d_j
# (only unilateral quits survive in the limit; simultaneous quits are second
# order). Consistency of the approach direction requires each player quitting
# at positive rate to be exactly indifferent at the limit, and each player
# quitting at zero rate to weakly prefer continuing:
#   d_j > 0 ⇒ r_{{j}},j = y*(d)_j        (indifference)
#   d_j = 0 ⇒ r_{{j}},j ≤ y*(d)_j        (continue optimal)
# These are necessary conditions for a "slow stationary" approach path; see
# docs/VERIFICATION_TARGET.md for their precise status in the literature.

"""
    limit_value(g, d) -> Vector

`y*(d)`: limit continuation value for approach direction `d` (need not be
normalized; must be ≥ 0, not all zero).
"""
function limit_value(g::QuittingGame, d::AbstractVector{T}) where {T<:Real}
    R = promote_type(T, eltype(g.r))
    s = sum(d)
    iszero(s) && throw(ArgumentError("direction must be non-zero"))
    v = zeros(R, g.N)
    for j in 1:g.N
        iszero(d[j]) && continue
        m = 1 << (j - 1)
        @views v .+= d[j] .* g.r[m, :]
    end
    v ./ s
end

"""
    directional_violation(g, d)

How badly direction `d` fails the limit-consistency conditions:
`max_j` of `|r_{{j}},j − y*(d)_j|` over `d_j > 0` and of
`max(0, r_{{j}},j − y*(d)_j)` over `d_j = 0`. A direction with value 0 is a
candidate stationary-approach direction; a game where the *minimum over all
d ∈ Δ* is strictly positive admits no vanishing-stationary approach path.

!!! warning "Detector, not a margin"
    Its zero set is right, its value is not. On the support this uses
    `|r_{{j}},j − y*(d)_j|`, whereas the deviation gain the game actually
    offers along `d` is smaller by the factor `1 − d_j`. Its minimum over the
    simplex therefore over-states the margin (0.2857 against 0.1099 on gen025,
    0.4420 against 0.1124 on gen015) and must never be quoted as one. The
    quantity to quote is `directional_margin` in `directional_margin.jl`; see
    `docs/G1_LIMIT_LEMMA.md` §2. This function is kept as the search-time
    detector, and the sieve's fitness still uses it deliberately, so that the
    candidate ranking stays reproducible.
"""
function directional_violation(g::QuittingGame, d::AbstractVector{T}) where {T<:Real}
    y = limit_value(g, d)
    R = eltype(y)
    worst = zero(R)
    for j in 1:g.N
        rj = g.r[1 << (j - 1), j]
        if d[j] > 0
            worst = max(worst, abs(rj - y[j]))
        else
            worst = max(worst, max(zero(R), rj - y[j]))
        end
    end
    worst
end

"""
    min_directional_violation_grid(g; resolution=60) -> (value, argmin)

Scan of `min_{d∈Δ} directional_violation` over a simplex grid with local
refinement. Search evidence only; exact emptiness is Phase-2 work (QE over the
simplex, ≤ N-1 free variables).
"""
function min_directional_violation_grid(g::QuittingGame; resolution::Int = 60,
                                        refine_steps::Int = 200)
    N = g.N
    best = Inf
    bestd = zeros(N)
    # enumerate compositions of `resolution` into N parts (grid on the simplex)
    d = zeros(N)
    stack = [(zeros(Int, 0), resolution)]
    while !isempty(stack)
        (prefix, rem) = pop!(stack)
        if length(prefix) == N - 1
            comp = vcat(prefix, rem)
            for i in 1:N
                d[i] = comp[i] / resolution
            end
            v = directional_violation(g, d)
            if v < best
                best = v
                bestd .= d
            end
        else
            for a in 0:rem
                push!(stack, (vcat(prefix, a), rem - a))
            end
        end
    end
    # local refinement: move mass between coordinate pairs
    step = 1.0 / resolution
    for _ in 1:refine_steps
        improved = false
        for i in 1:N, j in 1:N
            i == j && continue
            bestd[i] < step && continue
            cand = copy(bestd)
            cand[i] -= step
            cand[j] += step
            v = directional_violation(g, cand)
            if v < best
                best = v
                bestd .= cand
                improved = true
            end
        end
        improved || (step /= 2)
        step < 1e-12 && break
    end
    best, bestd
end
