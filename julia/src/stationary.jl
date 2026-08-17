# Stationary profiles of the repeated quitting game.
#
# A stationary profile x has self-consistent value γ(x). Against stationary
# opponents x_{-i}, player i faces a one-state optimal stopping problem, so
# their best-response value is
#     BR_i(x_{-i}) = max(Qval_i, Cval_i)
# where Qval_i = expected payoff from quitting now, and Cval_i = expected
# payoff from continuing forever (= conditional absorption payoff caused by
# the others, or 0 if the others never quit). x is a stationary ε-equilibrium
# iff  BR_i − γ_i(x) ≤ ε  for every i. This repeated-game margin is the
# correct one: one-shot weighted deviation gains underestimate deviation power
# in low-absorption regimes (e.g. FTV at small symmetric x: one-shot gain
# O(x) but always-continue gains a constant).

"""
    selfconsistent_value(g, x) -> Vector

γ(x): expected undiscounted payoff of playing `x` forever. Zero when `x = 0`.
"""
function selfconsistent_value(g::QuittingGame, x::AbstractVector{T}) where {T<:Real}
    R = promote_type(T, eltype(g.r))
    p = quit_distribution(x)
    pabs = one(R) - p[1]
    iszero(pabs) && return zeros(R, g.N)
    v = zeros(R, g.N)
    for m in 1:(2^g.N - 1)
        iszero(p[m + 1]) && continue
        @views v .+= p[m + 1] .* g.r[m, :]
    end
    v ./ pabs
end

"""
    stationary_br_values(g, x) -> Vector

`BR_i(x_{-i})` for every player: the optimal-stopping value against the
stationary opponents' profile (ignores `x[i]`).
"""
function stationary_br_values(g::QuittingGame, x::AbstractVector{T}) where {T<:Real}
    R = promote_type(T, eltype(g.r))
    N = g.N
    br = Vector{R}(undef, N)
    for i in 1:N
        ibit = 1 << (i - 1)
        qval = zero(R)          # quit now
        sabs = zero(R)          # Σ_{T≠∅} P(T) r_T,i  (others' absorption terms)
        πi = zero(R)            # P(some other player quits)
        for m in 0:(2^N - 1)
            (m & ibit) == 0 || continue
            q = one(R)
            for j in 1:N
                j == i && continue
                q *= (m >> (j - 1)) & 1 == 1 ? x[j] : one(T) - x[j]
            end
            iszero(q) && continue
            qval += q * g.r[m + ibit, i]
            if m != 0
                sabs += q * g.r[m, i]
                πi += q
            end
        end
        cval = iszero(πi) ? zero(R) : sabs / πi
        br[i] = max(qval, cval)
    end
    br
end

"""
    stationary_violation(g, x)

`max_i (BR_i(x_{-i}) − γ_i(x))`: the largest repeated-game deviation gain
against the stationary profile `x` (always ≥ 0 up to the max with 0; exactly 0
iff `x` is a stationary 0-equilibrium; a stationary ε-equilibrium iff ≤ ε).
"""
function stationary_violation(g::QuittingGame, x::AbstractVector)
    γ = selfconsistent_value(g, x)
    br = stationary_br_values(g, x)
    worst = zero(eltype(γ))
    for i in 1:g.N
        worst = max(worst, br[i] - γ[i])
    end
    worst
end

is_stationary_equilibrium(g::QuittingGame, x; tol = 0) = stationary_violation(g, x) <= tol

"""
    min_stationary_violation_grid(g; resolution=20) -> (value, argmin)

Grid + local-refinement scan of `min_x stationary_violation`. Search evidence
only — exact emptiness proofs are produced by `certify_min_stationary_violation`.
"""
function min_stationary_violation_grid(g::QuittingGame{T}; resolution::Int = 20,
                                       refine_steps::Int = 60) where {T}
    N = g.N
    best = convert(float(T), Inf)
    bestx = zeros(float(T), N)
    grid = range(0.0, 1.0; length = resolution)
    x = zeros(float(T), N)
    idx = ones(Int, N)
    total = resolution^N
    for k in 0:(total - 1)
        t = k
        for i in 1:N
            idx[i] = t % resolution + 1
            t ÷= resolution
        end
        for i in 1:N
            x[i] = grid[idx[i]]
        end
        v = stationary_violation(g, x)
        if v < best
            best = v
            bestx .= x
        end
    end
    step = 1.0 / resolution
    for _ in 1:refine_steps
        improved = false
        for i in 1:g.N, s in (-step, step)
            xi = clamp(bestx[i] + s, 0.0, 1.0)
            xi == bestx[i] && continue
            old = bestx[i]
            bestx[i] = xi
            v = stationary_violation(g, bestx)
            if v < best
                best = v
                improved = true
            else
                bestx[i] = old
            end
        end
        improved || (step /= 2)
        step < 1e-12 && break
    end
    best, bestx
end
