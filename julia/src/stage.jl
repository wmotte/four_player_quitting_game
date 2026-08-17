# One-shot (stage) game G(y): the quitting game truncated to a single stage,
# with continuation payoff vector y if everyone continues.

"""
    quit_distribution(x) -> Vector

Probability `P(S quits exactly)` for every coalition bitmask `0:(2^N-1)`
(index `mask + 1`), given quit-probabilities `x`.
"""
function quit_distribution(x::AbstractVector{T}) where {T<:Real}
    N = length(x)
    p = zeros(T, 2^N)
    p[1] = one(T)
    for i in 1:N
        bit = 1 << (i - 1)
        for m in (2^i - 1):-1:0            # masks over players 1..i, descending
            base = p[m + 1]
            iszero(base) && continue
            if (m & bit) == 0
                p[m + bit + 1] += base * x[i]
                p[m + 1] = base * (one(T) - x[i])
            end
        end
    end
    p
end

"Probability that at least one player quits under `x`."
absorption_prob(x::AbstractVector) = 1 - prod(1 .- x)

"""
    stage_value(g, x, y) -> Vector

Expected payoff vector of the one-shot game `G(y)` under quit-profile `x`:
`Σ_{S≠∅} P(S) r_S + P(∅) y`.
"""
function stage_value(g::QuittingGame{T}, x::AbstractVector, y::AbstractVector) where {T}
    p = quit_distribution(x)
    v = p[1] .* collect(y)
    for m in 1:(2^g.N - 1)
        iszero(p[m + 1]) && continue
        @views v .+= p[m + 1] .* g.r[m, :]
    end
    v
end

"""
    deviation_gain(g, i, x, y)

`D_i(x_{-i}; y)`: player `i`'s expected payoff from quitting minus continuing,
holding the other players' quit-probabilities fixed. Positive ⇒ quitting is
strictly better. Multilinear in `x_{-i}`; `x[i]` itself is ignored.
"""
function deviation_gain(g::QuittingGame, i::Integer, x::AbstractVector{T}, y::AbstractVector) where {T<:Real}
    N = g.N
    ibit = 1 << (i - 1)
    D = zero(promote_type(T, eltype(y), eltype(g.r)))
    # enumerate coalitions T of the OTHER players (masks without bit i)
    for m in 0:(2^N - 1)
        (m & ibit) == 0 || continue
        q = one(T)
        for j in 1:N
            j == i && continue
            q *= (m >> (j - 1)) & 1 == 1 ? x[j] : one(T) - x[j]
        end
        iszero(q) && continue
        quitpay = g.r[m + ibit, i]
        contpay = m == 0 ? y[i] : g.r[m, i]
        D += q * (quitpay - contpay)
    end
    D
end

"""
    stage_nash_violation(g, x, y) -> value

How far `x` is from being a Nash equilibrium of the stage game `G(y)`:
the largest one-shot deviation gain available to any player. Zero (≤ tol)
iff `x` is a stage Nash equilibrium. Specifically, per player:
`max(x_i > 0 ? -D_i : 0, x_i < 1 ? D_i : 0)` — quitting with positive
probability requires `D_i ≥ 0`, continuing with positive probability requires
`D_i ≤ 0`; violations are weighted by the probability mass on the suboptimal
action so that the value equals the actual payoff gain from switching.
"""
function stage_nash_violation(g::QuittingGame, x::AbstractVector{T}, y::AbstractVector) where {T<:Real}
    worst = zero(promote_type(T, eltype(y), eltype(g.r)))
    for i in 1:g.N
        D = deviation_gain(g, i, x, y)
        if D > 0            # would gain by quitting outright
            worst = max(worst, (one(T) - x[i]) * D)
        elseif D < 0        # would gain by continuing outright
            worst = max(worst, x[i] * (-D))
        end
    end
    worst
end

is_stage_nash(g::QuittingGame, x, y; tol = 0) = stage_nash_violation(g, x, y) <= tol
