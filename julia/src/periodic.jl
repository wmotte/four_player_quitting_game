# Periodic (cyclic) profiles: the profile repeats a block x^1, …, x^k forever.
#
# Continuation values satisfy the cyclic recursion
#   y^t = A^t + q^t · y^{t+1},   t = 1..k  (indices mod k),
# where A^t_i = Σ_{S≠∅} P_{x^t}(S) r_S,i and q^t = P_{x^t}(∅).
# If Π_t q^t = 1 (nobody ever quits) the profile is non-absorbing and y = 0.
#
# The block is a (subgame-perfect) equilibrium iff for every stage t, x^t is a
# Nash equilibrium of the stage game G(y^{t+1}) — the continuation value
# relevant at stage t is the value from stage t+1 onward.

"""
    periodic_values(g, xs) -> Vector{Vector}

Continuation values `y^1, …, y^k` for the periodic profile given by the block
`xs = [x¹, …, xᵏ]` of quit-probability vectors. Exact for rational inputs.
"""
function periodic_values(g::QuittingGame, xs::AbstractVector{<:AbstractVector{T}}) where {T<:Real}
    k = length(xs)
    R = promote_type(T, eltype(g.r))
    A = Vector{Vector{R}}(undef, k)
    q = Vector{R}(undef, k)
    for t in 1:k
        p = quit_distribution(xs[t])
        q[t] = p[1]
        a = zeros(R, g.N)
        for m in 1:(2^g.N - 1)
            iszero(p[m + 1]) && continue
            @views a .+= p[m + 1] .* g.r[m, :]
        end
        A[t] = a
    end
    Q = prod(q)
    ys = Vector{Vector{R}}(undef, k)
    if isone(Q)                       # non-absorbing cycle ⇒ payoff 0 everywhere
        for t in 1:k
            ys[t] = zeros(R, g.N)
        end
        return ys
    end
    # y^1 = A^1 + q^1 A^2 + q^1 q^2 A^3 + … + (Π q) y^1
    b = zeros(R, g.N)
    c = one(R)
    for t in 1:k
        b .+= c .* A[t]
        c *= q[t]
    end
    y1 = b ./ (one(R) - Q)
    ys[1] = y1
    for t in k:-1:2                   # y^t = A^t + q^t y^{t+1}, y^{k+1} = y^1
        nxt = t == k ? y1 : ys[t + 1]
        ys[t] = A[t] .+ q[t] .* nxt
    end
    ys
end

"""
    periodic_violation(g, xs)

Largest one-shot deviation gain at any stage of the periodic block `xs`
(stage-Nash violation of `x^t` in `G(y^{t+1})`). Zero iff the block is a
subgame-perfect equilibrium among one-shot deviations.
"""
function periodic_violation(g::QuittingGame, xs::AbstractVector{<:AbstractVector})
    k = length(xs)
    ys = periodic_values(g, xs)
    worst = stage_nash_violation(g, xs[k], ys[1])   # stage k looks at y^1
    for t in 1:(k - 1)
        worst = max(worst, stage_nash_violation(g, xs[t], ys[t + 1]))
    end
    worst
end

is_periodic_equilibrium(g::QuittingGame, xs; tol = 0) = periodic_violation(g, xs) <= tol

"""
    periodic_margin(g, xs)

Repeated-game margin of the periodic profile: `max_{i,t} (BR_i^t − y^t_i)`,
where `BR_i^t` is player i's optimal-stopping value against the cyclic
opponents' profile starting at stage `t`. Computed exactly by enumerating all
2^k quit-time policies over the k-state cycle (optimal policies are cyclic).
Zero iff the block is an exact subgame-perfect 0-equilibrium; the profile is
a (cyclic) ε-equilibrium iff the margin is ≤ ε.
"""
function periodic_margin(g::QuittingGame, xs::AbstractVector{<:AbstractVector{T}}) where {T<:Real}
    k = length(xs)
    R = promote_type(T, eltype(g.r))
    N = g.N
    ys = periodic_values(g, xs)
    worst = zero(R)
    for i in 1:N
        ibit = 1 << (i - 1)
        qval = Vector{R}(undef, k)   # quit-now value at stage t
        sabs = Vector{R}(undef, k)   # Σ_{T≠∅} Q_T r_T,i (others absorb)
        surv = Vector{R}(undef, k)   # Π_{j≠i}(1 − x_j^t)
        for t in 1:k
            q0, s0, sv = zero(R), zero(R), zero(R)
            for m in 0:(2^N - 1)
                (m & ibit) == 0 || continue
                q = one(R)
                for j in 1:N
                    j == i && continue
                    q *= (m >> (j - 1)) & 1 == 1 ? xs[t][j] : one(T) - xs[t][j]
                end
                iszero(q) && continue
                q0 += q * g.r[m + ibit, i]
                if m == 0
                    sv = q
                else
                    s0 += q * g.r[m, i]
                end
            end
            qval[t], sabs[t], surv[t] = q0, s0, sv
        end
        # policy σ = set of stages where i quits; exact value per start stage
        best = Vector{Union{Nothing,R}}(nothing, k)
        for σmask in 0:(2^k - 1)
            vals = Vector{R}(undef, k)
            if σmask == 0
                Q = prod(surv)
                if Q >= 1                       # others never quit ⇒ payoff 0
                    fill!(vals, zero(R))
                else
                    # V_t = sabs_t + surv_t V_{t+1}, cyclic
                    b = zero(R); c = one(R)
                    for l in 0:(k - 1)
                        t = mod1(1 + l, k)
                        b += c * sabs[t]
                        c *= surv[t]
                    end
                    V1 = b / (one(R) - Q)
                    vals[1] = V1
                    for t in k:-1:2
                        nxt = t == k ? V1 : vals[t + 1]
                        vals[t] = sabs[t] + surv[t] * nxt
                    end
                end
            else
                for t0 in 1:k
                    acc = zero(R); c = one(R); v = zero(R)
                    for l in 0:(k - 1)
                        t = mod1(t0 + l, k)
                        if (σmask >> (t - 1)) & 1 == 1
                            v = acc + c * qval[t]
                            break
                        end
                        acc += c * sabs[t]
                        c *= surv[t]
                    end
                    vals[t0] = v
                end
            end
            for t in 1:k
                if best[t] === nothing || vals[t] > best[t]
                    best[t] = vals[t]
                end
            end
        end
        for t in 1:k
            worst = max(worst, best[t] - ys[t][i])
        end
    end
    worst
end
