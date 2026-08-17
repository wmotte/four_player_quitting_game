# Ground-truth games from the literature. These calibrate the pipeline:
# known equilibria must be found/verified, and known-existence classes must
# never be flagged as counterexample candidates.

"""
    ftv1997() -> QuittingGame{Rational{BigInt}}

The Flesch–Thuijsman–Vrieze (1997, IJGT 26, 303–314) three-player quitting
game (cyclically symmetric):

    r_{1} = (1,3,0)   r_{1,2} = (1,0,1)
    r_{2} = (0,1,3)   r_{1,3} = (0,1,1)   r_{1,2,3} = (0,0,0)
    r_{3} = (3,0,1)   r_{2,3} = (1,1,0)

(The pair payoffs form one cyclic orbit under the shift 1→2→3→1, consistent
with the game's cyclic symmetry.)

Known facts: **no stationary ε-equilibrium** for small ε (the original FTV
result); the cyclic profile in which players take turns quitting with
probability 1/2 (period 3) is an exact subgame-perfect equilibrium with
continuation values cycling through (1,2,1) → (1,1,2) → (2,1,1).

NOTE on normalization: AKRS (arXiv:2012.04369) Example 5.4 uses unilateral
payoffs shifted by −1 per player (`(0,2,-1)` etc.). That shift is *not*
neutral for the full game: it keeps the never-quit payoff at 0, so in the
shifted game all-continue becomes an exact stationary equilibrium (solo
quitting also yields 0). The shift is harmless only for continuous-equilibrium
analysis. We use the original payoffs.
"""
function ftv1997()
    Q = Rational{BigInt}
    QuittingGame(3,
        [1] => Q[1, 3, 0],
        [2] => Q[0, 1, 3],
        [3] => Q[3, 0, 1],
        [1, 2] => Q[1, 0, 1],
        [1, 3] => Q[0, 1, 1],
        [2, 3] => Q[1, 1, 0],
        [1, 2, 3] => Q[0, 0, 0])
end

"The exact period-3 cyclic equilibrium block of `ftv1997()` (quit-probabilities)."
ftv1997_cycle() = [Rational{BigInt}[1//2, 0, 0],
                   Rational{BigInt}[0, 1//2, 0],
                   Rational{BigInt}[0, 0, 1//2]]

"""
    solan_vieille_4p() -> QuittingGame{Rational{BigInt}}

The four-player quitting game of Solan & Vieille (2001, MOR 26(2), §3,
Figure 2). Exact payoffs for every quitting coalition:

| S       | payoff        | S         | payoff        |
|---------|---------------|-----------|---------------|
| {1}     | (1,4,0,0)     | {1,2,3}   | (1,0,0,0)     |
| {2}     | (4,1,0,0)     | {1,2,4}   | (0,1,0,0)     |
| {3}     | (0,0,1,4)     | {1,3,4}   | (0,0,0,1)     |
| {4}     | (0,0,4,1)     | {2,3,4}   | (0,0,1,0)     |
| {1,2}   | (1,1,1,1)     | {1,2,3,4} | (-1,-1,-1,-1) |
| {3,4}   | (1,1,1,1)     |           |               |
| {1,3}   | (1,1,1,0)     | {1,4}     | (1,0,1,1)     |
| {2,3}   | (0,1,1,1)     | {2,4}     | (1,1,0,1)     |

Known facts (loc. cit.): satisfies A.1–A.2; admits **no stationary
ε-equilibrium** and no ε-equilibrium that stays ε-close to all-continue; the
"simplest" equilibrium is periodic with period 2: at odd stages players 1 and
3 quit with probabilities `1-x`, `1-z`, at even stages players 2 and 4 do,
where `x = 1/h`, `z = 1/g`, `g = 3/(4-h²)`.

NOTE: the published paper states that `h ∈ (1,2)` is a root of
`X⁴ + 3X³ - 2X² - 9X + 4` (their Eq. (30)); re-deriving their indifference
system from the payoff table yields instead

    z·γ¹_c = 1,  x·γ³_c = 1,
    γ¹_c = xz + 4z(1-x) + (1-x)(1-z),   γ³_c = xz + 4x(1-z),

which gives `g = 3/(4-h²)` (as in the paper) but `h` a root of
`3X⁴ + X³ - 26X² - 7X + 44` with `h ≈ 1.34031` in (1,2). Direct verification
against the raw payoff table confirms the corrected root: `periodic_violation`
is ≈ 1e-78 at 256-bit precision for the corrected `h`, but ≈ 0.11 for the
paper's printed root (h ≈ 1.43036). The paper's argument (a root in (1,2)
exists) is unaffected.

The typo is localised to a single term on p. 284 (checked against the printed
text, 2026-07-31). The paper prints `γ³_c = xz + 4z(1-x)`, which substituting
`x = 1/h`, `z = 1/g` gives `gh² = 1 + 4(h-1)` — but the equation it then prints
is `gh² = 1 + 4(g-1)`, which corresponds to `γ³_c = xz + 4x(1-z)`. Matrix (29)
on p. 283 settles it in favour of the latter: the payoff 4 to player 4 sits
where player 3 quits alone (probability `x(1-z)`), whereas the payoff 4 to
player 2 sits where player 1 quits alone (probability `(1-x)z`), so `γ¹_c` is
correct as printed and `γ³_c` is not. Consequently the first equation of the
`(g,h)` system should read `g²h = 1 + 4(h-1) + (g-1)(h-1)`. Eliminating `g`
from the system *as printed* reproduces the printed quartic exactly, which pins
the error upstream of Eq. (30); see `manuscripts/erratum/` for the correspondence and a
stand-alone verification.
"""
function solan_vieille_4p()
    Q = Rational{BigInt}
    QuittingGame(4,
        [1] => Q[1, 4, 0, 0],
        [2] => Q[4, 1, 0, 0],
        [3] => Q[0, 0, 1, 4],
        [4] => Q[0, 0, 4, 1],
        [1, 2] => Q[1, 1, 1, 1],
        [1, 3] => Q[1, 1, 1, 0],
        [1, 4] => Q[1, 0, 1, 1],
        [2, 3] => Q[0, 1, 1, 1],
        [2, 4] => Q[1, 1, 0, 1],
        [3, 4] => Q[1, 1, 1, 1],
        [1, 2, 3] => Q[1, 0, 0, 0],
        [1, 2, 4] => Q[0, 1, 0, 0],
        [1, 3, 4] => Q[0, 0, 0, 1],
        [2, 3, 4] => Q[0, 0, 1, 0],
        [1, 2, 3, 4] => Q[-1, -1, -1, -1])
end

"""
    solan_vieille_4p_cycle(; bits = 256) -> Vector{Vector{BigFloat}}

The period-2 equilibrium block of `solan_vieille_4p()` at `bits` precision:
odd-stage and even-stage quit-probability vectors. Root `h ≈ 1.34031` of the
corrected quartic `3X⁴+X³-26X²-7X+44` in (1,2) is computed by bisection (see
the `solan_vieille_4p` docstring for why this differs from the published Eq. (30)).
"""
function solan_vieille_4p_cycle(; bits::Int = 256)
    old = precision(BigFloat)
    try
        setprecision(BigFloat, bits)
        f(h) = 3h^4 + h^3 - 26h^2 - 7h + 44
        lo, hi = BigFloat(1), BigFloat(2)
        if f(lo) > 0                      # f is decreasing on (1,2) here
            lo, hi = hi, lo
        end
        @assert f(lo) < 0 && f(hi) > 0
        for _ in 1:(bits + 10)
            mid = (lo + hi) / 2
            if f(mid) < 0
                lo = mid
            else
                hi = mid
            end
        end
        h = (lo + hi) / 2
        g = 3 / (4 - h^2)
        x = 1 / h              # continue-probability of players 1,3 at odd stages
        z = 1 / g              # continue-probability of players 2,4 at odd stages... see below
        # Solan–Vieille profile (their x = continue-probs): odd stages (x,1,z,1),
        # even stages (1,x,1,z). Our convention is quit-probabilities:
        odd = BigFloat[1 - x, 0, 1 - z, 0]
        even = BigFloat[0, 1 - x, 0, 1 - z]
        return [odd, even]
    finally
        setprecision(BigFloat, old)
    end
end

"""
    symmetric_game(N, a, b) -> QuittingGame

Symmetric quitting game: quitters in a coalition of size `k` get `a[k]`,
non-quitters get `b[k]` (`b[N]` unused). Always has a pure stationary
0-equilibrium (Solan–Vieille 2001, Thm 1.3) — an existence-class test case.
"""
function symmetric_game(N::Int, a::AbstractVector, b::AbstractVector)
    length(a) == N && length(b) >= N - 1 ||
        throw(ArgumentError("need a[1..N] and b[1..N-1]"))
    T = promote_type(eltype(a), eltype(b))
    r = Matrix{T}(undef, 2^N - 1, N)
    for m in 1:(2^N - 1)
        k = count_ones(m)
        for i in 1:N
            r[m, i] = (m >> (i - 1)) & 1 == 1 ? a[k] : b[k]
        end
    end
    QuittingGame{T}(N, r)
end

"""
    unanimity_game(N) -> QuittingGame

Trivial game where quitting alone pays -1 and everyone-quits pays 1:
all-continue is a stationary equilibrium (r_{i},i ≤ 0), and all-quit as well.
Existence-class test case.
"""
function unanimity_game(N::Int)
    Q = Rational{BigInt}
    r = Matrix{Q}(undef, 2^N - 1, N)
    for m in 1:(2^N - 1)
        for i in 1:N
            if (m >> (i - 1)) & 1 == 1
                r[m, i] = m == 2^N - 1 ? 1 : -1
            else
                r[m, i] = 0
            end
        end
    end
    QuittingGame{Q}(N, r)
end
