# The floors the limit lemma demands of the stationary rung (gap G1).
#
# `docs/G1_LIMIT_LEMMA.md` carries the certified stationary margin off the
# stratified domain `D(x_min, p_min)` onto all of `[0,1]^I`, but only if the
# two floors are small enough. Proposition 4 of that note fixes how small,
# in terms of the certified directional margin `δ_dir`, the certified
# stationary margin `δ`, the player count `n` and the payoff sup-norm `‖r‖`:
#
#     t_0    = δ_dir / (16‖r‖)                   (Corollary 2)
#     ρ      = δ / (12‖r‖)                       (Proposition 4)
#     p_min ≤ t_0 / n
#     x_min ≤ (ρ/(n−1))^{n−1} · t_0/n
#
# and then Theorem 5 gives `m(x) ≥ ε* = min(δ_dir, δ)/2` everywhere, provided
# also `max_i r^{i}_i ≥ ε*` (the value at `x = 0`).
#
# Everything here is exact rational arithmetic; nothing is rounded except by
# `snap`, and that only ever rounds a floor DOWN. Rounding a floor down
# enlarges the domain `D`, so a proof at the snapped floor implies the one the
# lemma asks for — the direction that keeps the statement sound.
#
# The circularity is real and is resolved by iteration, not by algebra: the
# floors depend on `δ`, and `δ` is what certifying at those floors produces.
# The procedure is to pick a target `δ`, compute the floors from it, and run
# `certify_stationary_margin_msolve` at exactly those floors for exactly that
# `δ`. A `:proved` outcome makes the pair `(δ, floors)` self-consistent and
# Theorem 5 applies. A `:failed` outcome means lowering the target, which
# lowers `ρ` and hence the floors again — so the retry is at a strictly harsher
# domain and has to be re-run, never inherited.

"""
    payoff_sup_norm(g) -> T

`‖r‖ = max_{S,i} |r^S_i|`, the constant the limit-lemma estimates are written
in. Exact in the number type of `g`.
"""
payoff_sup_norm(g::QuittingGame) = maximum(abs, g.r)

"""
    unilateral_diag(g) -> Vector{T}

`(r^{i}_i)_i`: what each player gets by quitting alone. Theorem 5 needs
`max_i r^{i}_i ≥ ε*`, since that maximum is the margin at `x = 0`.
"""
unilateral_diag(g::QuittingGame{T}) where {T} =
    T[g.r[1 << (i - 1), i] for i in 1:g.N]

# Largest power `base^{-k}` (k ≥ 0) that is still ≤ q. Exact; `q > 0` required.
function _snap_down(q::Rational{BigInt}, base::Integer)
    q > 0 || throw(ArgumentError("can only snap a positive floor, got $q"))
    base > 1 || throw(ArgumentError("snap base must exceed 1, got $base"))
    v = Rational{BigInt}(1)
    while v > q
        v //= base
    end
    v
end

_snap(q::Rational{BigInt}, mode::Symbol) =
    mode === :exact ? q :
    mode === :dec   ? _snap_down(q, 10) :
    mode === :pow2  ? _snap_down(q, 2) :
    throw(ArgumentError("unknown snap mode $mode (use :exact, :dec or :pow2)"))

"""
    limit_lemma_floors(g; delta_dir, delta, snap = :dec) -> NamedTuple

The floors `(p_min, x_min)` at which the stationary margin `δ` has to be
re-certified for the limit lemma of `docs/G1_LIMIT_LEMMA.md` to carry it onto
all of `[0,1]^I`, together with the resulting `ε*`.

`delta_dir` is the certified directional margin on the simplex
(`certify_directional_margin`), `delta` the *target* stationary margin on the
stratified domain. Both are taken as exact rationals; a `Float64` would silently
change the statement and is rejected by `Rational{BigInt}` conversion only for
values that are not exactly representable, so pass fractions.

`snap` controls the presentation of the two floors: `:exact` returns the sharp
bounds of Proposition 4, `:dec` the largest `10^{-k}` below them (what the note
quotes, and what reads sanely in a paper), `:pow2` the largest `2^{-k}`.
Snapping only ever goes down, i.e. towards a larger domain and a stronger
statement.

Returns `(; rnorm, n, t0, rho, pmin_bound, xmin_bound, pmin, xmin,
epsilon_star, maxdiag, ok_at_zero)`, where `pmin_bound`/`xmin_bound` are the
sharp Proposition 4 ceilings, `pmin`/`xmin` the snapped values to run with,
and `ok_at_zero` records the `x = 0` hypothesis of Theorem 5.
"""
function limit_lemma_floors(g::QuittingGame; delta_dir, delta, snap::Symbol = :dec)
    n = g.N
    n >= 2 || throw(ArgumentError("the limit lemma needs at least 2 players"))
    ge = convert(QuittingGame{Rational{BigInt}}, g)
    ddir = Rational{BigInt}(delta_dir)
    d = Rational{BigInt}(delta)
    (ddir > 0 && d > 0) ||
        throw(ArgumentError("both margins must be positive, got δ_dir = $ddir, δ = $d"))
    rnorm = payoff_sup_norm(ge)
    rnorm > 0 || throw(ArgumentError("degenerate game: ‖r‖ = 0"))

    t0 = ddir // (16 * rnorm)
    rho = d // (12 * rnorm)
    pmin_bound = t0 // n
    xmin_bound = (rho // (n - 1))^(n - 1) * pmin_bound

    eps = min(ddir, d) // 2
    maxdiag = maximum(unilateral_diag(ge))

    (rnorm = rnorm, n = n, t0 = t0, rho = rho,
     pmin_bound = pmin_bound, xmin_bound = xmin_bound,
     pmin = _snap(pmin_bound, snap), xmin = _snap(xmin_bound, snap),
     epsilon_star = eps, maxdiag = maxdiag, ok_at_zero = maxdiag >= eps)
end

"""
    limit_lemma_floors_admissible(g; delta_dir, delta, pmin, xmin) -> Bool

Whether a hand-chosen pair of floors satisfies the two inequalities of
Proposition 4 for the given margins — the check to run before believing that a
certificate produced at `(pmin, xmin)` feeds the limit lemma.
"""
function limit_lemma_floors_admissible(g::QuittingGame; delta_dir, delta,
                                       pmin, xmin)
    f = limit_lemma_floors(g; delta_dir = delta_dir, delta = delta,
                           snap = :exact)
    Rational{BigInt}(pmin) <= f.pmin_bound &&
        Rational{BigInt}(xmin) <= f.xmin_bound
end
