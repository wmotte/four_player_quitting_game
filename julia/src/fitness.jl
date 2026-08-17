# Phase-1 fitness: how far a game is from admitting the "simple" equilibrium
# forms (S.1)-style objects. All margins are computed in Float64; they are
# SEARCH HEURISTICS ONLY — exact certification is Phase-2 work.
#
# fitness = min(m1, m2, m3, m4):
#   m1  min stationary violation over profiles with absorption ≥ pmin
#   m2  min directional (vanishing-approach) violation over Δ^{N-1}
#   m3  min periodic violation over blocks of period 2..K
#   m4  min stationary violation over the LOW-ABSORPTION band (absorption
#       down to the certificate floor 1/100 — the corner m1 never samples)
# A game with a large fitness has no obvious stationary / vanishing /
# short-cyclic equilibrium — precisely the raw material for Phase 2.

"""
    min_stationary_violation(g; pmin = 0.05, starts = 200, rng) -> (value, x)

Multistart local minimization of `stationary_violation` over profiles with
`absorption_prob(x) ≥ pmin` (the vanishing-absorption regime is m2's job).
"""
function min_stationary_violation(g::QuittingGame{Float64}; pmin::Float64 = 0.05,
                                  starts::Int = 200,
                                  rng::AbstractRNG = Random.Xoshiro(1))
    N = g.N
    penal(x) = absorption_prob(x) < pmin ? Inf : stationary_violation(g, x)
    best, bestx = Inf, fill(0.5, N)

    # Deterministic seeds FIRST. Stationary equilibria of quitting games
    # typically sit on pure profiles x ∈ {0,1}^N, and random interior starts
    # find those corners only unreliably — Phase-1 campaigns reported margins
    # of 0.16-0.24 for games that in fact have an exact equilibrium at a corner.
    # The 2^N corners are cheap, so always check them (both as raw points and
    # as descent starts).
    for m in 0:(2^N - 1)
        x = Float64[(m >> (i - 1)) & 1 for i in 1:N]
        v = penal(x)
        if v < best
            best, bestx = v, copy(x)
        end
        v = _coordinate_descent!(penal, x)
        if v < best
            best, bestx = v, copy(x)
        end
    end

    for s in 1:starts
        x = s == 1 ? fill(0.5, N) : rand(rng, N)
        absorption_prob(x) < pmin && (x .= clamp.(x .+ 0.5, 0.0, 1.0))
        v = _coordinate_descent!(penal, x)
        if v < best
            best, bestx = v, copy(x)
        end
    end
    best, bestx
end

"""
    min_corner_violation(g; pmin = 0.01, pband = 0.06, starts = 150, rng)
        -> (value, x)

Multistart local minimization of `stationary_violation` over the LOW-ABSORPTION
part of the certificate domain: `absorption_prob(x) ≥ pmin` with `pmin`
matching the V1/margin certificates (1/100), NOT m1's 0.05. The δ = 1/6 and
1/5 margin failures on gen025 showed the true stratified-domain minimum hides
exactly in the band m1 never samples — near-minimizers at x3, x4 ≈ xmin with
absorption at its floor. Starts are biased there: random profiles rescaled so
absorption lands in [pmin, pband], plus variants with a random subset of
players pinned near 0.
"""
function min_corner_violation(g::QuittingGame{Float64}; pmin::Float64 = 0.01,
                              pband::Float64 = 0.06, starts::Int = 150,
                              rng::AbstractRNG = Random.Xoshiro(3))
    N = g.N
    penal(x) = absorption_prob(x) < pmin ? Inf : stationary_violation(g, x)
    # rescale x towards 0 until absorption sits inside [pmin, pband]
    function toband!(x)
        absorption_prob(x) <= pband && return x
        lo, hi = 0.0, 1.0
        for _ in 1:40
            t = (lo + hi) / 2
            absorption_prob(t .* x) > pband ? (hi = t) : (lo = t)
        end
        x .*= (lo + hi) / 2
        x
    end
    best, bestx = Inf, fill(0.0, N)
    for s in 1:starts
        x = rand(rng, N)
        if s % 3 == 0        # pin a random nonempty proper subset near zero
            for i in randperm(rng, N)[1:rand(rng, 1:(N - 1))]
                x[i] = 1e-3 * rand(rng)
            end
        end
        toband!(x)
        absorption_prob(x) < pmin && continue
        v = _coordinate_descent!(penal, x)
        if v < best
            best, bestx = v, copy(x)
        end
    end
    best, bestx
end

"""
    min_periodic_violation(g, k; starts = 100, rng) -> (value, xs)

Multistart local minimization of `periodic_violation` over period-`k` blocks.
Only absorbing blocks are considered (a non-absorbing block is the all-continue
case, handled by filters/m2).
"""
function min_periodic_violation(g::QuittingGame{Float64}, k::Int;
                                starts::Int = 100,
                                rng::AbstractRNG = Random.Xoshiro(2))
    N = g.N
    function obj(flat::Vector{Float64})
        xs = [flat[(t-1)*N+1:t*N] for t in 1:k]
        periodic_margin(g, xs)
    end
    best, bestflat = Inf, Float64[]
    for _ in 1:starts
        flat = rand(rng, N * k)
        v = _coordinate_descent!(obj, flat)
        if v < best
            best, bestflat = v, copy(flat)
        end
    end
    best, [bestflat[(t-1)*N+1:t*N] for t in 1:k]
end

"""
Simple projected coordinate descent on [0,1]^n with shrinking steps.

`step` is only halved when a full sweep makes no *meaningful* progress. A
decrease smaller than `minrel` (relative to the current value) is accepted as a
better point but does NOT count as progress: otherwise a sweep that keeps
creeping by ~1e-16 holds `step` at `step0` forever and the loop never
terminates. This is not hypothetical — the BR-based margin is discontinuous on
the faces `x_j = 0`, and FTV'97 (which has no stationary equilibrium) drives the
descent along such a face indefinitely. `maxsweeps` is a hard backstop.
"""
function _coordinate_descent!(f, x::Vector{Float64}; step0 = 0.25, tol = 1e-10,
                              minrel = 1e-12, maxsweeps::Int = 5_000)
    fx = f(x)
    step = step0
    sweeps = 0
    while step > tol && sweeps < maxsweeps
        sweeps += 1
        improved = false
        # `fx` may be Inf (absorption below pmin); an Inf-relative threshold
        # would be NaN and make every comparison false.
        thresh = isfinite(fx) ? minrel * max(1.0, abs(fx)) : 0.0
        for i in eachindex(x), s in (-step, step)
            xi = clamp(x[i] + s, 0.0, 1.0)
            xi == x[i] && continue
            old = x[i]
            x[i] = xi
            fxi = f(x)
            if fxi < fx - thresh
                fx = fxi
                improved = true
            elseif fxi < fx
                fx = fxi          # better point, but not counted as progress
            else
                x[i] = old
            end
        end
        improved || (step /= 2)
    end
    fx
end

"""
    fitness(g; K = 3, filters = true, escape = true, kwargs...) -> NamedTuple

Aggregate Phase-1 fitness of a (Float64) game. Returns
`(value, m1, m2, m3, m4, m5, report)`; `value = -Inf` when a filter fires.

`m5` is the ESCAPE MARGIN (P2, `escape_margin`): the best `min_{j ∈ J} K_j(ξ)`
over supports without a certain quitter. It must be POSITIVE, otherwise no
continuation vector `x` with `x_j > v^j` for all `j` admits an equilibrium with
quitting, the game is (presumed) an escape game, and Simon (2007) Theorem 4
gives it approximate equilibria — it can never be a counterexample, whatever
`m1`…`m4` say. This is the screen the project ran for the first time on
7 Aug 2026, after both finalists had already gone through the whole pipeline;
both failed it.

The score is LEXICOGRAPHIC and not a minimum over all five: while `m5 ≤ 0` the
value IS `m5`, which is negative and therefore below every viable score, so a
search climbs out of the escape class first and only then maximises
`min(m1, m2, m3, m4)` as before. A flat `-Inf` there would leave a
differential-evolution run with no gradient at all.

Two honest limits of `m5`. It is a Float64 search, so `m5 ≤ 0` is a screen and
not a proof (`escape_witness` turns `m5 > 0` into an exact rational witness;
certifying `m5 ≤ 0` costs a dedicated run, see `scripts/simon_escape_class.jl`).
And it only looks at supports where nobody quits with certainty: witnesses with
a certain quitter need exact equalities `K_j = 0`, which a float search cannot
land on and which no perturbation of the payoffs preserves.
"""
function fitness(g::QuittingGame{Float64}; K::Int = 3, filters::Bool = true,
                 escape::Bool = true, qtrials::Int = 60, starts::Int = 120,
                 escape_starts::Int = 32, escape_tol::Float64 = 1e-9,
                 rng::AbstractRNG = Random.Xoshiro(42))
    report = nothing
    if filters
        gq = convert(QuittingGame{Rational{BigInt}}, rationalize_game(g))
        # F9 is handled here through m5, so that the search gets a gradient
        # instead of a flat rejection; the battery below is F1–F8.
        report = filter_report(gq; qtrials = qtrials, escape = false)
        report.viable ||
            return (value = -Inf, m1 = NaN, m2 = NaN, m3 = NaN, m4 = NaN, m5 = NaN,
                    report = report)
    end
    m5 = Inf
    if escape
        # `escape_tol` demands a ROBUST violation, not just a positive one: a
        # search campaign snaps its games to a coarse denominator before anything
        # exact runs, and snapping moves an entry of the pair matrix M by up to
        # 2/(2·denom). A witness with m5 = 1e-8 does not survive that.
        m5, _ = escape_margin(g; starts = escape_starts, rng = rng)
        m5 <= max(escape_tol, 1e-9) &&
            return (value = min(m5 - escape_tol, 0.0), m1 = NaN, m2 = NaN, m3 = NaN,
                    m4 = NaN, m5 = m5, report = report)
    end
    m1, _ = min_stationary_violation(g; starts = starts, rng = rng)
    m1 <= 1e-9 && return (value = -Inf, m1 = m1, m2 = NaN, m3 = NaN, m4 = NaN,
                          m5 = m5, report = report)
    m2, _ = min_directional_violation_grid(g)
    m2 <= 1e-9 && return (value = -Inf, m1 = m1, m2 = m2, m3 = NaN, m4 = NaN,
                          m5 = m5, report = report)
    m3 = Inf
    for k in 2:K
        mk, _ = min_periodic_violation(g, k; starts = max(20, starts ÷ k), rng = rng)
        m3 = min(m3, mk)
        m3 <= 1e-9 && return (value = -Inf, m1 = m1, m2 = m2, m3 = m3, m4 = NaN,
                              m5 = m5, report = report)
    end
    m4, _ = min_corner_violation(g; starts = starts, rng = rng)
    m4 <= 1e-9 && return (value = -Inf, m1 = m1, m2 = m2, m3 = m3, m4 = m4,
                          m5 = m5, report = report)
    (value = min(m1, m2, m3, m4), m1 = m1, m2 = m2, m3 = m3, m4 = m4, m5 = m5,
     report = report)
end

"""
    rationalize_game(g; denom = 64) -> QuittingGame{Rational{Int}}

Snap every payoff to the nearest rational with denominator ≤ `denom`.

Do NOT use `rationalize(Int, v; tol = ...)` here: `tol` is an accuracy bound,
not a denominator bound, so it happily returns things like 186//373 for
`denom = 32`. Exact Phase-2 certification is very sensitive to this — the
interval B&B runs `Rational{BigInt}` arithmetic over a 4-dimensional box tree,
and three-digit denominators made it run for over an hour without finishing
where small ones take minutes. Best rational approximation under a hard
denominator cap is cheap (`denom` trials per entry), so just do it directly.
"""
function rationalize_game(g::QuittingGame{Float64}; denom::Int = 64)
    function snap(v::Float64)
        best, err = 0 // 1, Inf
        for d in 1:denom
            n = round(Int, v * d)
            e = abs(v - n / d)
            if e < err
                best, err = n // d, e
            end
        end
        best
    end
    r = map(snap, g.r)
    QuittingGame{Rational{Int}}(g.N, Matrix{Rational{Int}}(r))
end
