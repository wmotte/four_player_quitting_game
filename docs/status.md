# Status on `cand_seed202_r78_gen011`

Honesty labels: *certified* means an exact run with a certificate in this
repository; *proved* means a human lemma, game-independent; *open* means not
settled.

No counterexample has been established. The game below is a candidate: it
passes Simon's escape screen, and the first two branches of the 2024
decomposition, together with the jump-free and periodic pieces of the third,
are certified empty on it. The bounded mixed remainder is open. That remainder
is G3.

## The game

`cand_seed202_r78_gen011`, digest `2ed6cd64d2fd`, family `11486bec`. Four
players, rational payoffs, recorded in
`certificates/seed202_r78_gen011/manifest.json`.

## Closed

| Object | Status |
|---|---|
| Stationary ε-equilibrium | *certified* empty, `ε* = 1/20`, on the whole cube `[0,1]^4` including the boundary |
| Equilibrium that ends in round 1, deviator held at the independent min-max | *certified* empty |
| Jump-free absorption path | *certified* empty. The essential-APS argument excludes Flesch paths; simultaneous positive rates are closed by an exact finite condition on the unilateral matrix |
| Period 2 and period 3 | *certified* empty, full grid of quitting patterns |
| Constant two-player support | *certified* empty: the chain map is Möbius, all eleven pencils hyperbolic |
| Constant support, all 15 nonempty quitting sets | *certified* empty at zero tolerance, one decreasing direction per set. Converting the margins into the ε-version the argument needs costs constants that are computed but not all assembled |
| Shrinking chains that switch the quitting set | *certified* empty, with positive slack |
| Some coordinate eventually reaches 1 | *certified* empty |
| Eventually-singleton fully absorbing paths | *certified* empty |
| Partially absorbing paths | *proved* empty in every quitting game |
| Short singleton-return pieces `q → J → q` | *certified* forbidden, all 28 patterns |
| Short pair-cycles | 229 of 231 *certified* excluded. On one certified cycle the return is Möbius, `x₃' = 4420 x₃ / (1377 − 4887 x₃)`, and `x₃'/x₃ > 260/81` on the whole cell |

The JSON groups behind the first two rows and the periodic row are in
`certificates/seed202_r78_gen011/`. Lean translations of those groups, and of
the front-[A], simultaneous-quit, and sharpness witnesses, are in `lean/`.

## Negative results (ceilings, not failures)

These are proofs that a whole family of methods cannot decide G3, however
much computing is spent on it.

- Iterating an outer bound on the values that mixed paths can achieve never
  reaches the empty set. The corner of the set is a limit of real jumps, with
  exact rational witnesses, so any sound outer bound has to keep that corner.
- Separation of recurrent-support hulls from the value set is exact and has
  no error term, but the same corner makes it permanently blind on 32,624 of
  32,767 families (99.56%).
- Clamping the profile near the origin and asking whether a region containing
  the origin misses a hull fails because the origin lies *inside* every such
  hull, for every support, by an exact rational linear programme.
- There is no linear potential that decreases along every admissible step: an
  exact Gordan witness, full rank, on this game and two others.
- Convex piecewise-linear potentials fail as well. The programme collapses to
  exactly zero on a minimal blocking set of steps, most of which carry an
  exact existence certificate. That is the one place where the decisive
  number is numerical.
- Discrete over-approximations of the step relation (extra support history,
  value bands, mass clocks, two-edge memory) remain non-empty.

An invariant-set search on the available outer approximation is defeated by
twenty-one certified segments that enter the collar and leave it again. Those
exit states are terminal, so what has been refuted is the sieve, not the
game.

## Open: G3

Bounded mixed paths. Two statements, both needing a quantitative margin.

1. A chain of jumps cannot keep away from both boundary collars indefinitely.
2. A chain cannot enter a neighbourhood of zero infinitely often without
   converging to it.

The constant-support case of (1) is closed. What remains is chains that
switch sets. The finite sieve is exhausted: with the tail left free the
system is underdetermined at every length.

The half of (2) that forbids diving into the collar and coming back out is
not closable on the outer approximation available. The half that forbids
staying near zero forever without converging is where the three ceilings
bite. Replacing the hull in the third test by a single-support version
escapes that ceiling and shrinks the region to a shell, under a hypothesis
that is not proved. That is not a closure.

Of the steps that could block a proof, roughly two thirds admit no successor,
and only about one in seven can be extended in both directions.

## What this repository does not claim

It does not claim that a four-player quitting game without uncorrelated
ε-equilibrium has been found. It does not claim that sunspot equilibria fail.
The Lean files are a translation of the JSON. A logged `lake build Formal`
on 17 August 2026 accepted them (950 jobs); see [lean_build.txt](lean_build.txt).
