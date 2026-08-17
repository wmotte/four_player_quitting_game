# A computational search for a four-player quitting game without uncorrelated ε-equilibrium

Existence of a uniform ε-equilibrium in quitting games is known for at most
three players and open for four. This repository records a computational
attack on that question, on one explicit four-player game with rational
payoffs.

**No counterexample has been established.** Two of the three branches of the
known existence criterion are closed on this game. The remaining branch,
bounded mixed absorption, is open. That gap is called G3 below.

## The problem

A quitting game is a stochastic game in which each player, each round, can
only continue or quit. The game ends at the first quit. Payoffs depend on who
quit. Solan (1999) proved existence for at most three players. From four
players on, the question is open; it is Problem 251* in the EMS list
(Rassias 2021, contribution of Solan).

Every quitting game has a *sunspot* ε-equilibrium (Solan and Solan 2020). A
counterexample can therefore only concern *uncorrelated* Nash ε-equilibria.

Ashkenazi-Golan, Krasikov, Rainer and Solan (*Mathematical Programming* 203,
2024, Theorem 3.4) give a decomposition: a quitting game has an
ε-equilibrium for every ε > 0 if and only if one of three things happens.

1. A stationary ε-equilibrium exists.
2. An ε-equilibrium that ends in the first round exists.
3. There is an absorbing profile in which every player is sequentially
   ε-perfect.

The search tries to refute all three on one game. See [docs/problem.md](docs/problem.md).

## The approach

The work is computational, and it is done in **Julia**, because that is the
toolkit at hand. A search proposes a game; everything after that is exact.

The search has two stages. The first draws the matrix of unilateral quitting
payoffs at random, with small-denominator rationals, and keeps only those
that lie outside every known existence theorem. The second fixes such a
matrix and searches over the remaining payoffs (those that apply when two or
more players quit together) by differential evolution. The objective is the
smallest of several violation margins, so the search cannot buy one margin
with another.

That stage runs in floating point and is not to be trusted. Its output is a
shortlist. Survivors are snapped to rational payoffs and re-screened. Only
then does the ladder begin.

From the ladder onward nothing leaves exact rational arithmetic. Each step
produces a machine-checkable certificate. A second program, written
independently in Python and calling none of the Julia code, checks those
certificates again. The same certificates are also replayed as Lean 4
theorems against the Lean kernel.

This repository ships the certificates, the Python checker, the Lean
corpus for one game, and the Julia search that proposed it.

## The game

The live candidate is `cand_seed202_r78_gen011` (digest `2ed6cd64d2fd`).
Four players. Rational payoffs. It violates Simon's escape criterion, as any
counterexample must: a game that satisfies that criterion *has* approximate
equilibria (Simon 2007, Theorem 4).

The 15 coalition payoff rows (players 1–4; coalitions in binary order
`{1}`, `{2}`, `{1,2}`, `{3}`, …, `{1,2,3,4}`) are in
`certificates/seed202_r78_gen011/manifest.json`.

## What is closed, and where it is stuck

On this game, certified in exact arithmetic:

| Claim | Status |
|---|---|
| No stationary ε-equilibrium | closed, margin `ε* = 1/20` on the whole cube `[0,1]^4` |
| No ε-equilibrium that ends in round 1 | closed |
| No absorption path without jumps | closed |
| Period-2 and period-3 cyclic profiles | closed |
| Constant quitting set, all 15 nonempty subsets | closed (zero-tolerance margins; the ε-conversion constants are computed but not all assembled) |
| Shrinking chains that switch the quitting set | closed, with positive slack |
| A coordinate eventually reaches 1; eventually-singleton fully absorbing paths | closed |
| Short singleton-return pieces of a chain (all 28 patterns) | closed |
| Short pair-cycles | 229 of 231 closed; one certified return is Möbius and expands by more than `260/81` on the whole cell |

What remains is G3: *bounded* mixed paths, those that mix continuous stretches
with discrete jumps and do not shrink. That remainder is two statements, both
of which need a quantitative margin.

- A chain cannot stay away from both boundary collars for arbitrarily many
  consecutive steps.
- A chain that enters a neighbourhood of zero infinitely often must converge
  to it.

More computing of the present kind will not close either. Discrete
over-approximations of the step relation stay non-empty. A linear potential
that decreases along every admissible step does not exist (an exact Gordan
witness). The convex piecewise-linear version collapses to zero on a
certified blocking set. Three independent ceilings show that whole families
of methods cannot decide this case. What is needed is an argument by hand.

All games examined here have only normal players in Simon's min-max sense.
That puts them inside Theorem 4.1 of Simon (2012): a counterexample of this
kind would falsify Question 1 of that paper, which is open.

Details: [docs/status.md](docs/status.md). Literature: [LITERATURE.md](LITERATURE.md).

## How to verify the certificates

Python 3, standard library only. No packages.

```
python3 checker/check_certificates.py certificates/seed202_r78_gen011
```

Expected last line: `162/162 accepted as expected`.

The full audit (corpus, good fixtures, corrupted fixtures, case enumeration):

```
python3 checker/run_tests.py
```

Expected last line: `all checker tests passed`.

The checker uses `fractions.Fraction` throughout. It does not solve and it
does not search. Every check is evaluate, expand, compare. It shares no code
with the Julia pipeline that produced the certificates. See
[docs/certificates.md](docs/certificates.md) and
[checker/README.md](checker/README.md).

## How to replay the certificates in Lean 4

The Lean files under `lean/` are a mechanical translation of the same JSON.
A logged `lake build Formal` on 17 August 2026 accepted the whole corpus
(950 jobs, including Mathlib). The log is [docs/lean_build.txt](docs/lean_build.txt).

To replay:

```
cd lean
lake exe cache get
lake build Formal
```

The period-2 batch alone is the cheap check:

```
lake build Formal.Certificates.Seed202_r78_gen011.PeriodK2.Batch01
```

Toolchain: Lean 4.33.0-rc1, Mathlib `v4.33.0-rc1`. See [lean/README.md](lean/README.md).

## How to run the search

Julia 1.10 or later. `CDDLib` is needed for the Flesch-path gate.

```
julia --project=julia -e 'using Pkg; Pkg.instantiate(); Pkg.test()'
julia --project=julia julia/scripts/run_phase1.jl --seed 1 \
      --gens 50 --pop 28 --rmats 10 --out artifacts/candidates/run1
julia --project=julia julia/scripts/sieve_candidates.jl artifacts/candidates/run1
```

The search writes a shortlist of rational games. It does not certify them.
See [julia/README.md](julia/README.md).

## Layout

```
certificates/seed202_r78_gen011/   162 JSON certificates and the manifest
checker/                           independent Python checker
lean/                              Lean 4 replay of the same certificates
julia/                             the search that proposed the game
docs/                              the problem, the status, the file format
LITERATURE.md                      papers
```

## License

Apache-2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE).

## Author

Wim Otte, University Medical Center Utrecht.
w.m.otte@umcutrecht.nl
