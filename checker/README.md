# The independent checker

A second implementation of "is this certificate valid?". It shares no code,
no library and no language with the Julia pipeline that produced the
certificates: Python 3, standard library only, `fractions.Fraction`
throughout, no solving and no search. Every check is evaluate, expand,
compare.

```
python3 check_certificates.py ../certificates/seed202_r78_gen011
python3 run_tests.py
python3 enumerate_cases.py ../certificates/seed202_r78_gen011/manifest.json
```

`run_tests.py` asserts four things: every exported certificate is accepted,
every hand-built good fixture is accepted, every corrupted fixture is
rejected for the recorded reason, and the period-k case list matches its
closed form and contains every periodic case the candidate manifest names.

Expected on this repository:

```
exported certificates: 162/162 accepted
good fixtures: 9/9 accepted
negative suite: 37/37 rejected for the right reason
case enumeration
...
all checker tests passed
```

## What each type is checked against

| Type | Check |
|---|---|
| `nullstellensatz` | Expand `Σ gᵢ fᵢ` and require the constant 1. |
| `rur` | Rational univariate representation, Sturm chain, isolation, strict sign of the refuting condition. |
| `bnb_trace` | Cited condition has a strict constant sign on every leaf. Coverage by a split tree, or by volume plus disjoint interiors for a short flat list. |
| `aps_trace` | Declared inclusions and final emptiness, by exact Farkas witnesses. |
| `witness` | Substitute the point and compare, exactly. |

The live corpus uses `nullstellensatz`, `bnb_trace`, and `witness`. The other
two types appear as fixtures only.

## Binding to the game

A Nullstellensatz identity can be valid and still talk about the wrong game.
`bind_systems.py` re-derives the periodic indifference system from the
manifest's payoff matrix and the case label, and requires the certificate's
equations to equal it. `enumerate_cases.py` re-derives the period-k case list
from the mathematical description and checks that every periodic case the
manifest names is on that list.

## Limits

- `aps_trace` checks bookkeeping, not that each polytope is the operator
  image of its predecessor.
- Completeness of the case list rests on two human lemmas (shift-invariance
  of type A; droppability of the type-B tail) that this code implements but
  does not prove.
- There are no certificates for the remaining mixed case G3.

The fixtures under `tests/` use a historical game name in their JSON. They
are format tests, not claims about that game.
