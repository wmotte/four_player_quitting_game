# Certificate format

JSON, UTF-8, one certificate per file. All numbers are exact rationals,
written as strings `"n/d"` or `"n"`, never as floats. A certificate is
self-contained: it embeds the polynomials it talks about. Verification is
decision-free arithmetic (evaluate, expand, compare). No solving, no search,
no floating point.

The independent checker is `checker/check_certificates.py`. The Lean files
under `lean/` are a mechanical translation of the same JSON.

## Envelope

```json
{
  "format_version": 1,
  "id": "stable unique identifier",
  "game": "seed202_r78_gen011",
  "case": "enumeration case, optional",
  "claim": "one-line statement",
  "type": "nullstellensatz | rur | bnb_trace | aps_trace | witness",
  "domain": {},
  "data": {}
}
```

`format_version` must be `1`. The corpus in this repository uses three of the
five types: `nullstellensatz`, `bnb_trace`, and `witness`. The other two
appear only as hand-built fixtures in `checker/tests/good/`.

## Types

| Type | What the checker does |
|---|---|
| `nullstellensatz` | Expand `Σ gᵢ fᵢ` and require the constant 1. The system has no solution over any extension of ℚ. |
| `rur` | Check the rational univariate representation, the Sturm chain, isolation, and a strict sign of the refuting condition on each isolated root, by exact interval arithmetic. |
| `bnb_trace` | On every leaf of a binary split tree, the cited condition has a strict constant sign, so it has no zero there. Coverage is automatic for a split tree. A flat list of leaves is accepted only up to 2000 leaves, and only if the leaves lie in the root, have disjoint interiors, and have volumes that sum to the root. |
| `aps_trace` | Every declared polytope inclusion via exact non-negative Farkas multipliers, and final emptiness via a Farkas witness. This checks the bookkeeping, not that each polytope is the operator image of its predecessor. |
| `witness` | Substitute the stated point and compare, exactly. |

Interval arithmetic is outward. For multilinear polynomials in at most 12
variables the exact range is taken from the box vertices.

## The manifest

`certificates/seed202_r78_gen011/manifest.json` ties the files to the game.
It carries the exact payoff matrix, a commit hash for the producing code, and
a case table. The checker rejects a manifest that records a dirty working
tree, and it requires each row's `case` label to match the certificate.

For periodic `nullstellensatz` certificates, `checker/bind_systems.py`
re-derives the indifference system from the payoff matrix and the case label,
sharing no code with the producer, and requires equality. A valid identity
about the wrong game is then rejected.

## Groups in this corpus

| Directory | Claim | Type |
|---|---|---|
| `directional/` | Directional margin on the vanishing-probability simplex | `bnb_trace` |
| `v0/` | No equilibrium that ends in round 1 | `bnb_trace`, `witness` |
| `front_a/` | The profile in which exactly coalition K quits outright is never a stage-game Nash equilibrium | `witness` |
| `lcp0/` | The linear complementarity problem at zero has only the trivial solution | `witness` |
| `no_fap/` | No sequentially perfect Flesch absorption path | `witness` |
| `periodic_k2/` | Period-2 indifference systems inconsistent | `nullstellensatz` |
| `simultaneous_quit/` | No strictly positive simultaneous quit rates on a coalition | `witness` |
| `sharpness/` | An explicit stationary profile whose deviation gain is an upper bound on the margin | `witness` |

There are no G3 certificates. The remaining mixed case is not in a form a
finite algebraic certificate can close.

## What a green checker does not prove

- That the case *list* is complete. `checker/enumerate_cases.py` re-derives
  the period-k list from the mathematical description and checks its own
  counts and partition. Two human lemmas (shift-invariance of type A;
  droppability of the type-B tail) sit outside that check.
- That a `bnb_trace` excludes the right function of the game, except where
  the conditions are re-derived from the payoff matrix.
- Anything beyond what the JSON types encode. The Lean replay of those
  same files was accepted by `lake build Formal` on 17 August 2026
  (see [lean_build.txt](lean_build.txt)).
