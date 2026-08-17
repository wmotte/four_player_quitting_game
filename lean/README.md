# Lean 4 replay

Mechanical translation of the JSON certificates for `cand_seed202_r78_gen011`.
The files are not hand-written. There is no `sorry`, `admit`, `axiom`, or
`native_decide` in this corpus.

A logged `lake build Formal` on 17 August 2026 accepted this corpus
(950 jobs). The log is [docs/lean_build.txt](../docs/lean_build.txt).
Replay with the commands below.

## Toolchain

- Lean 4.33.0-rc1 (`lean-toolchain`)
- Mathlib `v4.33.0-rc1` (`lakefile.toml`, pinned in `lake-manifest.json`)

## Build

```
cd lean
lake exe cache get
```

Cheap check, minutes after the cache:

```
lake build Formal.Certificates.Seed202_r78_gen011.PeriodK2.Batch01
lake build Formal.Certificates.SimultaneousQuit.Batch01
lake build Formal.Certificates.FrontA.Batch01
lake build Formal.Certificates.Sharpness.Batch01
```

Full corpus, hours. The directional tree (46 modules) and the first-round
tree (35 modules) dominate.

```
lake build
```

An unbounded parallel `lake build` can start one Lean process per core and
exhaust memory. If that happens, build the batches above first, then the
`Main` modules one at a time.

## Layout

| Path | Claim |
|---|---|
| `Formal/Certificates/Directional/Seed202R78Gen011Margin/` | Directional margin, input to the stationary branch |
| `Formal/Certificates/V0/Seed202R78Gen011*` | No equilibrium that ends in round 1 |
| `Formal/Certificates/Seed202_r78_gen011/PeriodK2/` | Period-2 Nullstellensatz identities |
| `Formal/Certificates/FrontA/` | Front [A], this game only |
| `Formal/Certificates/SimultaneousQuit/` | No simultaneous positive quit rates, this game only |
| `Formal/Certificates/Sharpness/` | Stationary-margin upper witness, this game only |

`Formal/Smoke.lean` is a four-line Nullstellensatz identity, to confirm the
toolchain before the generated files.

## Trust

The kernel plus Mathlib. The Python checker in `../checker/` is an
independent check of the same JSON, and does not use Lean.
