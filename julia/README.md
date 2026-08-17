# Heuristic search

Two stages, both in Julia. The first draws the unilateral matrix `R` and keeps
only those that pass the Q-matrix, LCP, principal-minor, and Flesch-path
gates. The second fixes such an `R` and runs differential evolution over the
forty-four multi-quit payoffs. The objective is the smallest of four violation
margins, after leaving Simon's escape class.

This stage runs in floating point. Its output is a shortlist. Survivors are
snapped to rationals and rescreened. Nothing here is a certificate.

```
julia --project=julia -e 'using Pkg; Pkg.instantiate(); Pkg.test()'
julia --project=julia julia/scripts/run_phase1.jl --seed 1 \
      --gens 50 --pop 28 --rmats 10 --out artifacts/candidates/run1
julia --project=julia julia/scripts/sieve_candidates.jl artifacts/candidates/run1
```

`CDDLib` is needed only for the Flesch-path gate. The rest of the search is
the standard library.
