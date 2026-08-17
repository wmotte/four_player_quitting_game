import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Real.Basic

/-- Toolchain smoke test in the exact shape the auto-generated C1
certificates use: a Nullstellensatz cofactor identity discharged by
`linear_combination`. The system {x·y − 1 = 0, x = 0} is inconsistent:
1 = (−y)·(x·y − 1)·… — here simply 1 = y·h₂-arranged combination. -/
theorem smoke_nullstellensatz (x y : ℝ)
    (h1 : x * y - 1 = 0)
    (h2 : x = 0)
    : False := by
  have key : (1 : ℝ) = 0 := by
    linear_combination (-1) * h1 + y * h2
  exact one_ne_zero key
