import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace LlaminarSoftmaxAudit

/-- The max operand already supplies one unit scale. The evaluator is arbitrary
except for its explicit value at zero; this is not a GPU floating-point model. -/
theorem max_rebase_evaluator (evaluate : ℝ → ℝ) (hzero : evaluate 0 = 1)
    (a b : ℝ) :
    (evaluate (a - max a b), evaluate (b - max a b)) =
      if a ≤ b then (evaluate (a - b), 1) else (1, evaluate (b - a)) := by
  by_cases h : a ≤ b
  · simp [h, hzero]
  · simp [h, max_eq_left (le_of_not_ge h), hzero]

/-- Real exponential specialization of the unchanged online max scaling. -/
theorem max_rebase_exp (a b : ℝ) :
    (Real.exp (a - max a b), Real.exp (b - max a b)) =
      if a ≤ b then (Real.exp (a - b), 1) else (1, Real.exp (b - a)) :=
  max_rebase_evaluator Real.exp Real.exp_zero a b

/-- Equal finite maxima need no exponential evaluation. -/
theorem equal_max_scales (evaluate : ℝ → ℝ) (hzero : evaluate 0 = 1) (a : ℝ) :
    (evaluate (a - max a a), evaluate (a - max a a)) = (1, 1) := by
  simp [hzero]

/-- A single live tile has unit tile scale. The native producer's initialization
and one-tile loop bound are separate source obligations. -/
theorem one_tile_scale (evaluate : ℝ → ℝ) (hzero : evaluate 0 = 1) (a : ℝ) :
    evaluate (a - a) = 1 := by simp [hzero]

/-- Signed weighted outputs require a numerator bound as well as a partition
bound. This exact identity isolates both errors before taking absolute values. -/
theorem weighted_quotient_difference (n z dn dz : ℝ)
    (hz : z ≠ 0) (hzd : z + dz ≠ 0) :
    (n + dn) / (z + dz) - n / z = (dn - (n / z) * dz) / (z + dz) := by
  field_simp
  ring

#print axioms max_rebase_evaluator
#print axioms max_rebase_exp
#print axioms equal_max_scales
#print axioms one_tile_scale
#print axioms weighted_quotient_difference
end LlaminarSoftmaxAudit
