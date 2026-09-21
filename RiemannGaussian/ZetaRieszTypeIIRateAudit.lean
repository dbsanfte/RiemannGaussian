/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszTypeIIReduction

/-!
# Quantifier and rate checks for the proposed Type-II input

Logarithmic-error sieve theorems do not supply the fixed positive power
saving in `LocalizedTypeIIBound`. The existing growing-height Vinogradov
rectangle also fails its lower-height hypothesis on a fixed-height cofinal
scale. These facts audit applicability; neither asserts that the actual
arithmetic estimate is false or unprovable.
-/

namespace RiemannGaussian.ZetaRieszTypeII
noncomputable section
open Filter Topology

/-- At logarithmic coordinate t, the ratio of a log-saving envelope to
the required power-saving envelope grows without bound. -/
theorem logarithmic_to_power_ratio_tendsto (B : ℕ) :
    Tendsto (fun t : ℝ =>
      (Real.exp t / t ^ B) / Real.exp ((999 / 1000 : ℝ) * t)) atTop atTop := by
  have h := tendsto_exp_mul_div_rpow_atTop (B : ℝ) (1 / 1000) (by norm_num)
  apply h.congr'
  filter_upwards [] with t
  rw [Real.rpow_natCast]
  calc
    Real.exp ((1 / 1000 : ℝ) * t) / t ^ B =
        (Real.exp t / Real.exp ((999 / 1000 : ℝ) * t)) / t ^ B := by
      rw [← Real.exp_sub]
      congr 2
      ring
    _ = _ := by ring

/-- No fixed constant turns an inverse-logarithmic error envelope into
the exact 1/1000 power saving at all sufficiently large scales. -/
theorem logarithmic_envelope_eventually_exceeds (B : ℕ) (C : ℝ) :
    ∀ᶠ t : ℝ in atTop,
      C * Real.exp ((999 / 1000 : ℝ) * t) < Real.exp t / t ^ B := by
  filter_upwards [(logarithmic_to_power_ratio_tendsto B).eventually
    (eventually_gt_atTop C)] with t ht
  exact (lt_div_iff₀ (Real.exp_pos _)).mp ht

/-- The lower-height condition of any fixed positive-degree Vinogradov
rectangle eventually fails at every fixed height as the block scale grows. -/
theorem fixed_height_outside_growing_rectangle (y : ℝ) {d : ℕ} (hd : 0 < d) :
    ∀ᶠ M : ℕ in atTop, ¬(M : ℝ) ^ d ≤ |y| := by
  have ht := (tendsto_pow_atTop (Nat.ne_of_gt hd)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [ht.eventually (eventually_gt_atTop |y|)] with M hM
  exact not_le_of_gt hM

/-- The repository's literal Dirichlet power-saving rectangle is therefore
unavailable cofinally at the fixed height of the candidate zero. -/
theorem fixed_height_outside_repo_vmvt (y : ℝ) {k : ℕ} (hk : 12 ≤ k) :
    ∀ᶠ M : ℕ in atTop, ¬(M : ℝ) ^ (2 * k - 2) ≤ |y| :=
  fixed_height_outside_growing_rectangle y (by omega)

end
end RiemannGaussian.ZetaRieszTypeII
