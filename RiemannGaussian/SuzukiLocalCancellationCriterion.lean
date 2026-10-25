/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiLocalCancellationTransfer
import RiemannGaussian.SuzukiLocalCancellationPrimePowers

/-!
# The ordinary-prime version of the local Suzuki criterion

The proved constant cost of proper prime powers preserves the precise
all-positive-exponents lower-bound target. Both arithmetic estimates remain
unproved; only their equivalence and conditional implication to RH are asserted.
-/

namespace RiemannGaussian
noncomputable section

/-- A uniformly bounded change preserves the real-cutoff subpolynomial lower bound. -/
theorem localCancellation_lower_bound_of_bounded_sub {f g : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hfg : ∀ X : ℝ, 1 ≤ X → |f X - g X| ≤ K)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℝ, 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → -(C * X ^ ε) ≤ g X) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℝ, 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → -(C * X ^ ε) ≤ f X := by
  intro ε hε
  obtain ⟨C, hC, X₀, hX₀, hb⟩ := hg ε hε
  refine ⟨C + K, add_nonneg hC hK, X₀, hX₀, fun X hX => ?_⟩
  have hX1 : 1 ≤ X := by linarith
  have hp : 1 ≤ X ^ ε := Real.one_le_rpow hX1 hε.le
  have he := (abs_le.mp (hfg X hX1)).1
  have hh := hb X hX
  nlinarith [mul_le_mul_of_nonneg_left hp hK]

/-- The exact research target is unchanged by deleting proper prime powers,
with the uniform constant cost included in the exponent-dependent allowance. -/
theorem suzukiLocalArithmetic_lower_bound_iff_ordinary :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℝ, 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → -(C * X ^ ε) ≤ suzukiLocalArithmeticComparison X) ↔
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℝ, 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → -(C * X ^ ε) ≤ suzukiLocalOrdinaryArithmeticComparison X) := by
  have hK : 0 ≤ 54 * ((Real.sqrt 2 + 1) * Real.log 2) := by positivity
  constructor
  · apply localCancellation_lower_bound_of_bounded_sub hK
    intro X hX
    rw [abs_sub_comm]
    exact abs_suzukiLocalArithmeticComparison_sub_ordinary_le hX
  · exact localCancellation_lower_bound_of_bounded_sub hK
      (fun _ hX => abs_suzukiLocalArithmeticComparison_sub_ordinary_le hX)

/-- The ordinary-prime version of the precise arithmetic target also implies
Mathlib's literal RH, with proper powers and the PNT boundary fully discharged. -/
theorem riemannHypothesis_of_suzukiLocalOrdinaryArithmeticComparison_lower_bound
    (hg : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℝ, 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → -(C * X ^ ε) ≤ suzukiLocalOrdinaryArithmeticComparison X) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_suzukiLocalArithmeticComparison_subpolynomial_lower_bound
    (suzukiLocalArithmetic_lower_bound_iff_ordinary.mpr hg)

end
end RiemannGaussian
