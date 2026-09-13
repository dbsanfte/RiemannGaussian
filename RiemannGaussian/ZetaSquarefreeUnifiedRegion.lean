/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaUnifiedZeroFree
import RiemannGaussian.ZetaSquarefreeGaussianRegionUnion

/-!
# Complete explicit coverage in the signed squarefree response

Restoring the all-height pole-reserve region removes the inherited
500002 starting-height restriction from this transport. Every center with
absolute ordinate at least three has the full radius of the combined
explicit width. The original signed prime envelope remains untouched.
-/

namespace RiemannGaussian.SquarefreeUnifiedRegion
noncomputable section
open Complex

/-- Evaluate the complete explicit width at the upper doubled-window endpoint. -/
def margin (y : ℝ) : ℝ := ZetaUnifiedZeroFree.width (2 * |y| + 3)

/-- The margin is positive and satisfies the original quarter-width cap. -/
theorem margin_bounds (y : ℝ) : 0 < margin y ∧ margin y < 1 / 4 :=
  ZetaUnifiedZeroFree.width_bounds _

/-- The full Cauchy radius is larger than one by half the zero-free margin. -/
def radius (y : ℝ) : ℝ := 1 + margin y / 2

/-- The full radius satisfies the original two-harmonic threshold. -/
theorem radius_bounds (y : ℝ) : 1 < radius y ∧ radius y < 9 / 8 := by
  obtain ⟨hm, hmu⟩ := margin_bounds y
  unfold radius
  constructor <;> linarith

/-- At these centers the pole-separation cap is inactive. -/
theorem radius_eq {y : ℝ} (hy : 3 ≤ |y|) :
    SquarefreeEulerBand.radius y (margin y) = radius y :=
  SquarefreeEulerBand.radius_eq (by linarith) (margin_bounds y).2

/-- Every zero in the entire doubled window obeys the complete margin.
The actual zero-height floor supplies the logarithmic domain condition. -/
theorem window_margin {y : ℝ} (hy : 3 ≤ |y|) (ρ : NontrivialZetaZero)
    (hρ : |ρ.1.im - 2 * y| ≤ 2 * SquarefreeEulerBand.radius y (margin y)) :
    ρ.1.re < 1 - margin y := by
  rw [radius_eq hy] at hρ
  have hu := (abs_abs_sub_abs_le_abs_sub ρ.1.im (2 * y)).trans hρ
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hu
  have ht : |ρ.1.im| ≤ |2 * |y| + 3| := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 * |y| + 3)]
    linarith [(abs_le.mp hu).2, (radius_bounds y).2]
  have hL : 1 ≤ ZetaNearOneBudgetLimit.scale ρ.1.im := by
    change 1 ≤ Real.log (|ρ.1.im| + 2)
    linarith [thirteen_tenths_lt_log_abs_im_add_two ρ]
  have hm : margin y ≤ ZetaUnifiedZeroFree.width ρ.1.im :=
    ZetaUnifiedZeroFree.width_antitone_abs hL ht
  linarith [ZetaUnifiedZeroFree.exact_margin ρ]

/-- Literal quotient analyticity holds around the whole larger closed
disc already at absolute center height three. -/
theorem analyticOnNhd_response {y : ℝ} (hy : 3 ≤ |y|) :
    AnalyticOnNhd ℂ squarefreeEulerResponse
      (Metric.closedBall (3 / 2 + I * y) (radius y)) := by
  rw [← radius_eq hy]
  exact SquarefreeLocalWindow.analyticOnNhd_response (by linarith)
    (margin_bounds y).1 (margin_bounds y).2 (window_margin hy)

/-- All marked responses inherit the entire larger disc and their full
signed prime envelope. The response constant may depend on the center. -/
theorem exists_response_bound {y : ℝ} (hy : 3 ≤ |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ), 0 < r → r ≤ radius y →
      ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime) → ∀ P : ℕ,
        Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
        ∀ (p : Polynomial ℂ) (N : ℕ),
          ‖RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
            C * SquarefreeEulerPhase.envelope 2 S (3 / 2 + I * y) r * r⁻¹ ^ N *
              ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  rw [← radius_eq hy]
  exact SquarefreeLocalWindow.exists_response_bound (by linarith)
    (margin_bounds y).1 (margin_bounds y).2 (window_margin hy)

/-- No radius supplied by either Gaussian component is lost. -/
theorem gaussian_radius_le (y : ℝ) : SquarefreeGaussianRegionUnion.radius y ≤ radius y := by
  have h := ZetaUnifiedZeroFree.gaussian_width_le (2 * |y| + 3)
  change SquarefreeGaussianRegionUnion.margin y ≤ margin y at h
  unfold SquarefreeGaussianRegionUnion.radius radius
  linarith

end
end RiemannGaussian.SquarefreeUnifiedRegion
