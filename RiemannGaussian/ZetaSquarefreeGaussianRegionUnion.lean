/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianRegionUnion
import RiemannGaussian.ZetaSquarefreeGaussianRetainedRegion

/-!
# The improved explicit region in the original squarefree arithmetic

The complete doubled-ordinate window uses the maximum of both proved curves.
The original marked responses inherit its full Cauchy radius and unchanged
signed two-harmonic prime envelope. Each constant may depend on the center.
No estimate for the surviving ordinary-prime carrier is supplied here.
-/

namespace RiemannGaussian.SquarefreeGaussianRegionUnion
noncomputable section
open Complex ZetaGaussianRegionUnion

/-- The full doubled-window height, including both endpoint enlargements. -/
def windowLogHeight (y : ℝ) : ℝ := Real.log (2 * |y| + 5)

/-- The entire window stays in the positive logarithmic cost domain. -/
theorem windowLogHeight_ge_one (y : ℝ) : 1 ≤ windowLogHeight y := by
  apply (Real.le_log_iff_exp_le (by positivity : 0 < 2 * |y| + 5)).mpr
  linarith [Real.exp_one_lt_d9, abs_nonneg y]

/-- The union is evaluated at the upper endpoint of the enlarged window. -/
def margin (y : ℝ) : ℝ := width (2 * |y| + 3)

/-- Every margin is positive and obeys the enlarged physical ceiling. -/
theorem margin_bounds (y : ℝ) : 0 < margin y ∧ margin y ≤ 1 / 40500 :=
  width_bounds _

/-- The enlarged logarithmic height is exactly the height of the chosen endpoint. -/
theorem windowLogHeight_eq (y : ℝ) :
    ZetaNearOneBudgetLimit.scale (2 * |y| + 3) = windowLogHeight y := by
  change Real.log (|2 * |y| + 3| + 2) = Real.log (2 * |y| + 5)
  rw [abs_of_nonneg (by positivity : 0 ≤ 2 * |y| + 3)]
  congr 1
  ring

/-- The full improved Cauchy radius, without an additional fractional loss. -/
def radius (y : ℝ) : ℝ := 1 + margin y / 2

/-- The new radius exceeds one and satisfies the two-harmonic threshold. -/
theorem radius_bounds (y : ℝ) : 1 < radius y ∧ radius y < 9 / 8 := by
  obtain ⟨hm, hmu⟩ := margin_bounds y
  unfold radius
  constructor <;> linarith

/-- The pole-separation cap is inactive at all eligible arithmetic centers. -/
theorem radius_eq {y : ℝ} (hy : 500002 ≤ |y|) :
    SquarefreeEulerBand.radius y (margin y) = radius y := by
  exact SquarefreeEulerBand.radius_eq (by linarith) (by linarith [(margin_bounds y).2])

/-- Every ordinate in the actual doubled window satisfies the new height bounds. -/
theorem window_heights {y t : ℝ} (hy : 500002 ≤ |y|)
    (ht : |t - 2 * y| ≤ 2 * radius y) :
    1000000 ≤ |t| ∧ ZetaNearOneBudgetLimit.scale t ≤ windowLogHeight y := by
  have h := (abs_abs_sub_abs_le_abs_sub t (2 * y)).trans ht
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  constructor
  · linarith [(radius_bounds y).2]
  · apply Real.log_le_log (by positivity : 0 < |t| + 2)
    linarith [(radius_bounds y).2]

/-- The enlarged explicit region discharges the entire local denominator window. -/
theorem window_margin {y : ℝ} (hy : 500002 ≤ |y|) (ρ : NontrivialZetaZero)
    (hρ : |ρ.1.im - 2 * y| ≤ 2 * SquarefreeEulerBand.radius y (margin y)) :
    ρ.1.re < 1 - margin y := by
  rw [radius_eq hy] at hρ
  obtain ⟨ht, hL⟩ := window_heights hy hρ
  have hL0 := ZetaGaussianBandBudget.scale_lower ht
  have hm : margin y ≤ width ρ.1.im :=
    width_antitone hL0 (by rw [windowLogHeight_eq]; exact hL)
  have hz := exact_margin ρ ht
  linarith

/-- The literal squarefree quotient is analytic around the full improved disc. -/
theorem analyticOnNhd_response {y : ℝ} (hy : 500002 ≤ |y|) :
    AnalyticOnNhd ℂ squarefreeEulerResponse
      (Metric.closedBall (3 / 2 + I * y) (radius y)) := by
  rw [← radius_eq hy]
  exact SquarefreeLocalWindow.analyticOnNhd_response (by linarith)
    (margin_bounds y).1 (by linarith [(margin_bounds y).2]) (window_margin hy)

/-- All original marked responses retain their signed prime envelope on
the larger disc. The single response constant may depend on the center. -/
theorem exists_response_bound {y : ℝ} (hy : 500002 ≤ |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ), 0 < r → r ≤ radius y →
      ∀ S : Finset ℕ, (∀ a ∈ S, a.Prime) → ∀ P : ℕ,
        Squarefree P → (∀ a ∈ P.primeFactors, a ∉ S) →
        ∀ (p : Polynomial ℂ) (N : ℕ),
          ‖RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
            C * SquarefreeEulerPhase.envelope 2 S (3 / 2 + I * y) r * r⁻¹ ^ N *
              ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  rw [← radius_eq hy]
  exact SquarefreeLocalWindow.exists_response_bound (by linarith)
    (margin_bounds y).1 (by linarith [(margin_bounds y).2]) (window_margin hy)

private theorem previous_margin_eq_width (y : ℝ) :
    SquarefreeGaussianRetainedRegion.margin y =
      ZetaGaussianRetainedRegion.explicitWidth (2 * |y| + 3) := by
  rw [ZetaGaussianRetainedRegion.explicitWidth_eq_min
    (by rw [windowLogHeight_eq]; exact windowLogHeight_ge_one y), windowLogHeight_eq]
  rfl

/-- The previous arithmetic Cauchy radius is contained at every center. -/
theorem previous_radius_le (y : ℝ) : SquarefreeGaussianRetainedRegion.radius y ≤ radius y := by
  have h := previous_width_le (2 * |y| + 3)
  rw [← previous_margin_eq_width] at h
  change SquarefreeGaussianRetainedRegion.margin y ≤ margin y at h
  unfold SquarefreeGaussianRetainedRegion.radius radius
  linarith

/-- At moderate height the excess radius above one is at least ten times larger. -/
theorem tenfold_radius_gain {y : ℝ} (hy : windowLogHeight y ≤ 64) :
    10 * (SquarefreeGaussianRetainedRegion.radius y - 1) ≤ radius y - 1 := by
  have h := tenfold_previous_le (t := 2 * |y| + 3)
    (by rw [windowLogHeight_eq]; exact windowLogHeight_ge_one y)
    (by rwa [windowLogHeight_eq])
  rw [← previous_margin_eq_width] at h
  change 10 * SquarefreeGaussianRetainedRegion.margin y ≤ margin y at h
  unfold SquarefreeGaussianRetainedRegion.radius radius
  linarith

end
end RiemannGaussian.SquarefreeGaussianRegionUnion
