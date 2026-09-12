/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiSharpProfile
import RiemannGaussian.GaussianHalfLaplaceCurvature

/-!
# A uniform Fermi surplus after retaining endpoint curvature

The proved `9/50` interior margin and the curvature of the shifted
Gaussian interval give a surplus at target `3/16`. The scalar comparison
holds for the entire established coarse coefficient class; no new phase
coefficients are selected. Actual zero exclusion is proved downstream.
-/

namespace RiemannGaussian.GaussianFermiCurvatureProfile
noncomputable section
open Complex Filter MeasureTheory Set
open GaussianFermiLaplaceOrder GaussianHalfLaplaceBounds GaussianHalfLaplaceCurvature
open GaussianFermiProfileSurplus

/-- A rational source enclosure at the largest positive damping in the
new normalized comparison. -/
theorem halfGaussian_unit_nineteen_thousandths_lower :
    (1753 / 2000 : ℝ) ≤ halfGaussian 1 (19 / 1000) := by
  have hs : (443 / 500 : ℝ) ≤ Real.sqrt Real.pi / 2 := by
    have hpi := Real.pi_gt_d2
    have hsq := Real.sq_sqrt Real.pi_pos.le
    nlinarith [Real.sqrt_nonneg Real.pi]
  have h := halfGaussian_tangent_lower (by norm_num : (0 : ℝ) < 1) (19 / 1000)
  norm_num at h
  linarith

/-- Retaining the displaced interval's curvature encloses the larger
negative pole damping with a rational bound sufficient for the surplus. -/
theorem halfGaussian_unit_neg_nine_twentieths_upper :
    halfGaussian 1 (-(9 / 20)) ≤ (1167 / 1000 : ℝ) := by
  have hs : Real.sqrt Real.pi ≤ (709 / 400 : ℝ) := by
    have hpi := Real.pi_lt_d4
    have hsq := Real.sq_sqrt Real.pi_pos.le
    nlinarith [Real.sqrt_nonneg Real.pi]
  have he : Real.exp ((9 / 20 : ℝ) ^ 2 / 4) ≤ 1600 / 1519 := by
    have h := Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ (9 / 20) ^ 2 / 4)
      (by norm_num : (9 / 20 : ℝ) ^ 2 / 4 < 1)
    norm_num at h ⊢
    exact h
  have h := halfGaussian_neg_curvature_upper (by norm_num : (0 : ℝ) ≤ 9 / 20)
  calc
    _ ≤ _ := h
    _ ≤ (1600 / 1519 : ℝ) * ((709 / 400) / 2 + (9 / 20) / 2 -
        ((9 / 20) / 2) ^ 3 / (3 * (1 + ((9 / 20) / 2) ^ 2))) := by
      apply mul_le_mul he
        (by gcongr)
        (by have := Real.sqrt_nonneg Real.pi; norm_num; linarith)
        (by norm_num)
    _ ≤ _ := by norm_num

/-- The entire established coefficient class has a strict surplus at
target `3/16`, uniformly over the proved normalized margin interval. -/
theorem profile_surplus {a₀ a₁ M μ : ℝ} (ha₀ : 0 ≤ a₀)
    (ha₀u : a₀ ≤ 37 / 200) (ha₁ : 79 / 250 ≤ a₁) (hM : M ≤ 61 / 100)
    (hμ0 : 1799 / 10000 ≤ μ) (hμ1 : μ ≤ 9 / 50) :
    a₀ * halfGaussian 1 (-(5 / 2) * μ) + M / 10 + 1 / 20000 ≤
      a₁ * halfGaussian 1 ((5 / 2) * (3 / 16 - μ)) := by
  have ht : (1753 / 2000 : ℝ) ≤ halfGaussian 1 ((5 / 2) * (3 / 16 - μ)) := by
    apply halfGaussian_unit_nineteen_thousandths_lower.trans
    exact halfGaussian_antitone (by norm_num) (by linarith)
  have hp : halfGaussian 1 (-(5 / 2) * μ) ≤ (1167 / 1000 : ℝ) := by
    apply (halfGaussian_antitone (by norm_num)
      (show -(9 / 20 : ℝ) ≤ -(5 / 2) * μ by linarith)).trans
    exact halfGaussian_unit_neg_nine_twentieths_upper
  have hs : (79 / 250 : ℝ) * (1753 / 2000) ≤
      a₁ * halfGaussian 1 ((5 / 2) * (3 / 16 - μ)) :=
    mul_le_mul ha₁ ht (by norm_num) (by linarith)
  have hpu : a₀ * halfGaussian 1 (-(5 / 2) * μ) ≤ (37 / 200 : ℝ) * (1167 / 1000) :=
    (mul_le_mul_of_nonneg_left hp ha₀).trans (mul_le_mul_of_nonneg_right ha₀u (by norm_num))
  linarith

/-- Gaussian dilation turns the uniform curvature surplus into a
logarithmically growing margin for every edge distance at most `3/(16L)`. -/
theorem scaled_profile_surplus {a₀ a₁ M L m d : ℝ} (ha₀ : 0 ≤ a₀)
    (ha₀u : a₀ ≤ 37 / 200) (ha₁ : 79 / 250 ≤ a₁) (hM : M ≤ 61 / 100)
    (hL : 0 < L) (hm0 : 1799 / 10000 ≤ L * m) (hm1 : L * m ≤ 9 / 50)
    (hd : d ≤ 3 / (16 * L)) :
    a₀ * halfGaussian (4 / (25 * L ^ 2)) (-m) + M * L / 4 + L / 8000 ≤
      a₁ * halfGaussian (4 / (25 * L ^ 2)) (d - m) := by
  let r := 2 / (5 * L)
  have hr : 0 < r := by dsimp [r]; positivity
  have hB : 1 * r ^ 2 = 4 / (25 * L ^ 2) := by dsimp [r]; field_simp; ring
  have hp : -(5 / 2) * (L * m) * r = -m := by dsimp [r]; field_simp
  have ht : (5 / 2) * (3 / 16 - L * m) * r = 3 / (16 * L) - m := by dsimp [r]; field_simp
  have ep : halfGaussian (4 / (25 * L ^ 2)) (-m) =
      (5 / 2) * L * halfGaussian 1 (-(5 / 2) * (L * m)) := by
    apply mul_left_cancel₀ hr.ne'
    rw [← hB, ← hp, halfGaussian_scale hr]
    dsimp [r]
    field_simp
  have et : halfGaussian (4 / (25 * L ^ 2)) (3 / (16 * L) - m) =
      (5 / 2) * L * halfGaussian 1 ((5 / 2) * (3 / 16 - L * m)) := by
    apply mul_left_cancel₀ hr.ne'
    rw [← hB, ← ht, halfGaussian_scale hr]
    dsimp [r]
    field_simp
  calc
    _ = ((5 / 2) * L) *
        (a₀ * halfGaussian 1 (-(5 / 2) * (L * m)) + M / 10 + 1 / 20000) := by rw [ep]; ring
    _ ≤ ((5 / 2) * L) * (a₁ * halfGaussian 1 ((5 / 2) * (3 / 16 - L * m))) :=
      mul_le_mul_of_nonneg_left (profile_surplus ha₀ ha₀u ha₁ hM hm0 hm1) (by positivity)
    _ = a₁ * halfGaussian (4 / (25 * L ^ 2)) (3 / (16 * L) - m) := by rw [et]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (halfGaussian_antitone (by positivity) (by linarith)) (by linarith)

/-- The already established exact phase row satisfies the new scaled
comparison without changing any phase or coefficient. -/
theorem exact_scaled_profile_surplus {L m d : ℝ} (hL : 0 < L)
    (hm0 : 1799 / 10000 ≤ L * m) (hm1 : L * m ≤ 9 / 50) (hd : d ≤ 3 / (16 * L)) :
    phaseContactExactCoefficients 0 * halfGaussian (4 / (25 * L ^ 2)) (-m) +
      (∑ j : Fin 9, if j = 0 then 0 else phaseContactExactCoefficients j) * L / 4 + L / 8000 ≤
        phaseContactExactCoefficients 1 * halfGaussian (4 / (25 * L ^ 2)) (d - m) :=
  scaled_profile_surplus (phaseContactExactCoefficients_pos 0).le exact_constant_upper
    exact_first_lower exact_nonconstant_mass_upper hL hm0 hm1 hd

/-- Elementary logarithmic bounds place the actual `9/50` band margin
in the narrow interval needed by the uniform curvature comparison. -/
theorem normalized_margin_bounds {t : ℝ} (ht : 0 < t) (hlog : 100000 ≤ Real.log t) :
    1799 / 10000 ≤ Real.log t * (9 / (50 * Real.log (48 * t))) ∧
      Real.log t * (9 / (50 * Real.log (48 * t))) ≤ 9 / 50 := by
  have h48 : 0 ≤ Real.log (48 : ℝ) := Real.log_nonneg (by norm_num)
  have h48u : Real.log (48 : ℝ) ≤ 47 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 48)]
  have hS : Real.log (48 * t) = Real.log 48 + Real.log t := Real.log_mul (by norm_num) ht.ne'
  have hSp : 0 < Real.log (48 * t) := by rw [hS]; linarith
  rw [← mul_div_assoc]
  constructor
  · apply (le_div_iff₀ (by positivity)).mpr
    rw [hS]
    linarith
  · apply (div_le_iff₀ (by positivity)).mpr
    rw [hS]
    linarith

end
end RiemannGaussian.GaussianFermiCurvatureProfile
