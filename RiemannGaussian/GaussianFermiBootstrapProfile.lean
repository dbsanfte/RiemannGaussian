/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaFermiGlobalMargin

/-!
# A Gaussian surplus after feeding back the first Fermi region

The proved `3/20` region supplies normalized interior margins close to
`3/20`. Exact Gaussian bounds then give a strict source surplus at the
larger target width `4/25`. The scalar theorem is uniform over the same
coarse coefficient class as before; no new phase coefficients are fitted.
-/

namespace RiemannGaussian.GaussianFermiBootstrapProfile
noncomputable section
open Complex Filter MeasureTheory Set
open GaussianFermiLaplaceOrder GaussianHalfLaplaceBounds GaussianFermiProfileSurplus

/-- An exact lower enclosure for the positive damping argument needed by
the second interior comparison. -/
theorem halfGaussian_unit_thirtythree_thousandths_lower :
    (1739 / 2000 : ℝ) ≤ halfGaussian 1 (33 / 1000) := by
  have hs : (443 / 500 : ℝ) ≤ Real.sqrt Real.pi / 2 := by
    have hpi := Real.pi_gt_d2
    have hsq := Real.sq_sqrt Real.pi_pos.le
    nlinarith [Real.sqrt_nonneg Real.pi]
  have h := halfGaussian_tangent_lower (by norm_num : (0 : ℝ) < 1) (33 / 1000)
  norm_num at h
  linarith

/-- Exact Gaussian reflection and the exponential tangent enclose the
negative damping pole at the larger interior margin. -/
theorem halfGaussian_unit_neg_nine_twentieths_upper :
    halfGaussian 1 (-(9 / 20)) ≤ (121 / 100 : ℝ) := by
  have hs : Real.sqrt Real.pi ≤ (887 / 500 : ℝ) := by
    have hpi := Real.pi_lt_d4
    have hsq := Real.sq_sqrt Real.pi_pos.le
    nlinarith [Real.sqrt_nonneg Real.pi]
  have he : Real.exp ((9 / 20 : ℝ) ^ 2 / 4) ≤ 1600 / 1519 := by
    have h := Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ (9 / 20) ^ 2 / 4)
      (by norm_num : (9 / 20 : ℝ) ^ 2 / 4 < 1)
    norm_num at h ⊢
    exact h
  have hp : 0 ≤ Real.exp ((9 / 20 : ℝ) ^ 2 / 4) - 1 / 2 := by
    linarith [Real.add_one_le_exp ((9 / 20 : ℝ) ^ 2 / 4)]
  norm_num at he hp
  have h := halfGaussian_neg_upper (by norm_num : (0 : ℝ) < 1) (9 / 20)
  norm_num only [div_one, mul_one] at h
  calc
    _ ≤ _ := h
    _ ≤ (887 / 500 : ℝ) * (1600 / 1519 - 1 / 2) + 9 / 40 := by gcongr
    _ ≤ _ := by norm_num

/-- Every coefficient family satisfying the established coarse bounds has
a positive surplus for the target `4/25`, uniformly on the new normalized
margin interval. -/
theorem profile_surplus {a₀ a₁ M μ : ℝ} (ha₀ : 0 ≤ a₀)
    (ha₀u : a₀ ≤ 37 / 200) (ha₁ : 79 / 250 ≤ a₁) (hM : M ≤ 61 / 100)
    (hμ0 : 149 / 1000 ≤ μ) (hμ1 : μ ≤ 3 / 20) :
    a₀ * halfGaussian 1 (-3 * μ) + M / 12 + 1 / 20000 ≤
      a₁ * halfGaussian 1 (3 * (4 / 25 - μ)) := by
  have ht : (1739 / 2000 : ℝ) ≤ halfGaussian 1 (3 * (4 / 25 - μ)) := by
    apply halfGaussian_unit_thirtythree_thousandths_lower.trans
    exact halfGaussian_antitone (by norm_num) (by linarith)
  have hp : halfGaussian 1 (-3 * μ) ≤ (121 / 100 : ℝ) := by
    apply (halfGaussian_antitone (by norm_num) (show -(9 / 20 : ℝ) ≤ -3 * μ by linarith)).trans
    exact halfGaussian_unit_neg_nine_twentieths_upper
  have hs : (79 / 250 : ℝ) * (1739 / 2000) ≤ a₁ * halfGaussian 1 (3 * (4 / 25 - μ)) :=
    mul_le_mul ha₁ ht (by norm_num) (by linarith)
  have hpu : a₀ * halfGaussian 1 (-3 * μ) ≤ (37 / 200 : ℝ) * (121 / 100) :=
    (mul_le_mul_of_nonneg_left hp ha₀).trans (mul_le_mul_of_nonneg_right ha₀u (by norm_num))
  linarith

/-- Exact Gaussian dilation turns the second normalized surplus into an
unbounded logarithmic-height surplus at every smaller target edge distance. -/
theorem scaled_profile_surplus {a₀ a₁ M L m d : ℝ} (ha₀ : 0 ≤ a₀)
    (ha₀u : a₀ ≤ 37 / 200) (ha₁ : 79 / 250 ≤ a₁) (hM : M ≤ 61 / 100)
    (hL : 0 < L) (hm0 : 149 / 1000 ≤ L * m) (hm1 : L * m ≤ 3 / 20)
    (hd : d ≤ 4 / (25 * L)) :
    a₀ * halfGaussian (1 / (9 * L ^ 2)) (-m) + M * L / 4 + 3 * L / 20000 ≤
      a₁ * halfGaussian (1 / (9 * L ^ 2)) (d - m) := by
  let r := 1 / (3 * L)
  have hr : 0 < r := by dsimp [r]; positivity
  have hB : 1 * r ^ 2 = 1 / (9 * L ^ 2) := by dsimp [r]; field_simp; ring
  have hp : -3 * (L * m) * r = -m := by dsimp [r]; field_simp
  have ht : 3 * (4 / 25 - L * m) * r = 4 / (25 * L) - m := by
    dsimp [r]
    field_simp
  have ep : halfGaussian (1 / (9 * L ^ 2)) (-m) =
      3 * L * halfGaussian 1 (-3 * (L * m)) := by
    apply mul_left_cancel₀ hr.ne'
    rw [← hB, ← hp, halfGaussian_scale hr]
    dsimp [r]
    field_simp
  have et : halfGaussian (1 / (9 * L ^ 2)) (4 / (25 * L) - m) =
      3 * L * halfGaussian 1 (3 * (4 / 25 - L * m)) := by
    apply mul_left_cancel₀ hr.ne'
    rw [← hB, ← ht, halfGaussian_scale hr]
    dsimp [r]
    field_simp
  calc
    _ = (3 * L) * (a₀ * halfGaussian 1 (-3 * (L * m)) + M / 12 + 1 / 20000) := by
      rw [ep]
      ring
    _ ≤ (3 * L) * (a₁ * halfGaussian 1 (3 * (4 / 25 - L * m))) :=
      mul_le_mul_of_nonneg_left (profile_surplus ha₀ ha₀u ha₁ hM hm0 hm1) (by positivity)
    _ = a₁ * halfGaussian (1 / (9 * L ^ 2)) (4 / (25 * L) - m) := by rw [et]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact halfGaussian_antitone (by positivity) (by linarith)

/-- The existing exact coefficient row satisfies the second scaled surplus
without changing any phase or fitting a new family. -/
theorem exact_scaled_profile_surplus {L m d : ℝ} (hL : 0 < L)
    (hm0 : 149 / 1000 ≤ L * m) (hm1 : L * m ≤ 3 / 20) (hd : d ≤ 4 / (25 * L)) :
    phaseContactExactCoefficients 0 * halfGaussian (1 / (9 * L ^ 2)) (-m) +
      (∑ j : Fin 9, if j = 0 then 0 else phaseContactExactCoefficients j) * L / 4 +
        3 * L / 20000 ≤
          phaseContactExactCoefficients 1 * halfGaussian (1 / (9 * L ^ 2)) (d - m) :=
  scaled_profile_surplus (phaseContactExactCoefficients_pos 0).le exact_constant_upper
    exact_first_lower exact_nonconstant_mass_upper hL hm0 hm1 hd

/-- The larger normalized margin still lies in the admissible Gaussian
scale range; the general scale condition is `L*m<=1/3`. -/
theorem scale_admissible {L m : ℝ} (hL : 1 ≤ L) (hm : 0 ≤ m) (hmu : L * m ≤ 1 / 3) :
    m ^ 2 ≤ 1 / (9 * L ^ 2) ∧ 1 / (9 * L ^ 2) ≤ 1 := by
  have hLp : 0 < L := by linarith
  have hmle : m ≤ 1 / (3 * L) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have he : (1 / (3 * L)) ^ 2 = 1 / (9 * L ^ 2) := by field_simp; ring
  constructor
  · rw [← he]
    exact pow_le_pow_left₀ hm hmle 2
  · apply (div_le_one (by positivity)).mpr
    nlinarith

/-- At heights where the global Fermi margin has its proved eventual
formula, the full normalized interval required by the second comparison
follows from elementary logarithmic inequalities. -/
theorem normalized_margin_bounds_of_eq {t : ℝ} (ht : 0 < t)
    (hlog : 100000 ≤ Real.log t)
    (he : zetaFermiZeroMargin (48 * t) = 3 / (20 * Real.log (48 * t))) :
    149 / 1000 ≤ Real.log t * zetaFermiZeroMargin (48 * t) ∧
      Real.log t * zetaFermiZeroMargin (48 * t) ≤ 3 / 20 := by
  have h48 : 0 ≤ Real.log (48 : ℝ) := Real.log_nonneg (by norm_num)
  have h48u : Real.log (48 : ℝ) ≤ 47 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 48)]
  have hS : Real.log (48 * t) = Real.log 48 + Real.log t :=
    Real.log_mul (by norm_num) ht.ne'
  have hSp : 0 < Real.log (48 * t) := by rw [hS]; linarith
  rw [he, ← mul_div_assoc]
  constructor
  · apply (le_div_iff₀ (by positivity)).mpr
    rw [hS]
    linarith
  · apply (div_le_iff₀ (by positivity)).mpr
    rw [hS]
    linarith

end
end RiemannGaussian.GaussianFermiBootstrapProfile
