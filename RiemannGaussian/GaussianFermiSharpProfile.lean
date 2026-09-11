/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiBootstrapProfile
import RiemannGaussian.GaussianHalfLaplaceShift

/-!
# A larger Fermi surplus from the shifted Gaussian endpoint

The exact shifted half-Gaussian identity improves the pole estimate enough
to reach target width `9/50`, using the same established coefficient bounds
and the first global Fermi margin. The surplus is uniform over that entire
coefficient class. No new phase family is selected.
-/

namespace RiemannGaussian.GaussianFermiSharpProfile
noncomputable section
open Complex Filter MeasureTheory Set
open GaussianFermiLaplaceOrder GaussianHalfLaplaceBounds GaussianHalfLaplaceShift
open GaussianFermiProfileSurplus

/-- A rational lower enclosure at the largest source damping used by the
sharper comparison. -/
theorem halfGaussian_unit_thirtyone_fourhundredths_lower :
    (3389 / 4000 : ℝ) ≤ halfGaussian 1 (31 / 400) := by
  have hs : (443 / 500 : ℝ) ≤ Real.sqrt Real.pi / 2 := by
    have hpi := Real.pi_gt_d2
    have hsq := Real.sq_sqrt Real.pi_pos.le
    nlinarith [Real.sqrt_nonneg Real.pi]
  have h := halfGaussian_tangent_lower (by norm_num : (0 : ℝ) < 1) (31 / 400)
  norm_num at h
  linarith

/-- Retaining the shifted interval gives a sharper rational pole enclosure
than the reflection estimate with only a tangent on the other half-line. -/
theorem halfGaussian_unit_neg_three_eighths_upper :
    halfGaussian 1 (-(3 / 8)) ≤ (557 / 500 : ℝ) := by
  have hs : Real.sqrt Real.pi ≤ (887 / 500 : ℝ) := by
    have hpi := Real.pi_lt_d4
    have hsq := Real.sq_sqrt Real.pi_pos.le
    nlinarith [Real.sqrt_nonneg Real.pi]
  have he : Real.exp ((3 / 8 : ℝ) ^ 2 / 4) ≤ 256 / 247 := by
    have h := Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ (3 / 8) ^ 2 / 4)
      (by norm_num : (3 / 8 : ℝ) ^ 2 / 4 < 1)
    norm_num at h ⊢
    exact h
  norm_num at he
  have h := halfGaussian_neg_shift_upper (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) ≤ 3 / 8)
  norm_num only [div_one, mul_one] at h
  calc
    _ ≤ _ := h
    _ ≤ (256 / 247 : ℝ) * ((887 / 500) / 2 + 3 / 16) := by gcongr
    _ ≤ _ := by norm_num

/-- Every coefficient family satisfying the existing coarse bounds has a
strict surplus at target `9/50`, uniformly in the available margin interval. -/
theorem profile_surplus {a₀ a₁ M μ : ℝ} (ha₀ : 0 ≤ a₀)
    (ha₀u : a₀ ≤ 37 / 200) (ha₁ : 79 / 250 ≤ a₁) (hM : M ≤ 61 / 100)
    (hμ0 : 149 / 1000 ≤ μ) (hμ1 : μ ≤ 3 / 20) :
    a₀ * halfGaussian 1 (-(5 / 2) * μ) + M / 10 + 1 / 2000 ≤
      a₁ * halfGaussian 1 ((5 / 2) * (9 / 50 - μ)) := by
  have ht : (3389 / 4000 : ℝ) ≤ halfGaussian 1 ((5 / 2) * (9 / 50 - μ)) := by
    apply halfGaussian_unit_thirtyone_fourhundredths_lower.trans
    exact halfGaussian_antitone (by norm_num) (by linarith)
  have hp : halfGaussian 1 (-(5 / 2) * μ) ≤ (557 / 500 : ℝ) := by
    apply (halfGaussian_antitone (by norm_num)
      (show -(3 / 8 : ℝ) ≤ -(5 / 2) * μ by linarith)).trans
    exact halfGaussian_unit_neg_three_eighths_upper
  have hs : (79 / 250 : ℝ) * (3389 / 4000) ≤
      a₁ * halfGaussian 1 ((5 / 2) * (9 / 50 - μ)) :=
    mul_le_mul ha₁ ht (by norm_num) (by linarith)
  have hpu : a₀ * halfGaussian 1 (-(5 / 2) * μ) ≤ (37 / 200 : ℝ) * (557 / 500) :=
    (mul_le_mul_of_nonneg_left hp ha₀).trans (mul_le_mul_of_nonneg_right ha₀u (by norm_num))
  linarith

/-- Dilation gives a logarithmically growing surplus at every edge distance
at most `9/(50*L)`, for every coefficient family in the coarse class. -/
theorem scaled_profile_surplus {a₀ a₁ M L m d : ℝ} (ha₀ : 0 ≤ a₀)
    (ha₀u : a₀ ≤ 37 / 200) (ha₁ : 79 / 250 ≤ a₁) (hM : M ≤ 61 / 100)
    (hL : 0 < L) (hm0 : 149 / 1000 ≤ L * m) (hm1 : L * m ≤ 3 / 20)
    (hd : d ≤ 9 / (50 * L)) :
    a₀ * halfGaussian (4 / (25 * L ^ 2)) (-m) + M * L / 4 + L / 800 ≤
      a₁ * halfGaussian (4 / (25 * L ^ 2)) (d - m) := by
  let r := 2 / (5 * L)
  have hr : 0 < r := by dsimp [r]; positivity
  have hB : 1 * r ^ 2 = 4 / (25 * L ^ 2) := by dsimp [r]; field_simp; ring
  have hp : -(5 / 2) * (L * m) * r = -m := by dsimp [r]; field_simp
  have ht : (5 / 2) * (9 / 50 - L * m) * r = 9 / (50 * L) - m := by
    dsimp [r]
    field_simp
  have ep : halfGaussian (4 / (25 * L ^ 2)) (-m) =
      (5 / 2) * L * halfGaussian 1 (-(5 / 2) * (L * m)) := by
    apply mul_left_cancel₀ hr.ne'
    rw [← hB, ← hp, halfGaussian_scale hr]
    dsimp [r]
    field_simp
  have et : halfGaussian (4 / (25 * L ^ 2)) (9 / (50 * L) - m) =
      (5 / 2) * L * halfGaussian 1 ((5 / 2) * (9 / 50 - L * m)) := by
    apply mul_left_cancel₀ hr.ne'
    rw [← hB, ← ht, halfGaussian_scale hr]
    dsimp [r]
    field_simp
  calc
    _ = ((5 / 2) * L) *
        (a₀ * halfGaussian 1 (-(5 / 2) * (L * m)) + M / 10 + 1 / 2000) := by
      rw [ep]
      ring
    _ ≤ ((5 / 2) * L) * (a₁ * halfGaussian 1 ((5 / 2) * (9 / 50 - L * m))) :=
      mul_le_mul_of_nonneg_left (profile_surplus ha₀ ha₀u ha₁ hM hm0 hm1) (by positivity)
    _ = a₁ * halfGaussian (4 / (25 * L ^ 2)) (9 / (50 * L) - m) := by rw [et]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact halfGaussian_antitone (by positivity) (by linarith)

/-- The original exact phase row satisfies the sharper scaled comparison. -/
theorem exact_scaled_profile_surplus {L m d : ℝ} (hL : 0 < L)
    (hm0 : 149 / 1000 ≤ L * m) (hm1 : L * m ≤ 3 / 20) (hd : d ≤ 9 / (50 * L)) :
    phaseContactExactCoefficients 0 * halfGaussian (4 / (25 * L ^ 2)) (-m) +
      (∑ j : Fin 9, if j = 0 then 0 else phaseContactExactCoefficients j) * L / 4 +
        L / 800 ≤
          phaseContactExactCoefficients 1 * halfGaussian (4 / (25 * L ^ 2)) (d - m) :=
  scaled_profile_surplus (phaseContactExactCoefficients_pos 0).le exact_constant_upper
    exact_first_lower exact_nonconstant_mass_upper hL hm0 hm1 hd

/-- The sharper Gaussian scale is admissible whenever `L*m<=2/5`. -/
theorem scale_admissible {L m : ℝ} (hL : 1 ≤ L) (hm : 0 ≤ m) (hmu : L * m ≤ 2 / 5) :
    m ^ 2 ≤ 4 / (25 * L ^ 2) ∧ 4 / (25 * L ^ 2) ≤ 1 := by
  have hLp : 0 < L := by linarith
  have hmle : m ≤ 2 / (5 * L) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have he : (2 / (5 * L)) ^ 2 = 4 / (25 * L ^ 2) := by field_simp; ring
  constructor
  · rw [← he]
    exact pow_le_pow_left₀ hm hmle 2
  · apply (div_le_one (by positivity)).mpr
    nlinarith

end
end RiemannGaussian.GaussianFermiSharpProfile
