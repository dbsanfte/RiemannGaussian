/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianHalfLaplaceBounds
import RiemannGaussian.ZetaPhaseContactPrimal

/-!
# A strict Gaussian source surplus for the existing exact phase family

Coarse rational enclosures for the already proved exact coefficient row
and the actual Gaussian integrals give a strict positive surplus. The
comparison is uniform over an interval of normalized interior margins.
Exact dilation transfers it to every positive logarithmic scale. This
does not yet pay for the remaining pole, gamma and outside-height costs.
-/

namespace RiemannGaussian.GaussianFermiProfileSurplus

noncomputable section
open Complex MeasureTheory Set
open GaussianFermiLaplaceOrder GaussianHalfLaplaceBounds

/-- The existing exact unit-frequency coefficient exceeds the coarse
rational value needed by the Gaussian comparison. -/
theorem exact_first_lower :
    (79 / 250 : ℝ) ≤ phaseContactExactCoefficients 1 := by
  have h := (abs_le.mp (abs_phaseContactExactCoefficients_sub_center_le 1)).1
  norm_num [phaseContactPrimalCenter, phaseContactPrimalCenterQ] at h
  linarith

/-- A coarse rational upper bound for the true constant coefficient. -/
theorem exact_constant_upper :
    phaseContactExactCoefficients 0 ≤ (37 / 200 : ℝ) := by
  have h := (abs_le.mp (abs_phaseContactExactCoefficients_sub_center_le 0)).2
  norm_num [phaseContactPrimalCenter, phaseContactPrimalCenterQ] at h
  linarith

/-- The complete nonconstant coefficient mass of the existing exact
family, including all small higher frequencies, is bounded at once. -/
theorem exact_nonconstant_mass_upper :
    (∑ j : Fin 9, if j = 0 then 0 else phaseContactExactCoefficients j) ≤ (61 / 100 : ℝ) := by
  have h (j : Fin 9) : phaseContactExactCoefficients j ≤
      phaseContactPrimalCenter j + 1 / 10 ^ 15 := by
    have hj := (abs_le.mp (abs_phaseContactExactCoefficients_sub_center_le j)).2
    linarith
  calc
    _ ≤ ∑ j : Fin 9, if j = 0 then 0 else phaseContactPrimalCenter j + 1 / 10 ^ 15 := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs <;> simp_all only [le_refl]
    _ ≤ _ := by norm_num [Fin.sum_univ_succ, phaseContactPrimalCenter, phaseContactPrimalCenterQ]

/-- The full true coefficient mass, including the constant mode, is at
most one. This pays for every common bounded height error. -/
theorem exact_total_mass_upper : (∑ j : Fin 9, phaseContactExactCoefficients j) ≤ 1 := by
  calc
    _ ≤ ∑ j : Fin 9, (phaseContactPrimalCenter j + 1 / 10 ^ 15) := by
      apply Finset.sum_le_sum
      intro j _
      have h := (abs_le.mp (abs_phaseContactExactCoefficients_sub_center_le j)).2
      linarith
    _ ≤ _ := by norm_num [Fin.sum_univ_succ, phaseContactPrimalCenter, phaseContactPrimalCenterQ]

/-- Every coefficient family with these coarse bounds has a strict
Gaussian source surplus throughout the whole normalized-margin interval. -/
theorem profile_surplus {a₀ a₁ M μ : ℝ} (ha₀ : 0 ≤ a₀)
    (ha₀u : a₀ ≤ 37 / 200) (ha₁ : 79 / 250 ≤ a₁) (hM : M ≤ 61 / 100)
    (hμ0 : 1 / 10 ≤ μ) (hμ1 : μ ≤ 21 / 200) :
    a₀ * halfGaussian 1 (-3 * μ) + M / 12 + 1 / 400 ≤
      a₁ * halfGaussian 1 (3 * (3 / 20 - μ)) := by
  have ht : (811 / 1000 : ℝ) ≤ halfGaussian 1 (3 * (3 / 20 - μ)) := by
    apply halfGaussian_unit_three_twentieths_lower.trans
    exact halfGaussian_antitone (by norm_num) (by linarith)
  have hp : halfGaussian 1 (-3 * μ) ≤ (109 / 100 : ℝ) := by
    apply (halfGaussian_antitone (by norm_num) (show -(63 / 200 : ℝ) ≤ -3 * μ by linarith)).trans
    exact halfGaussian_unit_neg_sixtythree_twohundredths_upper
  have hs : (79 / 250 : ℝ) * (811 / 1000) ≤ a₁ * halfGaussian 1 (3 * (3 / 20 - μ)) :=
    mul_le_mul ha₁ ht (by norm_num) (by linarith)
  have hpu : a₀ * halfGaussian 1 (-3 * μ) ≤ (37 / 200 : ℝ) * (109 / 100) :=
    (mul_le_mul_of_nonneg_left hp ha₀).trans (mul_le_mul_of_nonneg_right ha₀u (by norm_num))
  linarith

/-- The strict Gaussian surplus holds for the repository's already
defined exact phase family, without fitting a new coefficient row. -/
theorem exact_profile_surplus {μ : ℝ} (hμ0 : 1 / 10 ≤ μ) (hμ1 : μ ≤ 21 / 200) :
    phaseContactExactCoefficients 0 * halfGaussian 1 (-3 * μ) +
      (∑ j : Fin 9, if j = 0 then 0 else phaseContactExactCoefficients j) / 12 + 1 / 400 ≤
        phaseContactExactCoefficients 1 * halfGaussian 1 (3 * (3 / 20 - μ)) :=
  profile_surplus (phaseContactExactCoefficients_pos 0).le exact_constant_upper
    exact_first_lower exact_nonconstant_mass_upper hμ0 hμ1

/-- Exact scaling makes the surplus proportional to the logarithmic
height parameter, uniformly over every smaller target edge distance. -/
theorem scaled_profile_surplus {a₀ a₁ M L m d : ℝ} (ha₀ : 0 ≤ a₀)
    (ha₀u : a₀ ≤ 37 / 200) (ha₁ : 79 / 250 ≤ a₁) (hM : M ≤ 61 / 100)
    (hL : 0 < L) (hm0 : 1 / 10 ≤ L * m) (hm1 : L * m ≤ 21 / 200)
    (hd : d ≤ 3 / (20 * L)) :
    a₀ * halfGaussian (1 / (9 * L ^ 2)) (-m) + M * L / 4 + 3 * L / 400 ≤
      a₁ * halfGaussian (1 / (9 * L ^ 2)) (d - m) := by
  let r := 1 / (3 * L)
  have hr : 0 < r := by dsimp [r]; positivity
  have hB : 1 * r ^ 2 = 1 / (9 * L ^ 2) := by dsimp [r]; field_simp; ring
  have hp : -3 * (L * m) * r = -m := by dsimp [r]; field_simp
  have ht : 3 * (3 / 20 - L * m) * r = 3 / (20 * L) - m := by
    dsimp [r]
    field_simp
  have ep : halfGaussian (1 / (9 * L ^ 2)) (-m) =
      3 * L * halfGaussian 1 (-3 * (L * m)) := by
    apply mul_left_cancel₀ hr.ne'
    rw [← hB, ← hp, halfGaussian_scale hr]
    dsimp [r]
    field_simp
  have et : halfGaussian (1 / (9 * L ^ 2)) (3 / (20 * L) - m) =
      3 * L * halfGaussian 1 (3 * (3 / 20 - L * m)) := by
    apply mul_left_cancel₀ hr.ne'
    rw [← hB, ← ht, halfGaussian_scale hr]
    dsimp [r]
    field_simp
  calc
    _ = (3 * L) * (a₀ * halfGaussian 1 (-3 * (L * m)) + M / 12 + 1 / 400) := by
      rw [ep]
      ring
    _ ≤ (3 * L) * (a₁ * halfGaussian 1 (3 * (3 / 20 - L * m))) :=
      mul_le_mul_of_nonneg_left (profile_surplus ha₀ ha₀u ha₁ hM hm0 hm1) (by positivity)
    _ = a₁ * halfGaussian (1 / (9 * L ^ 2)) (3 / (20 * L) - m) := by rw [et]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact halfGaussian_antitone (by positivity) (by linarith)

/-- The scaled strict surplus for the actual exact coefficient row. -/
theorem exact_scaled_profile_surplus {L m d : ℝ} (hL : 0 < L)
    (hm0 : 1 / 10 ≤ L * m) (hm1 : L * m ≤ 21 / 200) (hd : d ≤ 3 / (20 * L)) :
    phaseContactExactCoefficients 0 * halfGaussian (1 / (9 * L ^ 2)) (-m) +
      (∑ j : Fin 9, if j = 0 then 0 else phaseContactExactCoefficients j) * L / 4 +
        3 * L / 400 ≤
          phaseContactExactCoefficients 1 * halfGaussian (1 / (9 * L ^ 2)) (d - m) :=
  scaled_profile_surplus (phaseContactExactCoefficients_pos 0).le exact_constant_upper
    exact_first_lower exact_nonconstant_mass_upper hL hm0 hm1 hd

end
end RiemannGaussian.GaussianFermiProfileSurplus
