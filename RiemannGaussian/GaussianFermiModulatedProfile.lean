/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianModulatedLaplaceEnclosure
import RiemannGaussian.GaussianFermiProfileSurplus

/-!
# A uniform source surplus for the positive modulated Gaussian

Exact Laplace enclosures give a surplus for the entire established coarse
phase-coefficient class at target `24/125`. The original phase
row satisfies that class. Dilation transports the surplus to the actual
logarithmic scale, retaining the coupled modulation. Zero exclusion is proved
downstream using the shifted pole, gamma and complete outside-divisor costs.
-/

namespace RiemannGaussian.GaussianFermiModulatedProfile
noncomputable section
open GaussianModulatedLaplace GaussianModulatedLaplaceEnclosure GaussianFermiProfileSurplus

/-- The complete coarse coefficient class has a uniform strict modulated surplus. -/
theorem profile_surplus {a₀ a₁ M μ : ℝ} (ha₀ : 0 ≤ a₀)
    (ha₀u : a₀ ≤ 37 / 200) (ha₁ : 79 / 250 ≤ a₁) (hM : M ≤ 61 / 100)
    (hμ0 : 937 / 5000 ≤ μ) (hμ1 : μ ≤ 3 / 16) :
    a₀ * halfModulated 1 (3 / 2) (-3 * μ) + M / 12 + 1 / 20000 ≤
      a₁ * halfModulated 1 (3 / 2) (3 * (24 / 125 - μ)) := by
  have ht : (6911 / 10000 : ℝ) ≤ halfModulated 1 (3 / 2) (3 * (24 / 125 - μ)) := by
    apply halfModulated_source_lower.trans
    exact halfModulated_antitone (by norm_num) _ (by linarith)
  have hp : halfModulated 1 (3 / 2) (-3 * μ) ≤ (2263 / 2500 : ℝ) := by
    apply (halfModulated_antitone (by norm_num) _
      (show -(9 / 16 : ℝ) ≤ -3 * μ by linarith)).trans
    exact halfModulated_pole_upper
  have hs : (79 / 250 : ℝ) * (6911 / 10000) ≤
      a₁ * halfModulated 1 (3 / 2) (3 * (24 / 125 - μ)) :=
    mul_le_mul ha₁ ht (by norm_num) (by linarith)
  have hpu : a₀ * halfModulated 1 (3 / 2) (-3 * μ) ≤ (37 / 200 : ℝ) * (2263 / 2500) :=
    (mul_le_mul_of_nonneg_left hp ha₀).trans (mul_le_mul_of_nonneg_right ha₀u (by norm_num))
  linarith

/-- The coupled dilation gives a logarithmically growing margin at every
edge distance up to the proposed target. -/
theorem scaled_profile_surplus {a₀ a₁ M L m d : ℝ} (ha₀ : 0 ≤ a₀)
    (ha₀u : a₀ ≤ 37 / 200) (ha₁ : 79 / 250 ≤ a₁) (hM : M ≤ 61 / 100)
    (hL : 0 < L) (hm0 : 937 / 5000 ≤ L * m) (hm1 : L * m ≤ 3 / 16)
    (hd : d ≤ 24 / (125 * L)) :
    a₀ * halfModulated (1 / (9 * L ^ 2)) (1 / (2 * L)) (-m) + M * L / 4 + 3 * L / 20000 ≤
      a₁ * halfModulated (1 / (9 * L ^ 2)) (1 / (2 * L)) (d - m) := by
  let r := 1 / (3 * L)
  have hr : 0 < r := by dsimp [r]; positivity
  have hB : 1 * r ^ 2 = 1 / (9 * L ^ 2) := by dsimp [r]; field_simp; ring
  have hδ : (3 / 2 : ℝ) * r = 1 / (2 * L) := by dsimp [r]; field_simp
  have hp : -3 * (L * m) * r = -m := by dsimp [r]; field_simp
  have ht : 3 * (24 / 125 - L * m) * r = 24 / (125 * L) - m := by dsimp [r]; field_simp
  have ep : halfModulated (1 / (9 * L ^ 2)) (1 / (2 * L)) (-m) =
      3 * L * halfModulated 1 (3 / 2) (-3 * (L * m)) := by
    apply mul_left_cancel₀ hr.ne'
    rw [← hB, ← hδ, ← hp, halfModulated_scale hr]
    dsimp [r]
    field_simp
  have et : halfModulated (1 / (9 * L ^ 2)) (1 / (2 * L)) (24 / (125 * L) - m) =
      3 * L * halfModulated 1 (3 / 2) (3 * (24 / 125 - L * m)) := by
    apply mul_left_cancel₀ hr.ne'
    rw [← hB, ← hδ, ← ht, halfModulated_scale hr]
    dsimp [r]
    field_simp
  calc
    _ = (3 * L) *
        (a₀ * halfModulated 1 (3 / 2) (-3 * (L * m)) + M / 12 + 1 / 20000) := by rw [ep]; ring
    _ ≤ (3 * L) * (a₁ * halfModulated 1 (3 / 2) (3 * (24 / 125 - L * m))) :=
      mul_le_mul_of_nonneg_left (profile_surplus ha₀ ha₀u ha₁ hM hm0 hm1) (by positivity)
    _ = a₁ * halfModulated (1 / (9 * L ^ 2)) (1 / (2 * L)) (24 / (125 * L) - m) := by rw [et]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (halfModulated_antitone (by positivity) _ (by linarith)) (by linarith)

/-- The existing phase row satisfies the comparison without changing its coefficients. -/
theorem exact_scaled_profile_surplus {L m d : ℝ} (hL : 0 < L)
    (hm0 : 937 / 5000 ≤ L * m) (hm1 : L * m ≤ 3 / 16) (hd : d ≤ 24 / (125 * L)) :
    phaseContactExactCoefficients 0 * halfModulated (1 / (9 * L ^ 2)) (1 / (2 * L)) (-m) +
      (∑ j : Fin 9, if j = 0 then 0 else phaseContactExactCoefficients j) * L / 4 + 3 * L / 20000 ≤
        phaseContactExactCoefficients 1 * halfModulated (1 / (9 * L ^ 2)) (1 / (2 * L)) (d - m) :=
  scaled_profile_surplus (phaseContactExactCoefficients_pos 0).le exact_constant_upper
    exact_first_lower exact_nonconstant_mass_upper hL hm0 hm1 hd

/-- The actual proved common margin falls in the required normalized interval. -/
theorem normalized_margin_bounds {t : ℝ} (ht : 0 < t) (hlog : 100000 ≤ Real.log t) :
    937 / 5000 ≤ Real.log t * (3 / (16 * Real.log (50 * t))) ∧
      Real.log t * (3 / (16 * Real.log (50 * t))) ≤ 3 / 16 := by
  have h50 : 0 ≤ Real.log (50 : ℝ) := Real.log_nonneg (by norm_num)
  have h50u : Real.log (50 : ℝ) ≤ 49 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 50)]
  have hS : Real.log (50 * t) = Real.log 50 + Real.log t := Real.log_mul (by norm_num) ht.ne'
  have hSp : 0 < Real.log (50 * t) := by rw [hS]; linarith
  rw [← mul_div_assoc]
  constructor
  · apply (le_div_iff₀ (by positivity)).mpr
    rw [hS]
    linarith
  · apply (div_le_iff₀ (by positivity)).mpr
    rw [hS]
    linarith

/-- The same Gaussian width is admissible throughout the larger normalized margin range. -/
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

end
end RiemannGaussian.GaussianFermiModulatedProfile
