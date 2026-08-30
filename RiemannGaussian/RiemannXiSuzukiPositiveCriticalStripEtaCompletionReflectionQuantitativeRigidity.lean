import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaCompletionReflectionLeadingCoefficientRigidity

/-!
# Quantitative high-ordinate eta reflection rigidity

The qualitative reflection theorem identifies the critical line as the exact
unit-norm locus of the eta multiplier.  This module extracts an explicit
coercive estimate from the high-ordinate part of that proof.

For absolute ordinate at least `8`, the horizontal derivative of the
multiplier log norm is bounded below by `1 / 200` throughout the open strip.
The mean-value theorem then bounds horizontal displacement from the critical
line by the logarithmic gain between the first nonzero localized Gaussian
coefficients at complementary zeros.

This is a quantitative stability statement, not a proof that the gain
vanishes.  An independent arithmetic or phase estimate is still needed to
force equality of the two coefficients.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

private theorem log_pi_lt_229_over_200_reflection :
    Real.log Real.pi < 229 / 200 := by
  have hexponential :=
    Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 229 / 200) 8
  have hpiExp : Real.pi < Real.exp (229 / 200) := by
    calc
      Real.pi < 3.1416 := Real.pi_lt_d4
      _ < ∑ i ∈ Finset.range 8,
          (229 / 200 : ℝ) ^ i / i.factorial := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp (229 / 200) := hexponential
  exact (Real.log_lt_iff_lt_exp Real.pi_pos).2 hpiExp

/-- At absolute ordinate at least `8`, the explicit horizontal logarithmic
slope exceeds the uniform rational constant `1 / 200`. -/
theorem one_over_200_lt_pairedEtaLaplaceReflectionDyadicLogSlope_re_of_eight_le_abs_im
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1)
    (hy : 8 ≤ |s.im|) :
    1 / 200 < (pairedEtaLaplaceReflectionDyadicLogSlope s).re := by
  let a₁ : ℝ := 1 + s.re / 2
  let b₁ : ℝ := s.im / 2
  let a₂ : ℝ := 1 + (1 - s.re) / 2
  let b₂ : ℝ := -s.im / 2
  have ha₁one : 1 ≤ a₁ := by dsimp [a₁]; linarith
  have ha₁upper : a₁ ≤ 3 / 2 := by dsimp [a₁]; linarith
  have ha₂one : 1 ≤ a₂ := by dsimp [a₂]; linarith
  have ha₂upper : a₂ ≤ 3 / 2 := by dsimp [a₂]; linarith
  have hb₁ : 4 ≤ |b₁| := by
    dsimp [b₁]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hb₂ : 4 ≤ |b₂| := by
    dsimp [b₂]
    rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have harg₁ :
      1 + s / 2 = (a₁ : ℂ) + (b₁ : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [a₁, b₁]
  have harg₂ :
      1 + (1 - s) / 2 = (a₂ : ℂ) + (b₂ : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [a₂, b₂]
  have hdigamma₁ :=
    re_digamma_gt_23_over_50_of_four_le_abs_im
      ha₁one ha₁upper hb₁
  have hdigamma₂ :=
    re_digamma_gt_23_over_50_of_four_le_abs_im
      ha₂one ha₂upper hb₂
  rw [← harg₁] at hdigamma₁
  rw [← harg₂] at hdigamma₂
  have hdyadic₁ :=
    re_log_two_div_one_sub_gt_half_log_two_of_norm_lt_one
      (norm_two_cpow_sub_one_lt_one hslt)
  have hdyadic₂ :=
    re_log_two_div_one_sub_gt_half_log_two_of_norm_lt_one
      (norm_two_cpow_neg_lt_one hspos)
  have hlogPi := log_pi_lt_229_over_200_reflection
  have hlogTwo := Real.log_two_gt_d9
  have havg :
      ((Complex.digamma (1 + s / 2) +
          Complex.digamma (1 + (1 - s) / 2)) / 2).re =
        ((Complex.digamma (1 + s / 2)).re +
          (Complex.digamma (1 + (1 - s) / 2)).re) / 2 := by
    rw [Complex.div_re]
    norm_num
    ring
  rw [show (pairedEtaLaplaceReflectionDyadicLogSlope s).re =
      -Real.log Real.pi +
        ((Complex.digamma (1 + s / 2)).re +
          (Complex.digamma (1 + (1 - s) / 2)).re) / 2 +
        (Complex.log 2 / (1 - (2 : ℂ) ^ (s - 1))).re +
        (Complex.log 2 / (1 - (2 : ℂ) ^ (-s))).re by
    unfold pairedEtaLaplaceReflectionDyadicLogSlope
    simp only [Complex.add_re, Complex.neg_re, Complex.log_ofReal_re]
    rw [havg]
  ]
  norm_num at hdigamma₁ hdigamma₂ hdyadic₁ hdyadic₂ ⊢
  nlinarith

/-- At high ordinate, the multiplier log norm grows by more than
`(sigma₂ - sigma₁) / 200` between any two horizontal coordinates in the open
critical strip. -/
theorem pairedEtaLaplaceReflectionLogNorm_sub_gt_one_over_200_mul_sub_of_eight_le_abs
    {sigma₁ sigma₂ y : ℝ}
    (hsigma₁pos : 0 < sigma₁) (hsigma₂lt : sigma₂ < 1)
    (hsigma : sigma₁ < sigma₂) (hy : 8 ≤ |y|) :
    (1 / 200) * (sigma₂ - sigma₁) <
      pairedEtaLaplaceReflectionLogNorm sigma₂ y -
        pairedEtaLaplaceReflectionLogNorm sigma₁ y := by
  let f : ℝ → ℝ := fun sigma =>
    pairedEtaLaplaceReflectionLogNorm sigma y
  have hcontinuous : ContinuousOn f (Ioo (0 : ℝ) 1) := by
    intro sigma hsigmaOpen
    exact (hasDerivAt_pairedEtaLaplaceReflectionLogNorm_dyadic
      hsigmaOpen.1 hsigmaOpen.2).continuousAt.continuousWithinAt
  have hdifferentiable :
      DifferentiableOn ℝ f (interior (Ioo (0 : ℝ) 1)) := by
    intro sigma hsigmaInterior
    have hsigmaOpen : sigma ∈ Ioo (0 : ℝ) 1 :=
      interior_subset hsigmaInterior
    exact (hasDerivAt_pairedEtaLaplaceReflectionLogNorm_dyadic
      hsigmaOpen.1 hsigmaOpen.2).differentiableAt.differentiableWithinAt
  have hderiv : ∀ sigma ∈ interior (Ioo (0 : ℝ) 1),
      (1 / 200 : ℝ) < deriv f sigma := by
    intro sigma hsigmaInterior
    have hsigmaOpen : sigma ∈ Ioo (0 : ℝ) 1 :=
      interior_subset hsigmaInterior
    rw [deriv_pairedEtaLaplaceReflectionLogNorm_eq_dyadicLogSlope_re
      hsigmaOpen.1 hsigmaOpen.2]
    apply
      one_over_200_lt_pairedEtaLaplaceReflectionDyadicLogSlope_re_of_eight_le_abs_im
    · simpa [Complex.mul_re] using hsigmaOpen.1
    · simpa [Complex.mul_re] using hsigmaOpen.2
    · simpa [Complex.mul_im] using hy
  exact (convex_Ioo (0 : ℝ) 1).mul_sub_lt_image_sub_of_lt_deriv
    hcontinuous hdifferentiable hderiv sigma₁
    ⟨hsigma₁pos, hsigma.trans hsigma₂lt⟩ sigma₂
    ⟨hsigma₁pos.trans hsigma, hsigma₂lt⟩ hsigma

/-- To the right of the critical line at high ordinate, the multiplier log
norm is bounded below linearly by the horizontal displacement. -/
theorem one_over_200_mul_sub_half_lt_pairedEtaLaplaceReflectionLogNorm_of_eight_le_abs
    {sigma y : ℝ} (hhalf : 1 / 2 < sigma) (hslt : sigma < 1)
    (hy : 8 ≤ |y|) :
    (1 / 200) * (sigma - 1 / 2) <
      pairedEtaLaplaceReflectionLogNorm sigma y := by
  have h :=
    pairedEtaLaplaceReflectionLogNorm_sub_gt_one_over_200_mul_sub_of_eight_le_abs
      (sigma₁ := (1 / 2 : ℝ)) (sigma₂ := sigma)
      (by norm_num) hslt hhalf hy
  rw [pairedEtaLaplaceReflectionLogNorm_half] at h
  simpa using h

/-- To the left of the critical line at high ordinate, the negative
multiplier log norm is bounded below linearly by the horizontal displacement. -/
theorem one_over_200_mul_half_sub_lt_neg_pairedEtaLaplaceReflectionLogNorm_of_eight_le_abs
    {sigma y : ℝ} (hspos : 0 < sigma) (hhalf : sigma < 1 / 2)
    (hy : 8 ≤ |y|) :
    (1 / 200) * (1 / 2 - sigma) <
      -pairedEtaLaplaceReflectionLogNorm sigma y := by
  have h :=
    pairedEtaLaplaceReflectionLogNorm_sub_gt_one_over_200_mul_sub_of_eight_le_abs
      (sigma₁ := sigma) (sigma₂ := (1 / 2 : ℝ))
      hspos (by norm_num) hhalf hy
  rw [pairedEtaLaplaceReflectionLogNorm_half] at h
  simpa using h

/-- The real logarithm of the complementary leading-coefficient ratio is
twice the same-ordinate eta multiplier log norm. -/
theorem realLog_pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_eq_two_mul_reflectionLogNorm
    (rho : NontrivialZetaZero) :
    Real.log
        (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
              (NontrivialZetaZero.conjugatePartner rho) /
            pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho) =
      2 * pairedEtaLaplaceReflectionLogNorm rho.1.re rho.1.im := by
  rw [pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_eq_reflectionMultiplier_normSq,
    Complex.normSq_eq_norm_sq, Real.log_pow]
  unfold pairedEtaLaplaceReflectionLogNorm
  rw [Complex.re_add_im]
  norm_num

/-- At a high-ordinate nontrivial zero, the absolute logarithmic gain between
the two positive leading coefficients controls horizontal distance from the
critical line with the explicit constant `1 / 100`. -/
theorem one_over_100_mul_abs_re_sub_half_le_abs_realLog_leadingCoefficient_ratio_of_eight_le_abs_im
    (rho : NontrivialZetaZero) (hy : 8 ≤ |rho.1.im|) :
    (1 / 100) * |rho.1.re - 1 / 2| ≤
      |Real.log
        (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
              (NontrivialZetaZero.conjugatePartner rho) /
            pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho)| := by
  rw [
    realLog_pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_eq_two_mul_reflectionLogNorm]
  rcases lt_trichotomy rho.1.re (1 / 2) with hleft | hline | hright
  · have hbound :=
      one_over_200_mul_half_sub_lt_neg_pairedEtaLaplaceReflectionLogNorm_of_eight_le_abs
        (NontrivialZetaZero.zero_lt_re rho) hleft hy
    rw [abs_of_nonpos (by linarith : rho.1.re - 1 / 2 ≤ 0),
      abs_of_nonpos (by linarith :
        2 * pairedEtaLaplaceReflectionLogNorm rho.1.re rho.1.im ≤ 0)]
    nlinarith
  · rw [hline, pairedEtaLaplaceReflectionLogNorm_half]
    norm_num
  · have hbound :=
      one_over_200_mul_sub_half_lt_pairedEtaLaplaceReflectionLogNorm_of_eight_le_abs
        hright (NontrivialZetaZero.re_lt_one rho) hy
    rw [abs_of_nonneg (by linarith : 0 ≤ rho.1.re - 1 / 2),
      abs_of_nonneg (by linarith :
        0 ≤ 2 * pairedEtaLaplaceReflectionLogNorm rho.1.re rho.1.im)]
    nlinarith

end
end RiemannGaussian
