/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiGammaShift
import RiemannGaussian.SuzukiCarrierNormalizedMass

/-!
# Signed Gamma curvature in the full normalized Suzuki source

The shifted representation is transported to the literal smooth xi source.
The completion term has a favorable imaginary sign for real nonnegative
weights, and its complex size has a uniform bound retaining the actual
normalization. General complex reflection weights retain their phase cost.
-/

open Complex Filter Set Topology
namespace RiemannGaussian
noncomputable section

/-- The complete real denominator of the shifted homogeneous smoothing. -/
def suzukiGammaShiftNormDenominator (r : ℝ) (s : ℂ) : ℝ :=
  normSq (suzukiGammaShiftDenominator s) + r ^ 2 * normSq (suzukiGammaShiftNumerator s)

/-- The real normalized mass in the shifted representation. -/
def suzukiGammaShiftNormalizedMass (r : ℝ) (s : ℂ) : ℝ :=
  normSq (suzukiGammaShiftNumerator s) / suzukiGammaShiftNormDenominator r s

/-- The shifted mass is nonnegative, including all common zeros. -/
theorem suzukiGammaShiftNormalizedMass_nonneg (r : ℝ) (s : ℂ) :
    0 ≤ suzukiGammaShiftNormalizedMass r s := by
  unfold suzukiGammaShiftNormalizedMass suzukiGammaShiftNormDenominator
  exact div_nonneg (normSq_nonneg _) (add_nonneg (normSq_nonneg _)
    (mul_nonneg (sq_nonneg _) (normSq_nonneg _)))

/-- The full variable normalization bounds the mass without imposing
any lower bound on either the numerator or denominator separately. -/
theorem suzukiGammaShiftNormalizedMass_le {r : ℝ} (hr : 0 < r) (s : ℂ) :
    suzukiGammaShiftNormalizedMass r s ≤ 1 / r ^ 2 := by
  by_cases hF : suzukiGammaShiftNumerator s = 0
  · simp [suzukiGammaShiftNormalizedMass, hF]
    positivity
  have hp := complexSmoothQuotient_denominator_pos hr
    (b := suzukiGammaShiftDenominator s) (Or.inl hF)
  apply (div_le_div_iff₀ hp (sq_pos_of_pos hr)).mpr
  nlinarith [normSq_nonneg (suzukiGammaShiftDenominator s)]

/-- The literal shifted smooth carrier, defined through common zeros. -/
def suzukiGammaShiftSmoothCarrier (r : ℝ) (s : ℂ) : ℂ :=
  complexSmoothQuotient r (I * suzukiGammaShiftNumerator s) (suzukiGammaShiftDenominator s)

/-- The full shifted Wronskian source retains the spectral Jacobian i. -/
def suzukiGammaShiftSpectralSource (r : ℝ) (s : ℂ) : ℂ :=
  2 * I * (r : ℂ) ^ 2 * suzukiGammaShiftNumerator s ^ 2 *
    starRingEnd ℂ (deriv suzukiGammaShiftNumerator s * suzukiGammaShiftDenominator s -
      suzukiGammaShiftNumerator s * deriv suzukiGammaShiftDenominator s) /
    (suzukiGammaShiftNormDenominator r s : ℂ) ^ 2

/-- The arithmetic curvature contribution with the same full variable
denominator as the actual source. -/
def suzukiGammaShiftArithmeticSource (r : ℝ) (s : ℂ) : ℂ :=
  2 * I * (r : ℂ) ^ 2 * suzukiGammaShiftNumerator s ^ 2 *
    starRingEnd ℂ (deriv suzukiGammaShiftNumerator s ^ 2 -
      suzukiGammaShiftNumerator s * deriv (deriv suzukiGammaShiftNumerator) s) /
    (suzukiGammaShiftNormDenominator r s : ℂ) ^ 2

/-- The actual completion curvature, still complex and carrying its
full normalization. Its sign is derived downstream. -/
def suzukiGammaShiftCompletionSource (r : ℝ) (s : ℂ) : ℂ :=
  -2 * I * (r : ℂ) ^ 2 * ((normSq (suzukiGammaShiftNumerator s) : ℂ) ^ 2) *
    starRingEnd ℂ (deriv suzukiGammaShiftCorrection s) /
    (suzukiGammaShiftNormDenominator r s : ℂ) ^ 2

private lemma spectral_factor {z : ℂ} (hz : 0 < (suzukiArithmeticZetaArgument z).re) :
    riemannXiSpectral z = suzukiGammaShiftFactor (suzukiArithmeticZetaArgument z) *
      suzukiGammaShiftNumerator (suzukiArithmeticZetaArgument z) := by
  rw [suzukiGammaShiftFactor_mul_numerator hz,
    suzukiArithmeticZetaArgument_eq_one_sub_completedSpectralCoordinate, riemannXi_one_sub]
  rfl

/-- The shifted normalization is exactly the globally smooth actual xi
mass, including the central value at every repeated zero. -/
theorem suzukiXiNormalizedMass_eq_gammaShift (r : ℝ) {z : ℂ}
    (hz : 0 < (suzukiArithmeticZetaArgument z).re) :
    suzukiXiNormalizedMass r z =
      suzukiGammaShiftNormalizedMass r (suzukiArithmeticZetaArgument z) := by
  change normSq (riemannXiSpectral z) /
    (normSq (suzukiXiEValue z) + r ^ 2 * normSq (riemannXiSpectral z)) = _
  rw [spectral_factor hz, suzukiXiEValue_eq_gammaShift hz]
  simp only [map_mul]
  rw [show normSq (suzukiGammaShiftFactor (suzukiArithmeticZetaArgument z)) *
      normSq (suzukiGammaShiftDenominator (suzukiArithmeticZetaArgument z)) + r ^ 2 *
      (normSq (suzukiGammaShiftFactor (suzukiArithmeticZetaArgument z)) *
        normSq (suzukiGammaShiftNumerator (suzukiArithmeticZetaArgument z))) =
      normSq (suzukiGammaShiftFactor (suzukiArithmeticZetaArgument z)) *
        suzukiGammaShiftNormDenominator r (suzukiArithmeticZetaArgument z) by
    unfold suzukiGammaShiftNormDenominator
    ring]
  exact mul_div_mul_left _ _ (normSq_pos.mpr (suzukiGammaShiftFactor_ne_zero hz)).ne'

/-- The full actual smooth carrier is invariant under the shifted
factorization, including genuine carrier poles and repeated xi zeros. -/
theorem suzukiXiSmoothCarrier_eq_gammaShift (r : ℝ) {z : ℂ}
    (hz : 0 < (suzukiArithmeticZetaArgument z).re) :
    suzukiXiSmoothCarrier r z = suzukiGammaShiftSmoothCarrier r (suzukiArithmeticZetaArgument z) := by
  rw [suzukiXiSmoothCarrier, spectral_factor hz, suzukiXiEValue_eq_gammaShift hz]
  rw [show I * (suzukiGammaShiftFactor (suzukiArithmeticZetaArgument z) *
      suzukiGammaShiftNumerator (suzukiArithmeticZetaArgument z)) =
      suzukiGammaShiftFactor (suzukiArithmeticZetaArgument z) *
        (I * suzukiGammaShiftNumerator (suzukiArithmeticZetaArgument z)) by ring]
  exact complexSmoothQuotient_mul r _ _ (suzukiGammaShiftFactor_ne_zero hz)

private lemma argument_derivative (z : ℂ) :
    HasDerivAt suzukiArithmeticZetaArgument (-I) z := by
  unfold suzukiArithmeticZetaArgument
  simpa only [mul_one, zero_mul, zero_add, zero_sub, id_eq] using
    (hasDerivAt_const z (1/2 : ℂ)).fun_sub ((hasDerivAt_const z I).fun_mul (hasDerivAt_id z))

/-- The literal xi source equals the shifted arithmetic Wronskian on
the whole positive half-plane, with no denominator-zero exception. -/
theorem suzukiXiSmoothCarrierSource_eq_gammaShift {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : 0 < (suzukiArithmeticZetaArgument z).re) :
    suzukiXiSmoothCarrierSource r z = suzukiGammaShiftSpectralSource r (suzukiArithmeticZetaArgument z) := by
  let s := suzukiArithmeticZetaArgument z
  change suzukiXiSmoothCarrierSource r z = suzukiGammaShiftSpectralSource r s
  by_cases hF : suzukiGammaShiftNumerator s = 0
  · have hA : riemannXiSpectral z = 0 :=
      (spectral_factor hz).trans (mul_eq_zero_of_right _ hF)
    simp [suzukiXiSmoothCarrierSource, suzukiGammaShiftSpectralSource, hA, hF]
  · have hf : HasDerivAt (fun w => I * suzukiGammaShiftNumerator (suzukiArithmeticZetaArgument w))
        (I * (deriv suzukiGammaShiftNumerator s * -I)) z := by
      simpa only [Function.comp_def] using
        (((analyticAt_suzukiGammaShiftNumerator hz).differentiableAt.hasDerivAt.comp z
          (argument_derivative z)).const_mul I)
    have hg : HasDerivAt (fun w => suzukiGammaShiftDenominator (suzukiArithmeticZetaArgument w))
        (deriv suzukiGammaShiftDenominator s * -I) z :=
      (analyticAt_suzukiGammaShiftDenominator hz).differentiableAt.hasDerivAt.comp z
        (argument_derivative z)
    have hnear : suzukiXiSmoothCarrier r =ᶠ[𝓝 z] fun w =>
        suzukiGammaShiftSmoothCarrier r (suzukiArithmeticZetaArgument w) := by
      filter_upwards [(argument_derivative z).continuousAt.preimage_mem_nhds
        ((Complex.isOpen_re_gt 0).mem_nhds hz)] with w hw
      exact suzukiXiSmoothCarrier_eq_gammaShift r hw
    have hCG : complexCauchyGreenSource (suzukiXiSmoothCarrier r) z =
        complexCauchyGreenSource (fun w =>
          suzukiGammaShiftSmoothCarrier r (suzukiArithmeticZetaArgument w)) z := by
      unfold complexCauchyGreenSource
      rw [hnear.fderiv_eq]
    rw [← complexCauchyGreenSource_suzukiXiSmoothCarrier hr, hCG]
    unfold suzukiGammaShiftSmoothCarrier
    rw [complexCauchyGreenSource_complexSmoothQuotient hr hf.differentiableAt hg.differentiableAt
      (Or.inl (mul_ne_zero I_ne_zero hF)), hf.deriv, hg.deriv]
    unfold suzukiGammaShiftSpectralSource suzukiGammaShiftNormDenominator
    dsimp only [s]
    simp only [map_mul, map_sub, map_neg, conj_I, normSq_I, one_mul]
    congr 1
    ring_nf
    simp

/-- The first completion derivative cancels exactly from the shifted
Wronskian. The remaining trigamma curvature is retained with its sign. -/
theorem suzukiGammaShift_wronskian {s : ℂ} (hs : 0 < s.re) :
    deriv suzukiGammaShiftNumerator s * suzukiGammaShiftDenominator s -
      suzukiGammaShiftNumerator s * deriv suzukiGammaShiftDenominator s =
    deriv suzukiGammaShiftNumerator s ^ 2 -
      suzukiGammaShiftNumerator s * deriv (deriv suzukiGammaShiftNumerator) s -
      deriv suzukiGammaShiftCorrection s * suzukiGammaShiftNumerator s ^ 2 := by
  have hF := analyticAt_suzukiGammaShiftNumerator hs
  have hQ := analyticAt_suzukiGammaShiftCorrection hs
  have hd := (hF.deriv.differentiableAt.hasDerivAt.add
    ((hQ.differentiableAt.hasDerivAt.const_add 1).mul hF.differentiableAt.hasDerivAt)).deriv
  change deriv suzukiGammaShiftDenominator s = _ at hd
  rw [hd, suzukiGammaShiftDenominator]
  ring

/-- Exact separation of arithmetic and completion contributions with
their shared variable denominator unchanged. -/
theorem suzukiGammaShiftSpectralSource_eq_add {s : ℂ} (hs : 0 < s.re) (r : ℝ) :
    suzukiGammaShiftSpectralSource r s =
      suzukiGammaShiftArithmeticSource r s + suzukiGammaShiftCompletionSource r s := by
  unfold suzukiGammaShiftSpectralSource suzukiGammaShiftArithmeticSource suzukiGammaShiftCompletionSource
  rw [suzukiGammaShift_wronskian hs, ← mul_conj (suzukiGammaShiftNumerator s)]
  simp only [map_sub, map_mul, map_pow]
  ring

/-- The normalized completion contribution is nonpositive in the
source's imaginary channel throughout the positive half-plane. -/
theorem suzukiGammaShiftCompletionSource_im_nonpos (r : ℝ) {s : ℂ} (hs : 0 < s.re) :
    (suzukiGammaShiftCompletionSource r s).im ≤ 0 := by
  have hq := (suzukiGammaShiftCorrection_deriv_re_pos hs).le
  unfold suzukiGammaShiftCompletionSource
  rw [← ofReal_pow, ← ofReal_pow, ← ofReal_pow, Complex.div_ofReal_im]
  simp only [mul_im, mul_re, ofReal_re, ofReal_im, conj_re, conj_im,
    I_re, I_im, neg_re, neg_im, re_ofNat, im_ofNat, mul_zero,
    sub_zero, zero_sub, add_zero, zero_add]
  apply div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
  have hp : 0 ≤ r ^ 2 * normSq (suzukiGammaShiftNumerator s) ^ 2 *
      (deriv suzukiGammaShiftCorrection s).re :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hq
  nlinarith

/-- The exact completion term depends on the square of the normalized
mass. This identity preserves its complex phase. -/
theorem suzukiGammaShiftCompletionSource_eq_mass (r : ℝ) (s : ℂ) :
    suzukiGammaShiftCompletionSource r s = -2 * I * (r : ℂ) ^ 2 *
      (suzukiGammaShiftNormalizedMass r s : ℂ) ^ 2 *
      starRingEnd ℂ (deriv suzukiGammaShiftCorrection s) := by
  unfold suzukiGammaShiftCompletionSource suzukiGammaShiftNormalizedMass
  rw [ofReal_div, div_pow]
  ring

/-- The full complex completion contribution is uniformly at most
`1/(4*r^2)` throughout the positive half-plane, at every imaginary height.
The actual normalization, genuine carrier poles and common zeros are included. -/
theorem norm_suzukiGammaShiftCompletionSource_le {r : ℝ} (hr : 0 < r) {s : ℂ}
    (hs : 0 < s.re) : ‖suzukiGammaShiftCompletionSource r s‖ ≤ 1 / (4 * r ^ 2) := by
  rw [suzukiGammaShiftCompletionSource_eq_mass]
  simp only [norm_mul, norm_neg, norm_pow, norm_conj, norm_I, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_one]
  calc
    _ ≤ 2 * r ^ 2 * (1 / r ^ 2) ^ 2 * (1 / 8) := by
      gcongr
      · exact suzukiGammaShiftNormalizedMass_nonneg r s
      · exact suzukiGammaShiftNormalizedMass_le hr s
      · exact norm_deriv_suzukiGammaShiftCorrection_le hs
    _ = _ := by field_simp; ring

/-- An independent one-sided bound for the full actual xi source:
its shifted completion curvature can only lower the imaginary part.
The complete variable denominator remains inside the arithmetic term. -/
theorem suzukiXiSmoothCarrierSource_im_le_gammaShiftArithmetic {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : 0 < (suzukiArithmeticZetaArgument z).re) :
    (suzukiXiSmoothCarrierSource r z).im ≤
      (suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z)).im := by
  rw [suzukiXiSmoothCarrierSource_eq_gammaShift hr hz, suzukiGammaShiftSpectralSource_eq_add hz,
    add_im]
  exact add_le_of_nonpos_right (suzukiGammaShiftCompletionSource_im_nonpos r hz)

/-- An independent bound for the complete complex discrepancy between
the actual xi source and its normalized arithmetic part. Arbitrary complex
weights stay inside the identity and pay their literal pointwise norm. -/
theorem norm_suzukiXiSmoothCarrierSource_gammaShift_error_le {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : 0 < (suzukiArithmeticZetaArgument z).re) (P : ℂ) :
    ‖P * (suzukiXiSmoothCarrierSource r z -
      suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z))‖ ≤
      ‖P‖ / (4 * r ^ 2) := by
  rw [suzukiXiSmoothCarrierSource_eq_gammaShift hr hz, suzukiGammaShiftSpectralSource_eq_add hz,
    add_sub_cancel_left, norm_mul]
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
    (norm_suzukiGammaShiftCompletionSource_le hr hz) (norm_nonneg P)

end
end RiemannGaussian
