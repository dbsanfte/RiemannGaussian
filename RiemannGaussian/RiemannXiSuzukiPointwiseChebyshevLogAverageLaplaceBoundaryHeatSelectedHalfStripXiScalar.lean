import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatSelectedHalfStripXiLogDerivative

/-!
# Real scalar form of the selected xi heat frontier

This module takes the imaginary part of the remaining literal xi-logarithmic-
derivative contour functional. It proves all interval and planar integrability
needed to commute real and imaginary parts through the integrals, and rewrites
the result as two real vertical integrals minus one real planar bulk integral.

The bulk integrand is computed explicitly from the real and imaginary parts of
`logDeriv riemannXi`. Lean also proves that its two coefficients are exactly
the partial derivatives of the real heat kernel, yielding the checked
first-order pairing that will feed a Green/Dirichlet-energy analysis.

The resulting real scalar still converges without normalization to `2 * pi`
times the complete nonnegative boundary-heat detector. No estimate forcing
that scalar to vanish is asserted here; unconditional arithmetic rigidity
remains the open RH-strength step.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Interval Topology

/-- The shifted boundary-heat kernel as a real function of its horizontal and
vertical coordinates. -/
def suzukiChebyshevLaplaceBoundaryHeatRealKernel
    (x tau a y : ℝ) : ℝ :=
  -2 * a * Real.exp (-tau * ((x - y) ^ 2 + a ^ 2))

/-- The completed-xi logarithmic derivative at the shifted coordinate
`1 / 2 + a + I * y`. -/
def shiftedRiemannXiLogDerivative (a y : ℝ) : ℂ :=
  logDeriv riemannXi (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)

/-- The real integrand obtained from a vertical boundary term of the weighted
xi logarithmic derivative. -/
def suzukiChebyshevLaplaceBoundaryHeatXiBoundaryScalarIntegrand
    (x tau a y : ℝ) : ℝ :=
  suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau a y *
    (shiftedRiemannXiLogDerivative a y).re

/-- The imaginary part of the xi logarithmic-derivative Cauchy--Green source,
written entirely as a real coordinate integrand. -/
def suzukiChebyshevLaplaceBoundaryHeatXiBulkScalarIntegrand
    (x tau a y : ℝ) : ℝ :=
  2 * Real.exp (-tau * ((x - y) ^ 2 + a ^ 2)) *
    (2 * tau * a * (x - y) * (shiftedRiemannXiLogDerivative a y).im +
      (2 * tau * a ^ 2 - 1) * (shiftedRiemannXiLogDerivative a y).re)

/-- The real part of the heat-weighted xi logarithmic derivative on a vertical
coordinate line is the explicit real boundary scalar integrand. -/
theorem suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative_re_coordinate (x tau a y : ℝ) :
    (suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative x tau
      ((a : ℂ) + (y : ℂ) * Complex.I)).re =
      suzukiChebyshevLaplaceBoundaryHeatXiBoundaryScalarIntegrand x tau a y := by
  have hshift :
      ((a : ℂ) + (y : ℂ) * Complex.I) + 1 / 2 =
        (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
    push_cast
    ring
  unfold suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative
  rw [suzukiChebyshevLaplaceBoundaryHeatKernel_apply]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [hshift]
  unfold suzukiChebyshevLaplaceBoundaryHeatXiBoundaryScalarIntegrand
    suzukiChebyshevLaplaceBoundaryHeatRealKernel
    shiftedRiemannXiLogDerivative
  simp

/-- The imaginary part of the heat source times the xi logarithmic derivative
is the explicit real bulk scalar integrand in shifted coordinates. -/
theorem suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource_im_coordinate
    (x tau a y : ℝ) :
    (suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource x tau
      ((a : ℂ) + (y : ℂ) * Complex.I)).im =
      suzukiChebyshevLaplaceBoundaryHeatXiBulkScalarIntegrand x tau a y := by
  have hshift :
      ((a : ℂ) + (y : ℂ) * Complex.I) + 1 / 2 =
        (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
    push_cast
    ring
  have hre : (((a : ℂ) + (y : ℂ) * Complex.I).re) = a := by simp
  have him : (((a : ℂ) + (y : ℂ) * Complex.I).im) = y := by simp
  unfold suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource
    suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource
  rw [hre, him, hshift]
  unfold suzukiChebyshevLaplaceBoundaryHeatXiBulkScalarIntegrand
    shiftedRiemannXiLogDerivative
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.I_re,
    Complex.I_im, Complex.re_ofNat, Complex.im_ofNat, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im, pow_two, zero_mul,
    mul_zero, one_mul, add_zero, zero_add, sub_zero]
  ring

/-- The horizontal-coordinate derivative of the real heat kernel is the
coefficient multiplying the real part of the xi logarithmic derivative. -/
theorem hasDerivAt_suzukiChebyshevLaplaceBoundaryHeatRealKernel_realCoordinate (x tau a y : ℝ) :
    HasDerivAt (fun u : ℝ =>
      suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau u y)
      (2 * Real.exp (-tau * ((x - y) ^ 2 + a ^ 2)) *
        (2 * tau * a ^ 2 - 1)) a := by
  unfold suzukiChebyshevLaplaceBoundaryHeatRealKernel
  have hsq : HasDerivAt (fun u : ℝ => u ^ 2) (2 * a) a := by
    apply ((hasDerivAt_id a).pow 2).congr_deriv
    simp [id]
  have hsum : HasDerivAt (fun u : ℝ => (x - y) ^ 2 + u ^ 2)
      (2 * a) a := by
    simpa using hsq.const_add ((x - y) ^ 2)
  have hexp := (hsum.const_mul (-tau)).exp
  have hcoef : HasDerivAt (fun u : ℝ => -2 * u) (-2) a := by
    simpa using (hasDerivAt_id a).const_mul (-2)
  apply (hcoef.mul hexp).congr_deriv
  ring

/-- The vertical-coordinate derivative of the real heat kernel is the
negative coefficient paired with the imaginary xi logarithmic derivative. -/
theorem hasDerivAt_suzukiChebyshevLaplaceBoundaryHeatRealKernel_imaginaryCoordinate
    (x tau a y : ℝ) :
    HasDerivAt (fun v : ℝ =>
      suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau a v)
      (-2 * Real.exp (-tau * ((x - y) ^ 2 + a ^ 2)) *
        (2 * tau * a * (x - y))) y := by
  unfold suzukiChebyshevLaplaceBoundaryHeatRealKernel
  have hxsub : HasDerivAt (fun v : ℝ => x - v) (-1) y :=
    (hasDerivAt_id y).const_sub x
  have hsq : HasDerivAt (fun v : ℝ => (x - v) ^ 2)
      (-2 * (x - y)) y := by
    apply (hxsub.pow 2).congr_deriv
    ring
  have hsum : HasDerivAt (fun v : ℝ => (x - v) ^ 2 + a ^ 2)
      (-2 * (x - y)) y := by
    simpa using hsq.add_const (a ^ 2)
  have hexp := (hsum.const_mul (-tau)).exp
  apply ((hasDerivAt_const y (-2 * a)).mul hexp).congr_deriv
  ring

/-- The heat-weighted genuine xi logarithmic derivative is interval integrable
on every selected near-critical right vertical side. -/
theorem intervalIntegrable_separatedSelectedLaplaceXiLogDerivativeRightBoundaryHeat
    (x tau : ℝ) (n : ℕ) :
    IntervalIntegrable
      (fun y : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative x tau
          ((selectedLaplaceSeparatedRightBoundary n : ℂ) +
            (y : ℂ) * Complex.I)) volume
      (-quantitativeSpectralBoundaryTruncation n)
      (quantitativeSpectralBoundaryTruncation n) := by
  let r : ℝ := selectedLaplaceSeparatedRightBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  have hdomain : [[r, r]] ×ℂ [[-T, T]] ⊆
      suzukiChebyshevLogAverageLaplacePoleClearedDomain := by
    simpa [r, T] using
      separatedSelectedLaplaceRightVerticalRectangle_subset_poleClearedDomain n
  have hfullRect :=
    rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
      x tau r r (-T) T hdomain
  have hfull : IntervalIntegrable
      (fun y : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
          ((r : ℂ) + (y : ℂ) * Complex.I)) volume (-T) T :=
    hfullRect.2.2.1
  have hregularAnalytic : ∀ p ∈ [[r, r]] ×ℂ [[-T, T]],
      AnalyticAt ℂ suzukiChebyshevLogAverageLaplaceRegularCorrection p := by
    intro p hp
    have hpDomain := hdomain hp
    apply
      analyticAt_suzukiChebyshevLogAverageLaplaceRegularCorrection_of_re_gt_neg_half
    change 0 < (p + 1 / 2).re ∧ riemannXi (p + 1 / 2) ≠ 0 at hpDomain
    simp at hpDomain
    linarith [hpDomain.1]
  have hregularRect :=
    rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
      x tau r r (-T) T
        suzukiChebyshevLogAverageLaplaceRegularCorrection hregularAnalytic
  have hregular : IntervalIntegrable
      (fun y : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection x tau
          ((r : ℂ) + (y : ℂ) * Complex.I)) volume (-T) T := by
    change IntervalIntegrable
      (fun y : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
          x tau suzukiChebyshevLogAverageLaplaceRegularCorrection
          ((r : ℂ) + (y : ℂ) * Complex.I)) volume (-T) T
    exact hregularRect.2.2.1
  have hsub := hfull.sub hregular
  apply hsub.congr
  intro y hy
  change
    suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
          ((r : ℂ) + (y : ℂ) * Complex.I) -
        suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection x tau
          ((r : ℂ) + (y : ℂ) * Complex.I) =
      suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative x tau
        ((r : ℂ) + (y : ℂ) * Complex.I)
  rw [suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_eq_xiLogDerivative_add_regularCorrection]
  ring

/-- The heat-weighted genuine xi logarithmic derivative is interval integrable
on every selected near-`-1 / 2` left vertical side. -/
theorem intervalIntegrable_separatedSelectedLaplaceXiLogDerivativeLeftBoundaryHeat
    (x tau : ℝ) (n : ℕ) :
    IntervalIntegrable
      (fun y : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative x tau
          ((selectedLaplaceSeparatedLeftBoundary n : ℂ) +
            (y : ℂ) * Complex.I)) volume
      (-quantitativeSpectralBoundaryTruncation n)
      (quantitativeSpectralBoundaryTruncation n) := by
  let l : ℝ := selectedLaplaceSeparatedLeftBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  have hdomain : [[l, l]] ×ℂ [[-T, T]] ⊆
      suzukiChebyshevLogAverageLaplacePoleClearedDomain := by
    simpa [l, T] using
      separatedSelectedLaplaceLeftVerticalRectangle_subset_poleClearedDomain n
  have hfullRect :=
    rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
      x tau l l (-T) T hdomain
  have hfull : IntervalIntegrable
      (fun y : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
          ((l : ℂ) + (y : ℂ) * Complex.I)) volume (-T) T :=
    hfullRect.2.2.1
  have hregularAnalytic : ∀ p ∈ [[l, l]] ×ℂ [[-T, T]],
      AnalyticAt ℂ suzukiChebyshevLogAverageLaplaceRegularCorrection p := by
    intro p hp
    have hpDomain := hdomain hp
    apply
      analyticAt_suzukiChebyshevLogAverageLaplaceRegularCorrection_of_re_gt_neg_half
    change 0 < (p + 1 / 2).re ∧ riemannXi (p + 1 / 2) ≠ 0 at hpDomain
    simp at hpDomain
    linarith [hpDomain.1]
  have hregularRect :=
    rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
      x tau l l (-T) T
        suzukiChebyshevLogAverageLaplaceRegularCorrection hregularAnalytic
  have hregular : IntervalIntegrable
      (fun y : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection x tau
          ((l : ℂ) + (y : ℂ) * Complex.I)) volume (-T) T := by
    change IntervalIntegrable
      (fun y : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
          x tau suzukiChebyshevLogAverageLaplaceRegularCorrection
          ((l : ℂ) + (y : ℂ) * Complex.I)) volume (-T) T
    exact hregularRect.2.2.1
  have hsub := hfull.sub hregular
  apply hsub.congr
  intro y hy
  change
    suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
          ((l : ℂ) + (y : ℂ) * Complex.I) -
        suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrection x tau
          ((l : ℂ) + (y : ℂ) * Complex.I) =
      suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative x tau
        ((l : ℂ) + (y : ℂ) * Complex.I)
  rw [suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_eq_xiLogDerivative_add_regularCorrection]
  ring

/-- The genuine xi logarithmic-derivative source is planar integrable through
the complete finite divisor inside every selected rectangle. -/
theorem integrableOn_separatedSelectedLaplaceXiLogDerivativeSource (x tau : ℝ) (n : ℕ) :
    IntegrableOn
      (suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource
        x tau)
      ([[selectedLaplaceSeparatedLeftBoundary n,
          selectedLaplaceSeparatedRightBoundary n]] ×ℂ
        [[-quantitativeSpectralBoundaryTruncation n,
          quantitativeSpectralBoundaryTruncation n]]) volume := by
  let l : ℝ := selectedLaplaceSeparatedLeftBoundary n
  let r : ℝ := selectedLaplaceSeparatedRightBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let R : Set ℂ := [[l, r]] ×ℂ [[-T, T]]
  have hT0 : 0 ≤ T := quantitativeSpectralBoundaryTruncation_nonneg n
  have hlr : l ≤ r :=
    (selectedLaplaceSeparatedLeftBoundary_lt_rightBoundary n).le
  have hbu : -T ≤ T := by linarith
  have hrectangle : R ⊆ suzukiChebyshevLaplaceFiniteSlab T := by
    simpa [R, l, r, T] using
      separatedSelectedLaplaceRectangle_subset_finiteSlab n
  have hfull : IntegrableOn
      (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau)
      R volume := by
    simpa [R] using
      integrableOn_suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource_finiteRectangle
        x tau l r (-T) T hT0 hrectangle
  have hregularAnalytic : ∀ p ∈ R,
      AnalyticAt ℂ suzukiChebyshevLogAverageLaplaceRegularCorrection p := by
    intro p hp
    apply
      analyticAt_suzukiChebyshevLogAverageLaplaceRegularCorrection_of_re_gt_neg_half
    dsimp only [R] at hp
    rw [uIcc_of_le hlr, uIcc_of_le hbu] at hp
    exact (selectedLaplaceSeparatedLeftBoundary_spec n).1.trans_le hp.1.1
  have hregular : IntegrableOn
      (suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrectionSource
        x tau) R volume := by
    have hcontinuous : ContinuousOn
        (suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrectionSource
          x tau) R := by
      unfold
        suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrectionSource
      exact
        (continuous_suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource
            x tau).continuousOn.mul
          (show AnalyticOnNhd ℂ
              suzukiChebyshevLogAverageLaplaceRegularCorrection R from
            hregularAnalytic).continuousOn
    exact hcontinuous.integrableOn_compact
      (isCompact_uIcc.reProdIm isCompact_uIcc)
  have hsub := hfull.sub hregular
  apply hsub.congr_fun _
    (isCompact_uIcc.reProdIm isCompact_uIcc).measurableSet
  intro p hp
  change
    suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau p -
        suzukiChebyshevLaplaceBoundaryHeatWeightedRegularCorrectionSource
          x tau p =
      suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource
        x tau p
  rw [suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource_eq_xiLogDerivative_add_regularCorrection]
  ring

/-- At an arbitrary complex point, the imaginary source component is the
explicit real bulk integrand evaluated at the point's two coordinates. -/
theorem suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource_im (x tau : ℝ) (p : ℂ) :
    (suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource
      x tau p).im =
      suzukiChebyshevLaplaceBoundaryHeatXiBulkScalarIntegrand
        x tau p.re p.im := by
  have hp : ((p.re : ℂ) + (p.im : ℂ) * Complex.I) = p := by
    apply Complex.ext <;> simp
  simpa only [hp] using
    suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource_im_coordinate
      x tau p.re p.im

/-- The bulk scalar integrand is the first-order pairing of the two heat-kernel
partial derivatives with the real and negative imaginary parts of `xi'/xi`. -/
theorem suzukiChebyshevLaplaceBoundaryHeatXiBulkScalarIntegrand_eq_kernel_deriv_pair
    (x tau a y : ℝ) :
    suzukiChebyshevLaplaceBoundaryHeatXiBulkScalarIntegrand x tau a y =
      deriv (fun u : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau u y) a *
          (shiftedRiemannXiLogDerivative a y).re -
        deriv (fun v : ℝ =>
          suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau a v) y *
          (shiftedRiemannXiLogDerivative a y).im := by
  rw [(hasDerivAt_suzukiChebyshevLaplaceBoundaryHeatRealKernel_realCoordinate x tau a y).deriv,
    (hasDerivAt_suzukiChebyshevLaplaceBoundaryHeatRealKernel_imaginaryCoordinate x tau a y).deriv]
  unfold suzukiChebyshevLaplaceBoundaryHeatXiBulkScalarIntegrand
  ring

/-- The fully real selected xi frontier: right vertical scalar minus left
vertical scalar minus the planar xi source scalar. -/
def separatedSelectedLaplaceXiLogDerivativeScalarHeat (x tau : ℝ) (n : ℕ) : ℝ :=
  (∫ y : ℝ in -quantitativeSpectralBoundaryTruncation n..
      quantitativeSpectralBoundaryTruncation n,
    suzukiChebyshevLaplaceBoundaryHeatXiBoundaryScalarIntegrand x tau
      (selectedLaplaceSeparatedRightBoundary n) y) -
  (∫ y : ℝ in -quantitativeSpectralBoundaryTruncation n..
      quantitativeSpectralBoundaryTruncation n,
    suzukiChebyshevLaplaceBoundaryHeatXiBoundaryScalarIntegrand x tau
      (selectedLaplaceSeparatedLeftBoundary n) y) -
  ∫ p : ℂ in
      ([[selectedLaplaceSeparatedLeftBoundary n,
          selectedLaplaceSeparatedRightBoundary n]] ×ℂ
        [[-quantitativeSpectralBoundaryTruncation n,
          quantitativeSpectralBoundaryTruncation n]]),
    suzukiChebyshevLaplaceBoundaryHeatXiBulkScalarIntegrand
      x tau p.re p.im

/-- The imaginary part of the oriented right xi vertical integral is its
explicit real boundary scalar integral. -/
theorem separatedSelectedLaplaceXiLogDerivativeRightBoundaryHeat_im (x tau : ℝ) (n : ℕ) :
    (separatedSelectedLaplaceXiLogDerivativeRightBoundaryHeat x tau n).im =
      ∫ y : ℝ in -quantitativeSpectralBoundaryTruncation n..
          quantitativeSpectralBoundaryTruncation n,
        suzukiChebyshevLaplaceBoundaryHeatXiBoundaryScalarIntegrand x tau
          (selectedLaplaceSeparatedRightBoundary n) y := by
  have hint := intervalIntegrable_separatedSelectedLaplaceXiLogDerivativeRightBoundaryHeat x tau n
  unfold separatedSelectedLaplaceXiLogDerivativeRightBoundaryHeat
    rectangularRightBoundaryIntegral
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul,
    one_mul, zero_add]
  have hre :
      (∫ y : ℝ in -quantitativeSpectralBoundaryTruncation n..
          quantitativeSpectralBoundaryTruncation n,
        (suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative x tau
          ((selectedLaplaceSeparatedRightBoundary n : ℂ) +
            (y : ℂ) * Complex.I)).re) =
      (∫ y : ℝ in -quantitativeSpectralBoundaryTruncation n..
          quantitativeSpectralBoundaryTruncation n,
        suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative x tau
          ((selectedLaplaceSeparatedRightBoundary n : ℂ) +
            (y : ℂ) * Complex.I)).re := by
    simpa using intervalIntegral.intervalIntegral_re hint
  rw [← hre]
  apply intervalIntegral.integral_congr
  intro y hy
  exact
    suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative_re_coordinate
      x tau (selectedLaplaceSeparatedRightBoundary n) y

/-- The imaginary part of the oriented left xi vertical integral is the
negative of its explicit real boundary scalar integral. -/
theorem separatedSelectedLaplaceXiLogDerivativeLeftBoundaryHeat_im (x tau : ℝ) (n : ℕ) :
    (separatedSelectedLaplaceXiLogDerivativeLeftBoundaryHeat x tau n).im =
      -(∫ y : ℝ in -quantitativeSpectralBoundaryTruncation n..
          quantitativeSpectralBoundaryTruncation n,
        suzukiChebyshevLaplaceBoundaryHeatXiBoundaryScalarIntegrand x tau
          (selectedLaplaceSeparatedLeftBoundary n) y) := by
  have hint := intervalIntegrable_separatedSelectedLaplaceXiLogDerivativeLeftBoundaryHeat x tau n
  unfold separatedSelectedLaplaceXiLogDerivativeLeftBoundaryHeat
    rectangularLeftBoundaryIntegral
  simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, neg_zero, zero_mul, neg_one_mul, zero_add]
  have hre :
      (∫ y : ℝ in -quantitativeSpectralBoundaryTruncation n..
          quantitativeSpectralBoundaryTruncation n,
        (suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative x tau
          ((selectedLaplaceSeparatedLeftBoundary n : ℂ) +
            (y : ℂ) * Complex.I)).re) =
      (∫ y : ℝ in -quantitativeSpectralBoundaryTruncation n..
          quantitativeSpectralBoundaryTruncation n,
        suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative x tau
          ((selectedLaplaceSeparatedLeftBoundary n : ℂ) +
            (y : ℂ) * Complex.I)).re := by
    simpa using intervalIntegral.intervalIntegral_re hint
  rw [← hre]
  congr 1
  apply intervalIntegral.integral_congr
  intro y hy
  exact
    suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative_re_coordinate
      x tau (selectedLaplaceSeparatedLeftBoundary n) y

/-- The imaginary part of the xi Cauchy--Green bulk is its explicit real
planar source integral. -/
theorem separatedSelectedLaplaceXiLogDerivativeBulkHeat_im (x tau : ℝ) (n : ℕ) :
    (separatedSelectedLaplaceXiLogDerivativeBulkHeat x tau n).im =
      ∫ p : ℂ in
        ([[selectedLaplaceSeparatedLeftBoundary n,
            selectedLaplaceSeparatedRightBoundary n]] ×ℂ
          [[-quantitativeSpectralBoundaryTruncation n,
            quantitativeSpectralBoundaryTruncation n]]),
        suzukiChebyshevLaplaceBoundaryHeatXiBulkScalarIntegrand
          x tau p.re p.im := by
  let l : ℝ := selectedLaplaceSeparatedLeftBoundary n
  let r : ℝ := selectedLaplaceSeparatedRightBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let R : Set ℂ := [[l, r]] ×ℂ [[-T, T]]
  have hlr : l ≤ r :=
    (selectedLaplaceSeparatedLeftBoundary_lt_rightBoundary n).le
  have hbu : -T ≤ T := by
    linarith [quantitativeSpectralBoundaryTruncation_nonneg n]
  have hint : IntegrableOn
      (suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource
        x tau) R volume := by
    simpa [R, l, r, T] using integrableOn_separatedSelectedLaplaceXiLogDerivativeSource x tau n
  unfold separatedSelectedLaplaceXiLogDerivativeBulkHeat
  rw [rectangularAreaIntegral_eq_setIntegral hlr hbu _ hint]
  change
    (∫ p : ℂ in R,
      suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource
        x tau p).im =
      ∫ p : ℂ in R,
        suzukiChebyshevLaplaceBoundaryHeatXiBulkScalarIntegrand
          x tau p.re p.im
  have himap :
      (∫ p : ℂ in R,
        (suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource
          x tau p).im) =
      (∫ p : ℂ in R,
        suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource
          x tau p).im := by
    simpa using integral_im hint
  rw [← himap]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun p =>
    suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivativeSource_im
      x tau p

/-- At every finite stage, the imaginary part of the literal three-term xi
functional is exactly the fully real scalar heat functional. -/
theorem separatedSelectedLaplaceXiLogDerivativeVerticalSubBulkHeat_im_eq_scalarHeat
    (x tau : ℝ) (n : ℕ) :
    (separatedSelectedLaplaceXiLogDerivativeVerticalSubBulkHeat
      x tau n).im = separatedSelectedLaplaceXiLogDerivativeScalarHeat x tau n := by
  unfold separatedSelectedLaplaceXiLogDerivativeVerticalSubBulkHeat
    separatedSelectedLaplaceXiLogDerivativeScalarHeat
  rw [Complex.sub_im, Complex.add_im,
    separatedSelectedLaplaceXiLogDerivativeRightBoundaryHeat_im,
    separatedSelectedLaplaceXiLogDerivativeLeftBoundaryHeat_im,
    separatedSelectedLaplaceXiLogDerivativeBulkHeat_im]
  ring

/-- The explicit real scalar heat functional converges without normalization
to `2 * pi` times the complete nonnegative xi boundary-heat detector. -/
theorem tendsto_separatedSelectedLaplaceXiLogDerivativeScalarHeat
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto (separatedSelectedLaplaceXiLogDerivativeScalarHeat x tau) atTop
      (𝓝 (2 * Real.pi *
        riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) := by
  have hlimit :=
    tendsto_separatedSelectedLaplaceXiLogDerivativeVerticalSubBulkHeat_im
      x htau
  apply hlimit.congr'
  exact Eventually.of_forall fun n =>
    separatedSelectedLaplaceXiLogDerivativeVerticalSubBulkHeat_im_eq_scalarHeat x tau n

end

end RiemannGaussian
