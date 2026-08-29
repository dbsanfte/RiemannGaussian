import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaDerivative
import RiemannGaussian.RiemannXiSuzukiRealAxisCompletedLog
import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatSelectedHalfStripXiLogNormPositiveHalfStrip

/-!
# The positive-strip xi gradient as a convergent paired-eta quotient

This module joins the arithmetic paired-eta series to the live reflected
xi-log-norm detector. The completed-factor identity first replaces the genuine
`xi'/xi` by the quotient of the convergent differentiated eta series and the
convergent eta series, together with explicit elementary and Archimedean
corrections, throughout `1 / 2 < re s < 1` away from the divisor.

At nonzero shifted points, the real and negative imaginary components of this
arithmetic quotient are exactly the two coordinate derivatives of
`log |xi|`. Both heat-boundary integrands and the full heat-gradient pairing
therefore acquire arithmetic eta-series representations.

The selected reflected vertical boundaries are proved pointwise zero-free.
The reflected planar rectangle can contain finitely many xi zeros, so the
bulk identity is promoted only almost everywhere after removing that finite
null set. This is sufficient to prove genuine planar integrability and exact
equality of the ordinary integrals. The resulting entirely positive-strip
paired-eta functional is equal at every finite stage to the live xi-gradient
functional and has the same unnormalized detector limit.

No estimate or sign assertion for the new arithmetic functional is made here.
In particular, the finite xi divisor is retained rather than assumed absent.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The completed xi logarithmic derivative with its zeta term replaced by
the explicit convergent paired-eta derivative quotient. -/
def pairedEtaArithmeticXiLogDerivative (s : ℂ) : ℂ :=
  1 / s + 1 / (s - 1) - Complex.log Real.pi / 2 +
    Complex.digamma (s / 2) / 2 +
      (∑' n : ℕ, pairedEtaCoreDerivativeSummand s n) /
          pairedEtaCore s - pairedEtaFactorLogDerivative s

/-- Away from the zeta divisor in the positive critical half-strip, the
genuine `xi'/xi` is exactly the paired-eta arithmetic expression. -/
theorem logDeriv_riemannXi_eq_pairedEtaArithmetic_of_half_lt_re_of_re_lt_one
    {s : ℂ} (hlower : 1 / 2 < s.re) (hupper : s.re < 1)
    (hzeta : riemannZeta s ≠ 0) :
    logDeriv riemannXi s = pairedEtaArithmeticXiLogDerivative s := by
  have hsone : s ≠ 1 := by
    intro h
    subst s
    norm_num at hupper
  rw [logDeriv_riemannXi_of_re_pos_of_riemannZeta_ne_zero
    (by linarith) hsone hzeta]
  rw [logDeriv_riemannZeta_eq_pairedEtaArithmetic_of_half_lt_re_of_re_lt_one
    hlower hupper hzeta]
  unfold pairedEtaArithmeticXiLogDerivative
  ring

/-- In the positive half-plane away from the pole, nonvanishing of xi forces
nonvanishing of zeta through the checked completed-factor identity. -/
theorem riemannZeta_ne_zero_of_riemannXi_ne_zero_of_re_pos_of_ne_one
    {s : ℂ} (hs : 0 < s.re) (hsone : s ≠ 1)
    (hxi : riemannXi s ≠ 0) :
    riemannZeta s ≠ 0 := by
  intro hzeta
  apply hxi
  rw [riemannXi_eq_mul_Gammaℝ_riemannZeta_of_re_pos hs hsone, hzeta]
  simp

/-- Away from the xi divisor in the positive critical half-strip, the
genuine `xi'/xi` is exactly the paired-eta arithmetic expression. -/
theorem logDeriv_riemannXi_eq_pairedEtaArithmetic_of_half_lt_re_of_re_lt_one_of_ne_zero
    {s : ℂ} (hlower : 1 / 2 < s.re) (hupper : s.re < 1)
    (hxi : riemannXi s ≠ 0) :
    logDeriv riemannXi s = pairedEtaArithmeticXiLogDerivative s := by
  have hsone : s ≠ 1 := by
    intro h
    subst s
    norm_num at hupper
  exact logDeriv_riemannXi_eq_pairedEtaArithmetic_of_half_lt_re_of_re_lt_one
    hlower hupper
    (riemannZeta_ne_zero_of_riemannXi_ne_zero_of_re_pos_of_ne_one
      (by linarith) hsone hxi)

/-- The paired-eta arithmetic xi logarithmic derivative in the detector's
shifted coordinates `s = 1 / 2 + a + I*y`. -/
def shiftedPairedEtaArithmeticXiLogDerivative (a y : ℝ) : ℂ :=
  pairedEtaArithmeticXiLogDerivative
    (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)

/-- At every nonzero point with `0 < a < 1 / 2`, the detector's genuine
shifted xi logarithmic derivative equals the paired-eta expression. -/
theorem shiftedRiemannXiLogDerivative_eq_pairedEtaArithmetic
    {a y : ℝ} (ha0 : 0 < a) (haHalf : a < 1 / 2)
    (hxi : riemannXi
      (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) ≠ 0) :
    shiftedRiemannXiLogDerivative a y =
      shiftedPairedEtaArithmeticXiLogDerivative a y := by
  unfold shiftedRiemannXiLogDerivative
    shiftedPairedEtaArithmeticXiLogDerivative
  apply
    logDeriv_riemannXi_eq_pairedEtaArithmetic_of_half_lt_re_of_re_lt_one_of_ne_zero
  · simp
    linarith
  · simp
    linarith
  · exact hxi

/-- Off the divisor, the horizontal derivative of `log |xi|` is the real
part of the paired-eta arithmetic xi logarithmic derivative. -/
theorem hasDerivAt_shiftedRiemannXiLogNorm_realCoordinate_eq_pairedEtaArithmetic
    {a y : ℝ} (ha0 : 0 < a) (haHalf : a < 1 / 2)
    (hxi : riemannXi
      (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) ≠ 0) :
    HasDerivAt (fun u : ℝ => shiftedRiemannXiLogNorm u y)
      (shiftedPairedEtaArithmeticXiLogDerivative a y).re a := by
  rw [← shiftedRiemannXiLogDerivative_eq_pairedEtaArithmetic
    ha0 haHalf hxi]
  exact hasDerivAt_shiftedRiemannXiLogNorm_realCoordinate hxi

/-- Off the divisor, the vertical derivative of `log |xi|` is the negative
imaginary part of the paired-eta arithmetic xi logarithmic derivative. -/
theorem hasDerivAt_shiftedRiemannXiLogNorm_imaginaryCoordinate_eq_pairedEtaArithmetic
    {a y : ℝ} (ha0 : 0 < a) (haHalf : a < 1 / 2)
    (hxi : riemannXi
      (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) ≠ 0) :
    HasDerivAt (shiftedRiemannXiLogNorm a)
      (-(shiftedPairedEtaArithmeticXiLogDerivative a y).im) y := by
  rw [← shiftedRiemannXiLogDerivative_eq_pairedEtaArithmetic
    ha0 haHalf hxi]
  exact hasDerivAt_shiftedRiemannXiLogNorm_imaginaryCoordinate hxi

/-- The real heat boundary integrand formed from the paired-eta arithmetic
xi logarithmic derivative. -/
def suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticBoundaryIntegrand
    (x tau a y : ℝ) : ℝ :=
  suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau a y *
    (shiftedPairedEtaArithmeticXiLogDerivative a y).re

/-- The heat-gradient pairing formed from the real and negative imaginary
parts of the paired-eta arithmetic xi logarithmic derivative. -/
def suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticGradientIntegrand
    (x tau a y : ℝ) : ℝ :=
  deriv (fun u : ℝ =>
    suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau u y) a *
      (shiftedPairedEtaArithmeticXiLogDerivative a y).re -
    deriv (fun v : ℝ =>
      suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau a v) y *
      (shiftedPairedEtaArithmeticXiLogDerivative a y).im

/-- Off the divisor in the positive shifted half-strip, the xi-log-norm
boundary integrand is its paired-eta arithmetic form. -/
theorem suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand_eq_pairedEtaArithmetic
    (x tau : ℝ) {a y : ℝ} (ha0 : 0 < a) (haHalf : a < 1 / 2)
    (hxi : riemannXi
      (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) ≠ 0) :
    suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand x tau a y =
      suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticBoundaryIntegrand
        x tau a y := by
  unfold suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand
    suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticBoundaryIntegrand
  rw [(hasDerivAt_shiftedRiemannXiLogNorm_realCoordinate_eq_pairedEtaArithmetic
    ha0 haHalf hxi).deriv]

/-- Off the divisor in the positive shifted half-strip, the xi-log-norm
gradient pairing is its paired-eta arithmetic form. -/
theorem suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand_eq_pairedEtaArithmetic
    (x tau : ℝ) {a y : ℝ} (ha0 : 0 < a) (haHalf : a < 1 / 2)
    (hxi : riemannXi
      (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) ≠ 0) :
    suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand x tau a y =
      suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticGradientIntegrand
        x tau a y := by
  unfold suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
    suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticGradientIntegrand
  rw [(hasDerivAt_shiftedRiemannXiLogNorm_realCoordinate_eq_pairedEtaArithmetic
      ha0 haHalf hxi).deriv,
    (hasDerivAt_shiftedRiemannXiLogNorm_imaginaryCoordinate_eq_pairedEtaArithmetic
      ha0 haHalf hxi).deriv]
  ring

/-- Reflecting the shifted real coordinate sends xi to the conjugate of its
value at the original shifted coordinate. -/
theorem riemannXi_shifted_neg_realCoordinate (a y : ℝ) :
    riemannXi
        (((-a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) =
      starRingEnd ℂ
        (riemannXi
          (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) := by
  let z : ℂ :=
    (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
  have hreflect :
      (((-a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) =
        1 - starRingEnd ℂ z := by
    dsimp [z]
    apply Complex.ext
    · simp
      ring
    · simp
  rw [hreflect, riemannXi_one_sub, riemannXi_conj]

/-- Nonvanishing of xi is preserved when the shifted real coordinate is
reflected. -/
theorem riemannXi_shifted_neg_realCoordinate_ne_zero
    {a y : ℝ}
    (hxi : riemannXi
      (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) ≠ 0) :
    riemannXi
      (((-a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
  rw [riemannXi_shifted_neg_realCoordinate]
  exact (map_ne_zero (starRingEnd ℂ)).mpr hxi

/-- The selected near-critical vertical side is xi-zero-free throughout its
bounded-height interval. -/
theorem riemannXi_shifted_selectedRightBoundary_ne_zero
    (n : ℕ) {y : ℝ}
    (hy : |y| ≤ quantitativeSpectralBoundaryTruncation n) :
    riemannXi
      ((((selectedLaplaceSeparatedRightBoundary n) + 1 / 2 : ℝ) : ℂ) +
        (y : ℂ) * Complex.I) ≠ 0 := by
  let r : ℝ := selectedLaplaceSeparatedRightBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  have hp : ((r : ℂ) + (y : ℂ) * Complex.I) ∈
      [[r, r]] ×ℂ [[-T, T]] := by
    rw [mem_reProdIm, uIcc_of_le le_rfl,
      uIcc_of_le (by
        linarith [quantitativeSpectralBoundaryTruncation_nonneg n] : -T ≤ T)]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, mul_zero, sub_zero, zero_add, add_zero, mul_one]
    exact ⟨⟨le_rfl, le_rfl⟩, abs_le.mp (by simpa [T] using hy)⟩
  have hdomain :=
    separatedSelectedLaplaceRightVerticalRectangle_subset_poleClearedDomain
      n hp
  have hshift :
      ((r : ℂ) + (y : ℂ) * Complex.I) + 1 / 2 =
        (((r + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
    push_cast
    ring
  change 0 < (((r : ℂ) + (y : ℂ) * Complex.I) + 1 / 2).re ∧
    riemannXi (((r : ℂ) + (y : ℂ) * Complex.I) + 1 / 2) ≠ 0 at hdomain
  rw [hshift] at hdomain
  simpa [r] using hdomain.2

/-- The selected near-`s = 0` vertical side is xi-zero-free throughout its
bounded-height interval. -/
theorem riemannXi_shifted_selectedLeftBoundary_ne_zero
    (n : ℕ) {y : ℝ}
    (hy : |y| ≤ quantitativeSpectralBoundaryTruncation n) :
    riemannXi
      ((((selectedLaplaceSeparatedLeftBoundary n) + 1 / 2 : ℝ) : ℂ) +
        (y : ℂ) * Complex.I) ≠ 0 := by
  let l : ℝ := selectedLaplaceSeparatedLeftBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  have hp : ((l : ℂ) + (y : ℂ) * Complex.I) ∈
      [[l, l]] ×ℂ [[-T, T]] := by
    rw [mem_reProdIm, uIcc_of_le le_rfl,
      uIcc_of_le (by
        linarith [quantitativeSpectralBoundaryTruncation_nonneg n] : -T ≤ T)]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, mul_zero, sub_zero, zero_add, add_zero, mul_one]
    exact ⟨⟨le_rfl, le_rfl⟩, abs_le.mp (by simpa [T] using hy)⟩
  have hdomain :=
    separatedSelectedLaplaceLeftVerticalRectangle_subset_poleClearedDomain
      n hp
  have hshift :
      ((l : ℂ) + (y : ℂ) * Complex.I) + 1 / 2 =
        (((l + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
    push_cast
    ring
  change 0 < (((l : ℂ) + (y : ℂ) * Complex.I) + 1 / 2).re ∧
    riemannXi (((l : ℂ) + (y : ℂ) * Complex.I) + 1 / 2) ≠ 0 at hdomain
  rw [hshift] at hdomain
  simpa [l] using hdomain.2

/-- The reflected near-critical positive-strip vertical side is xi-zero-free
throughout its bounded-height interval. -/
theorem riemannXi_shifted_reflectedRightBoundary_ne_zero
    (n : ℕ) {y : ℝ}
    (hy : |y| ≤ quantitativeSpectralBoundaryTruncation n) :
    riemannXi
      (((-selectedLaplaceSeparatedRightBoundary n + 1 / 2 : ℝ) : ℂ) +
        (y : ℂ) * Complex.I) ≠ 0 :=
  riemannXi_shifted_neg_realCoordinate_ne_zero
    (riemannXi_shifted_selectedRightBoundary_ne_zero n hy)

/-- The reflected near-`s = 1` positive-strip vertical side is xi-zero-free
throughout its bounded-height interval. -/
theorem riemannXi_shifted_reflectedLeftBoundary_ne_zero
    (n : ℕ) {y : ℝ}
    (hy : |y| ≤ quantitativeSpectralBoundaryTruncation n) :
    riemannXi
      (((-selectedLaplaceSeparatedLeftBoundary n + 1 / 2 : ℝ) : ℂ) +
        (y : ℂ) * Complex.I) ≠ 0 :=
  riemannXi_shifted_neg_realCoordinate_ne_zero
    (riemannXi_shifted_selectedLeftBoundary_ne_zero n hy)

/-- The paired-eta arithmetic boundary integrand is interval integrable on
the reflected near-critical selected side. -/
theorem intervalIntegrable_suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmetic_reflectedRight
    (x tau : ℝ) (n : ℕ) :
    IntervalIntegrable
      (fun y : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticBoundaryIntegrand
          x tau (-selectedLaplaceSeparatedRightBoundary n) y)
      volume (-quantitativeSpectralBoundaryTruncation n)
        (quantitativeSpectralBoundaryTruncation n) := by
  have hbu : -quantitativeSpectralBoundaryTruncation n ≤
      quantitativeSpectralBoundaryTruncation n := by
    linarith [quantitativeSpectralBoundaryTruncation_nonneg n]
  have hcomplex :=
    intervalIntegrable_separatedSelectedLaplaceXiLogDerivativeRightBoundaryHeat
      x tau n
  have hre : IntervalIntegrable
      (fun y : ℝ =>
        (suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative x tau
          ((selectedLaplaceSeparatedRightBoundary n : ℂ) +
            (y : ℂ) * Complex.I)).re)
      volume (-quantitativeSpectralBoundaryTruncation n)
        (quantitativeSpectralBoundaryTruncation n) :=
    ⟨hcomplex.1.re, hcomplex.2.re⟩
  apply hre.congr
  intro y hy
  rw [uIoc_of_le hbu] at hy
  have hyabs : |y| ≤ quantitativeSpectralBoundaryTruncation n :=
    abs_le.mpr ⟨hy.1.le, hy.2⟩
  have hxi := riemannXi_shifted_selectedRightBoundary_ne_zero n hyabs
  have hxireflected :=
    riemannXi_shifted_reflectedRightBoundary_ne_zero n hyabs
  calc
    (suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative x tau
      ((selectedLaplaceSeparatedRightBoundary n : ℂ) +
        (y : ℂ) * Complex.I)).re =
        suzukiChebyshevLaplaceBoundaryHeatXiBoundaryScalarIntegrand x tau
          (selectedLaplaceSeparatedRightBoundary n) y :=
      suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative_re_coordinate
        x tau (selectedLaplaceSeparatedRightBoundary n) y
    _ = suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand x tau
          (selectedLaplaceSeparatedRightBoundary n) y :=
      suzukiChebyshevLaplaceBoundaryHeatXiBoundaryScalarIntegrand_eq_logNorm_deriv
        x tau (selectedLaplaceSeparatedRightBoundary n) y hxi
    _ = suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand x tau
          (-selectedLaplaceSeparatedRightBoundary n) y :=
      (suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand_neg_realCoordinate
        x tau (selectedLaplaceSeparatedRightBoundary n) y).symm
    _ = suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticBoundaryIntegrand
          x tau (-selectedLaplaceSeparatedRightBoundary n) y := by
      apply
        suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand_eq_pairedEtaArithmetic
      · exact (selectedLaplaceReflectedRightBoundary_spec n).1
      · linarith [(selectedLaplaceReflectedRightBoundary_spec n).2]
      · exact hxireflected

/-- The paired-eta arithmetic boundary integrand is interval integrable on
the reflected near-`s = 1` selected side. -/
theorem intervalIntegrable_suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmetic_reflectedLeft
    (x tau : ℝ) (n : ℕ) :
    IntervalIntegrable
      (fun y : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticBoundaryIntegrand
          x tau (-selectedLaplaceSeparatedLeftBoundary n) y)
      volume (-quantitativeSpectralBoundaryTruncation n)
        (quantitativeSpectralBoundaryTruncation n) := by
  have hbu : -quantitativeSpectralBoundaryTruncation n ≤
      quantitativeSpectralBoundaryTruncation n := by
    linarith [quantitativeSpectralBoundaryTruncation_nonneg n]
  have hcomplex :=
    intervalIntegrable_separatedSelectedLaplaceXiLogDerivativeLeftBoundaryHeat
      x tau n
  have hre : IntervalIntegrable
      (fun y : ℝ =>
        (suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative x tau
          ((selectedLaplaceSeparatedLeftBoundary n : ℂ) +
            (y : ℂ) * Complex.I)).re)
      volume (-quantitativeSpectralBoundaryTruncation n)
        (quantitativeSpectralBoundaryTruncation n) :=
    ⟨hcomplex.1.re, hcomplex.2.re⟩
  apply hre.congr
  intro y hy
  rw [uIoc_of_le hbu] at hy
  have hyabs : |y| ≤ quantitativeSpectralBoundaryTruncation n :=
    abs_le.mpr ⟨hy.1.le, hy.2⟩
  have hxi := riemannXi_shifted_selectedLeftBoundary_ne_zero n hyabs
  have hxireflected :=
    riemannXi_shifted_reflectedLeftBoundary_ne_zero n hyabs
  calc
    (suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative x tau
      ((selectedLaplaceSeparatedLeftBoundary n : ℂ) +
        (y : ℂ) * Complex.I)).re =
        suzukiChebyshevLaplaceBoundaryHeatXiBoundaryScalarIntegrand x tau
          (selectedLaplaceSeparatedLeftBoundary n) y :=
      suzukiChebyshevLaplaceBoundaryHeatWeightedXiLogDerivative_re_coordinate
        x tau (selectedLaplaceSeparatedLeftBoundary n) y
    _ = suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand x tau
          (selectedLaplaceSeparatedLeftBoundary n) y :=
      suzukiChebyshevLaplaceBoundaryHeatXiBoundaryScalarIntegrand_eq_logNorm_deriv
        x tau (selectedLaplaceSeparatedLeftBoundary n) y hxi
    _ = suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand x tau
          (-selectedLaplaceSeparatedLeftBoundary n) y :=
      (suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand_neg_realCoordinate
        x tau (selectedLaplaceSeparatedLeftBoundary n) y).symm
    _ = suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticBoundaryIntegrand
          x tau (-selectedLaplaceSeparatedLeftBoundary n) y := by
      apply
        suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand_eq_pairedEtaArithmetic
      · linarith [(selectedLaplaceReflectedLeftBoundary_spec n).1]
      · exact (selectedLaplaceReflectedLeftBoundary_spec n).2
      · exact hxireflected

/-- On the reflected near-critical vertical side, the xi-log-norm boundary
integral is exactly its paired-eta arithmetic integral. -/
theorem intervalIntegral_suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundary_eq_pairedEtaArithmetic_reflectedRight
    (x tau : ℝ) (n : ℕ) :
    (∫ y : ℝ in -quantitativeSpectralBoundaryTruncation n..
        quantitativeSpectralBoundaryTruncation n,
      suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand x tau
        (-selectedLaplaceSeparatedRightBoundary n) y) =
      ∫ y : ℝ in -quantitativeSpectralBoundaryTruncation n..
        quantitativeSpectralBoundaryTruncation n,
        suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticBoundaryIntegrand
          x tau (-selectedLaplaceSeparatedRightBoundary n) y := by
  have hbu : -quantitativeSpectralBoundaryTruncation n ≤
      quantitativeSpectralBoundaryTruncation n := by
    linarith [quantitativeSpectralBoundaryTruncation_nonneg n]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le hbu] at hy
  apply
    suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand_eq_pairedEtaArithmetic
  · exact (selectedLaplaceReflectedRightBoundary_spec n).1
  · linarith [(selectedLaplaceReflectedRightBoundary_spec n).2]
  · exact riemannXi_shifted_reflectedRightBoundary_ne_zero n
      (abs_le.mpr hy)

/-- On the reflected near-`s = 1` vertical side, the xi-log-norm boundary
integral is exactly its paired-eta arithmetic integral. -/
theorem intervalIntegral_suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundary_eq_pairedEtaArithmetic_reflectedLeft
    (x tau : ℝ) (n : ℕ) :
    (∫ y : ℝ in -quantitativeSpectralBoundaryTruncation n..
        quantitativeSpectralBoundaryTruncation n,
      suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand x tau
        (-selectedLaplaceSeparatedLeftBoundary n) y) =
      ∫ y : ℝ in -quantitativeSpectralBoundaryTruncation n..
        quantitativeSpectralBoundaryTruncation n,
        suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticBoundaryIntegrand
          x tau (-selectedLaplaceSeparatedLeftBoundary n) y := by
  have hbu : -quantitativeSpectralBoundaryTruncation n ≤
      quantitativeSpectralBoundaryTruncation n := by
    linarith [quantitativeSpectralBoundaryTruncation_nonneg n]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le hbu] at hy
  apply
    suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand_eq_pairedEtaArithmetic
  · linarith [(selectedLaplaceReflectedLeftBoundary_spec n).1]
  · exact (selectedLaplaceReflectedLeftBoundary_spec n).2
  · exact riemannXi_shifted_reflectedLeftBoundary_ne_zero n
      (abs_le.mpr hy)

/-- On every reflected positive-half-strip rectangle, the xi-log-norm
gradient pairing and paired-eta arithmetic pairing agree almost everywhere;
the only excluded points form the explicit finite xi-zero window. -/
theorem ae_suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradient_eq_pairedEtaArithmetic_positiveHalfStrip
    (x tau : ℝ) (n : ℕ) :
    ∀ᵐ p : ℂ ∂volume.restrict
      ([[-selectedLaplaceSeparatedRightBoundary n,
          -selectedLaplaceSeparatedLeftBoundary n]] ×ℂ
        [[-quantitativeSpectralBoundaryTruncation n,
          quantitativeSpectralBoundaryTruncation n]]),
      suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
          x tau p.re p.im =
        suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticGradientIntegrand
          x tau p.re p.im := by
  let l : ℝ := -selectedLaplaceSeparatedRightBoundary n
  let r : ℝ := -selectedLaplaceSeparatedLeftBoundary n
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let R : Set ℂ := [[l, r]] ×ℂ [[-T, T]]
  let W : Finset ℂ := suzukiChebyshevLaplaceZeroWindow T
  have hlr : l ≤ r := by
    dsimp only [l, r]
    linarith [selectedLaplaceSeparatedLeftBoundary_lt_rightBoundary n]
  have hbu : -T ≤ T := by
    linarith [quantitativeSpectralBoundaryTruncation_nonneg n]
  have hT0 : 0 ≤ T := by
    exact quantitativeSpectralBoundaryTruncation_nonneg n
  have hRmeas : MeasurableSet R :=
    (isCompact_uIcc.reProdIm isCompact_uIcc).measurableSet
  have hWnull : (volume.restrict R) (W : Set ℂ) = 0 :=
    W.measure_zero (volume.restrict R)
  have havoid : ∀ᵐ p : ℂ ∂volume.restrict R, p ∉ (W : Set ℂ) :=
    measure_eq_zero_iff_ae_notMem.mp hWnull
  change ∀ᵐ p : ℂ ∂volume.restrict R, _
  filter_upwards [ae_restrict_mem hRmeas, havoid] with p hpR hpW
  have hpR' : p.re ∈ [[l, r]] ∧ p.im ∈ [[-T, T]] := hpR
  rw [uIcc_of_le hlr, uIcc_of_le hbu] at hpR'
  have him : |p.im| ≤ T := abs_le.mpr hpR'.2
  have hpzero : riemannXi (p + 1 / 2) ≠ 0 := by
    intro hzero
    apply hpW
    exact (mem_suzukiChebyshevLaplaceZeroWindow_iff hT0 p).mpr
      ⟨hzero, him⟩
  have hpcoord :
      (((p.re + 1 / 2 : ℝ) : ℂ) + (p.im : ℂ) * Complex.I) =
        p + 1 / 2 := by
    apply Complex.ext <;> simp
  have ha0 : 0 < p.re := by
    exact (selectedLaplaceReflectedRightBoundary_spec n).1.trans_le hpR'.1.1
  have haHalf : p.re < 1 / 2 := by
    exact hpR'.1.2.trans_lt
      (selectedLaplaceReflectedLeftBoundary_spec n).2
  apply
    suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand_eq_pairedEtaArithmetic
      x tau ha0 haHalf
  rw [hpcoord]
  exact hpzero

/-- The paired-eta arithmetic heat-gradient pairing is genuinely planar
integrable on each selected positive-half-strip rectangle despite its finite
xi divisor. -/
theorem integrableOn_suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticGradient_positiveHalfStrip
    (x tau : ℝ) (n : ℕ) :
    IntegrableOn (fun p : ℂ =>
      suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticGradientIntegrand
        x tau p.re p.im)
      ([[-selectedLaplaceSeparatedRightBoundary n,
          -selectedLaplaceSeparatedLeftBoundary n]] ×ℂ
        [[-quantitativeSpectralBoundaryTruncation n,
          quantitativeSpectralBoundaryTruncation n]]) volume := by
  apply
    (integrableOn_suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradient_positiveHalfStrip
      x tau n).congr
  filter_upwards [
    ae_suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradient_eq_pairedEtaArithmetic_positiveHalfStrip
      x tau n] with p hp
  exact hp

/-- The ordinary planar xi-log-norm gradient integral on each selected
positive-half-strip rectangle is exactly its paired-eta arithmetic integral. -/
theorem integral_suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradient_eq_pairedEtaArithmetic_positiveHalfStrip
    (x tau : ℝ) (n : ℕ) :
    (∫ p : ℂ in
        ([[-selectedLaplaceSeparatedRightBoundary n,
            -selectedLaplaceSeparatedLeftBoundary n]] ×ℂ
          [[-quantitativeSpectralBoundaryTruncation n,
            quantitativeSpectralBoundaryTruncation n]]),
      suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
        x tau p.re p.im) =
      ∫ p : ℂ in
        ([[-selectedLaplaceSeparatedRightBoundary n,
            -selectedLaplaceSeparatedLeftBoundary n]] ×ℂ
          [[-quantitativeSpectralBoundaryTruncation n,
            quantitativeSpectralBoundaryTruncation n]]),
        suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticGradientIntegrand
          x tau p.re p.im := by
  apply MeasureTheory.integral_congr_ae
  exact
    ae_suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradient_eq_pairedEtaArithmetic_positiveHalfStrip
      x tau n

/-- The selected positive-half-strip detector functional written entirely
through the paired-eta arithmetic xi logarithmic derivative. -/
def separatedSelectedLaplacePairedEtaArithmeticPositiveHalfStripGradientScalarHeat
    (x tau : ℝ) (n : ℕ) : ℝ :=
  (∫ y : ℝ in -quantitativeSpectralBoundaryTruncation n..
      quantitativeSpectralBoundaryTruncation n,
    suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticBoundaryIntegrand
      x tau (-selectedLaplaceSeparatedRightBoundary n) y) -
  (∫ y : ℝ in -quantitativeSpectralBoundaryTruncation n..
      quantitativeSpectralBoundaryTruncation n,
    suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticBoundaryIntegrand
      x tau (-selectedLaplaceSeparatedLeftBoundary n) y) +
  ∫ p : ℂ in
    ([[-selectedLaplaceSeparatedRightBoundary n,
        -selectedLaplaceSeparatedLeftBoundary n]] ×ℂ
      [[-quantitativeSpectralBoundaryTruncation n,
        quantitativeSpectralBoundaryTruncation n]]),
    suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticGradientIntegrand
      x tau p.re p.im

/-- At every finite stage, the live positive-strip xi-log-norm gradient
functional is exactly the paired-eta arithmetic functional. -/
theorem separatedSelectedLaplaceXiLogNormPositiveHalfStripGradientScalarHeat_eq_pairedEtaArithmetic
    (x tau : ℝ) (n : ℕ) :
    separatedSelectedLaplaceXiLogNormPositiveHalfStripGradientScalarHeat
        x tau n =
      separatedSelectedLaplacePairedEtaArithmeticPositiveHalfStripGradientScalarHeat
        x tau n := by
  unfold
    separatedSelectedLaplaceXiLogNormPositiveHalfStripGradientScalarHeat
    separatedSelectedLaplacePairedEtaArithmeticPositiveHalfStripGradientScalarHeat
  rw [
    intervalIntegral_suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundary_eq_pairedEtaArithmetic_reflectedRight,
    intervalIntegral_suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundary_eq_pairedEtaArithmetic_reflectedLeft,
    integral_suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradient_eq_pairedEtaArithmetic_positiveHalfStrip]

/-- The entirely paired-eta arithmetic positive-strip functional retains the
unnormalized limit to `2 * pi` times the complete nonnegative RH detector. -/
theorem tendsto_separatedSelectedLaplacePairedEtaArithmeticPositiveHalfStripGradientScalarHeat
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (separatedSelectedLaplacePairedEtaArithmeticPositiveHalfStripGradientScalarHeat
        x tau) atTop
      (𝓝 (2 * Real.pi *
        riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) := by
  have hlimit :=
    tendsto_separatedSelectedLaplaceXiLogNormPositiveHalfStripGradientScalarHeat
      x htau
  apply hlimit.congr'
  exact Eventually.of_forall fun n =>
    separatedSelectedLaplaceXiLogNormPositiveHalfStripGradientScalarHeat_eq_pairedEtaArithmetic
      x tau n

end
end RiemannGaussian
