import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaXiGradient

/-!
# Denominator geometry and energy of the paired-eta xi field

The live positive-strip detector is now represented by the convergent paired
eta series. This module exposes the precise nonlinear obstruction in that
representation. Write `E(s)` for paired eta and `D(s)` for the sum of its
explicit differentiated series. The singular logarithmic-gradient vector is

`(Re (D * conj E) / |E|^2, Im (D * conj E) / |E|^2)`.

Lean proves that its denominator vanishes exactly on the xi divisor in
`1 / 2 < re s < 1`, that its numerator has the exact squared norm
`|D|^2 * |E|^2`, and that the squared magnitude of `D / E` is the nonnegative
density `|D|^2 / |E|^2`. It also differentiates `|E|^2` in both detector
coordinates, identifying the two bilinear numerators as its exact gradient.

Finally, the paired-eta detector field is split pointwise into this normalized
singular field and a completely explicit completion/factor correction. This
does not estimate either piece. Division is totalized by Lean at a zero, so
the pointwise energy density is zero there; the actual zero contribution is
retained by the almost-everywhere integral and distributional frontier from
the preceding module. No integrability claim for the squared energy density
is made here.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The value of the rigorously summable differentiated paired-eta series. -/
def pairedEtaArithmeticDerivativeValue (s : ℂ) : ℂ :=
  ∑' n : ℕ, pairedEtaCoreDerivativeSummand s n

/-- The squared modulus of the paired-eta denominator. -/
def pairedEtaCoreNormSq (s : ℂ) : ℝ :=
  Complex.normSq (pairedEtaCore s)

/-- The real bilinear numerator of the paired-eta logarithmic derivative. -/
def pairedEtaLogDerivativeRealNumerator (s : ℂ) : ℝ :=
  (pairedEtaArithmeticDerivativeValue s *
    starRingEnd ℂ (pairedEtaCore s)).re

/-- The imaginary bilinear numerator of the paired-eta logarithmic
derivative. -/
def pairedEtaLogDerivativeImaginaryNumerator (s : ℂ) : ℝ :=
  (pairedEtaArithmeticDerivativeValue s *
    starRingEnd ℂ (pairedEtaCore s)).im

/-- The totalized squared magnitude of the paired-eta logarithmic derivative. -/
def pairedEtaLogDerivativeEnergyDensity (s : ℂ) : ℝ :=
  Complex.normSq (pairedEtaArithmeticDerivativeValue s) /
    pairedEtaCoreNormSq s

/-- The real component of the paired-eta quotient is its real bilinear
numerator divided by the squared denominator modulus. -/
theorem pairedEtaArithmeticQuotient_re (s : ℂ) :
    (pairedEtaArithmeticDerivativeValue s / pairedEtaCore s).re =
      pairedEtaLogDerivativeRealNumerator s / pairedEtaCoreNormSq s := by
  unfold pairedEtaCoreNormSq pairedEtaLogDerivativeRealNumerator
  rw [Complex.div_re]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The imaginary component of the paired-eta quotient is its imaginary
bilinear numerator divided by the squared denominator modulus. -/
theorem pairedEtaArithmeticQuotient_im (s : ℂ) :
    (pairedEtaArithmeticDerivativeValue s / pairedEtaCore s).im =
      pairedEtaLogDerivativeImaginaryNumerator s / pairedEtaCoreNormSq s := by
  unfold pairedEtaCoreNormSq pairedEtaLogDerivativeImaginaryNumerator
  rw [Complex.div_im]
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- In the positive critical half-strip, the squared paired-eta denominator
vanishes exactly on the genuine xi divisor. -/
theorem pairedEtaCoreNormSq_eq_zero_iff_riemannXi_eq_zero
    {s : ℂ} (hlower : 1 / 2 < s.re) (hupper : s.re < 1) :
    pairedEtaCoreNormSq s = 0 ↔ riemannXi s = 0 := by
  rw [pairedEtaCoreNormSq, Complex.normSq_eq_zero,
    pairedEtaCore_eq_zero_iff_riemannZeta_eq_zero_of_half_lt_re_of_re_lt_one
      hlower hupper]
  constructor
  · intro hzeta
    have hsone : s ≠ 1 := by
      intro h
      subst s
      norm_num at hupper
    rw [riemannXi_eq_mul_Gammaℝ_riemannZeta_of_re_pos
      (by linarith) hsone, hzeta]
    simp
  · intro hxi
    exact (isNontrivialZetaZero_of_riemannXi_eq_zero hxi).1

/-- Away from the xi divisor in the positive critical half-strip, the
paired-eta squared denominator is strictly positive. -/
theorem pairedEtaCoreNormSq_pos_of_riemannXi_ne_zero
    {s : ℂ} (hlower : 1 / 2 < s.re) (hupper : s.re < 1)
    (hxi : riemannXi s ≠ 0) :
    0 < pairedEtaCoreNormSq s := by
  rw [pairedEtaCoreNormSq, Complex.normSq_pos]
  intro heta
  apply hxi
  exact (pairedEtaCoreNormSq_eq_zero_iff_riemannXi_eq_zero
    hlower hupper).mp (Complex.normSq_eq_zero.mpr heta)

/-- The two bilinear eta numerators have exact squared magnitude
`|D|^2 * |E|^2`. -/
theorem pairedEtaLogDerivativeNumerator_sq_add_sq
    (s : ℂ) :
    (pairedEtaLogDerivativeRealNumerator s) ^ 2 +
        (pairedEtaLogDerivativeImaginaryNumerator s) ^ 2 =
      Complex.normSq (pairedEtaArithmeticDerivativeValue s) *
        pairedEtaCoreNormSq s := by
  rw [sq, sq]
  unfold pairedEtaLogDerivativeRealNumerator
    pairedEtaLogDerivativeImaginaryNumerator
  rw [← Complex.normSq_apply]
  unfold pairedEtaCoreNormSq
  rw [Complex.normSq_mul, Complex.normSq_conj]

/-- The squared Euclidean magnitude of the totalized quotient vector is the
eta energy density. -/
theorem pairedEtaArithmeticQuotient_re_sq_add_im_sq
    (s : ℂ) :
    ((pairedEtaArithmeticDerivativeValue s / pairedEtaCore s).re) ^ 2 +
        ((pairedEtaArithmeticDerivativeValue s / pairedEtaCore s).im) ^ 2 =
      pairedEtaLogDerivativeEnergyDensity s := by
  rw [sq, sq, ← Complex.normSq_apply, Complex.normSq_div]
  rfl

/-- The squared Euclidean magnitude of the normalized bilinear eta vector is
the eta energy density. -/
theorem pairedEtaNormalizedNumerator_sq_add_sq
    (s : ℂ) :
    (pairedEtaLogDerivativeRealNumerator s / pairedEtaCoreNormSq s) ^ 2 +
        (pairedEtaLogDerivativeImaginaryNumerator s /
          pairedEtaCoreNormSq s) ^ 2 =
      pairedEtaLogDerivativeEnergyDensity s := by
  rw [← pairedEtaArithmeticQuotient_re,
    ← pairedEtaArithmeticQuotient_im,
    pairedEtaArithmeticQuotient_re_sq_add_im_sq]

/-- The totalized paired-eta logarithmic-derivative energy density is
nonnegative everywhere. -/
theorem pairedEtaLogDerivativeEnergyDensity_nonneg (s : ℂ) :
    0 ≤ pairedEtaLogDerivativeEnergyDensity s := by
  rw [← pairedEtaArithmeticQuotient_re_sq_add_im_sq]
  positivity

/-- If the squared eta denominator vanishes, its real bilinear numerator also
vanishes; this records Lean's pointwise totalization at the divisor. -/
theorem pairedEtaLogDerivativeRealNumerator_eq_zero_of_coreNormSq_eq_zero
    {s : ℂ} (hzero : pairedEtaCoreNormSq s = 0) :
    pairedEtaLogDerivativeRealNumerator s = 0 := by
  have heta : pairedEtaCore s = 0 :=
    Complex.normSq_eq_zero.mp (by simpa [pairedEtaCoreNormSq] using hzero)
  simp [pairedEtaLogDerivativeRealNumerator, heta]

/-- If the squared eta denominator vanishes, its imaginary bilinear numerator
also vanishes; singular zero mass is therefore not a pointwise quotient
value. -/
theorem pairedEtaLogDerivativeImaginaryNumerator_eq_zero_of_coreNormSq_eq_zero
    {s : ℂ} (hzero : pairedEtaCoreNormSq s = 0) :
    pairedEtaLogDerivativeImaginaryNumerator s = 0 := by
  have heta : pairedEtaCore s = 0 :=
    Complex.normSq_eq_zero.mp (by simpa [pairedEtaCoreNormSq] using hzero)
  simp [pairedEtaLogDerivativeImaginaryNumerator, heta]

/-- The explicit elementary and Archimedean correction left after separating
the paired-eta logarithmic quotient from the completed xi field. -/
def pairedEtaArithmeticXiRegularCorrection (s : ℂ) : ℂ :=
  1 / s + 1 / (s - 1) - Complex.log Real.pi / 2 +
    Complex.digamma (s / 2) / 2 - pairedEtaFactorLogDerivative s

/-- The paired-eta arithmetic xi field is the singular eta quotient plus its
explicit completion/factor correction. -/
theorem pairedEtaArithmeticXiLogDerivative_eq_quotient_add_regularCorrection
    (s : ℂ) :
    pairedEtaArithmeticXiLogDerivative s =
      pairedEtaArithmeticDerivativeValue s / pairedEtaCore s +
        pairedEtaArithmeticXiRegularCorrection s := by
  unfold pairedEtaArithmeticXiLogDerivative
    pairedEtaArithmeticDerivativeValue
    pairedEtaArithmeticXiRegularCorrection
  ring

/-- The real component of the paired-eta arithmetic xi field is the
normalized real bilinear numerator plus the explicit correction. -/
theorem pairedEtaArithmeticXiLogDerivative_re
    (s : ℂ) :
    (pairedEtaArithmeticXiLogDerivative s).re =
      pairedEtaLogDerivativeRealNumerator s / pairedEtaCoreNormSq s +
        (pairedEtaArithmeticXiRegularCorrection s).re := by
  rw [pairedEtaArithmeticXiLogDerivative_eq_quotient_add_regularCorrection,
    Complex.add_re, pairedEtaArithmeticQuotient_re]

/-- The imaginary component of the paired-eta arithmetic xi field is the
normalized imaginary bilinear numerator plus the explicit correction. -/
theorem pairedEtaArithmeticXiLogDerivative_im
    (s : ℂ) :
    (pairedEtaArithmeticXiLogDerivative s).im =
      pairedEtaLogDerivativeImaginaryNumerator s / pairedEtaCoreNormSq s +
        (pairedEtaArithmeticXiRegularCorrection s).im := by
  rw [pairedEtaArithmeticXiLogDerivative_eq_quotient_add_regularCorrection,
    Complex.add_im, pairedEtaArithmeticQuotient_im]

/-- The convergent differentiated eta series gives the genuine complex
derivative of paired eta throughout the positive half-plane. -/
theorem hasDerivAt_pairedEtaCore_arithmeticDerivativeValue
    {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt pairedEtaCore (pairedEtaArithmeticDerivativeValue s) s := by
  have hdiff : DifferentiableAt ℂ pairedEtaCore s :=
    (analyticOnNhd_pairedEtaCore s hs).differentiableAt
  have h := hdiff.hasDerivAt
  rw [← (hasSum_pairedEtaCoreDerivativeSummand_deriv hs).tsum_eq] at h
  simpa [pairedEtaArithmeticDerivativeValue] using h

/-- The squared paired-eta denominator in shifted detector coordinates. -/
def shiftedPairedEtaCoreNormSq (a y : ℝ) : ℝ :=
  pairedEtaCoreNormSq
    (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)

/-- The real eta bilinear numerator in shifted detector coordinates. -/
def shiftedPairedEtaLogDerivativeRealNumerator (a y : ℝ) : ℝ :=
  pairedEtaLogDerivativeRealNumerator
    (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)

/-- The imaginary eta bilinear numerator in shifted detector coordinates. -/
def shiftedPairedEtaLogDerivativeImaginaryNumerator (a y : ℝ) : ℝ :=
  pairedEtaLogDerivativeImaginaryNumerator
    (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)

/-- The paired-eta logarithmic-derivative energy density in shifted detector
coordinates. -/
def shiftedPairedEtaLogDerivativeEnergyDensity (a y : ℝ) : ℝ :=
  pairedEtaLogDerivativeEnergyDensity
    (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)

/-- The explicit completion/factor correction in shifted detector
coordinates. -/
def shiftedPairedEtaArithmeticXiRegularCorrection (a y : ℝ) : ℂ :=
  pairedEtaArithmeticXiRegularCorrection
    (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)

/-- The horizontal derivative of `|E|^2` is twice the real bilinear eta
numerator. This remains valid at an eta zero. -/
theorem hasDerivAt_shiftedPairedEtaCoreNormSq_realCoordinate
    {a y : ℝ} (ha : -(1 / 2) < a) :
    HasDerivAt (fun u : ℝ => shiftedPairedEtaCoreNormSq u y)
      (2 * shiftedPairedEtaLogDerivativeRealNumerator a y) a := by
  let s : ℂ := (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
  let g : ℝ → ℂ := fun u =>
    pairedEtaCore (((u + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
  let affine : ℂ → ℂ := fun z => z + 1 / 2 + (y : ℂ) * Complex.I
  have hs : 0 < s.re := by
    dsimp [s]
    simp
    linarith
  have haffine : HasDerivAt affine 1 (a : ℂ) := by
    simpa [affine] using
      ((hasDerivAt_id (𝕜 := ℂ) (a : ℂ)).add_const (1 / 2)).add_const
        ((y : ℂ) * Complex.I)
  have hsAffine : affine (a : ℂ) = s := by
    dsimp [affine, s]
    push_cast
    ring
  have hcomp : HasDerivAt (pairedEtaCore ∘ affine)
      (pairedEtaArithmeticDerivativeValue s) (a : ℂ) := by
    have heta := hasDerivAt_pairedEtaCore_arithmeticDerivativeValue hs
    simpa only [mul_one] using
      heta.comp_of_eq (a : ℂ) haffine hsAffine.symm
  have hreal := hcomp.comp_ofReal
  have hg : HasDerivAt g (pairedEtaArithmeticDerivativeValue s) a := by
    simpa [g, affine] using hreal
  have hnorm := hg.norm_sq
  convert hnorm using 1
  · funext u
    simp [shiftedPairedEtaCoreNormSq, pairedEtaCoreNormSq, g,
      Complex.normSq_eq_norm_sq]
  · simp only [Complex.inner,
      shiftedPairedEtaLogDerivativeRealNumerator,
      pairedEtaLogDerivativeRealNumerator, g, s, Complex.mul_re,
      Complex.conj_re, Complex.conj_im]

/-- The vertical derivative of `|E|^2` is minus twice the imaginary bilinear
eta numerator. This remains valid at an eta zero. -/
theorem hasDerivAt_shiftedPairedEtaCoreNormSq_imaginaryCoordinate
    {a y : ℝ} (ha : -(1 / 2) < a) :
    HasDerivAt (shiftedPairedEtaCoreNormSq a)
      (-2 * shiftedPairedEtaLogDerivativeImaginaryNumerator a y) y := by
  let s : ℂ := (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
  let g : ℝ → ℂ := fun v =>
    pairedEtaCore (((a + 1 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I)
  let affine : ℂ → ℂ := fun z =>
    (((a + 1 / 2 : ℝ) : ℂ) + z * Complex.I)
  have hs : 0 < s.re := by
    dsimp [s]
    simp
    linarith
  have haffine : HasDerivAt affine Complex.I (y : ℂ) := by
    simpa [affine] using
      ((hasDerivAt_id (𝕜 := ℂ) (y : ℂ)).mul_const Complex.I).const_add
        (((a + 1 / 2 : ℝ) : ℂ))
  have hsAffine : affine (y : ℂ) = s := rfl
  have hcomp : HasDerivAt (pairedEtaCore ∘ affine)
      (pairedEtaArithmeticDerivativeValue s * Complex.I) (y : ℂ) := by
    have heta := hasDerivAt_pairedEtaCore_arithmeticDerivativeValue hs
    exact heta.comp_of_eq (y : ℂ) haffine hsAffine.symm
  have hreal := hcomp.comp_ofReal
  have hg : HasDerivAt g
      (pairedEtaArithmeticDerivativeValue s * Complex.I) y := by
    simpa [g, affine] using hreal
  have hnorm := hg.norm_sq
  convert hnorm using 1
  · funext v
    simp [shiftedPairedEtaCoreNormSq, pairedEtaCoreNormSq, g,
      Complex.normSq_eq_norm_sq]
  · simp only [Complex.inner,
      shiftedPairedEtaLogDerivativeImaginaryNumerator,
      pairedEtaLogDerivativeImaginaryNumerator, g, s, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.I_re,
      Complex.I_im]
    ring

/-- In the detector's positive shifted half-strip, the squared eta
denominator vanishes exactly on the corresponding xi divisor. -/
theorem shiftedPairedEtaCoreNormSq_eq_zero_iff_riemannXi_eq_zero
    {a y : ℝ} (ha0 : 0 < a) (haHalf : a < 1 / 2) :
    shiftedPairedEtaCoreNormSq a y = 0 ↔
      riemannXi
        (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) = 0 := by
  apply pairedEtaCoreNormSq_eq_zero_iff_riemannXi_eq_zero
  · simp
    linarith
  · simp
    linarith

/-- Off the xi divisor in positive shifted coordinates, the squared eta
denominator is strictly positive. -/
theorem shiftedPairedEtaCoreNormSq_pos_of_riemannXi_ne_zero
    {a y : ℝ} (ha0 : 0 < a) (haHalf : a < 1 / 2)
    (hxi : riemannXi
      (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) ≠ 0) :
    0 < shiftedPairedEtaCoreNormSq a y := by
  apply pairedEtaCoreNormSq_pos_of_riemannXi_ne_zero
  · simp
    linarith
  · simp
    linarith
  · exact hxi

/-- The singular eta boundary field: the heat kernel times the normalized
real bilinear numerator. -/
def suzukiChebyshevLaplaceBoundaryHeatPairedEtaSingularBoundaryIntegrand
    (x tau a y : ℝ) : ℝ :=
  suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau a y *
    (shiftedPairedEtaLogDerivativeRealNumerator a y /
      shiftedPairedEtaCoreNormSq a y)

/-- The explicit regular-correction contribution to the eta boundary field. -/
def suzukiChebyshevLaplaceBoundaryHeatPairedEtaRegularBoundaryIntegrand
    (x tau a y : ℝ) : ℝ :=
  suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau a y *
    (shiftedPairedEtaArithmeticXiRegularCorrection a y).re

/-- The heat-gradient pairing with the normalized singular eta vector field. -/
def suzukiChebyshevLaplaceBoundaryHeatPairedEtaSingularGradientIntegrand
    (x tau a y : ℝ) : ℝ :=
  deriv (fun u : ℝ =>
    suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau u y) a *
      (shiftedPairedEtaLogDerivativeRealNumerator a y /
        shiftedPairedEtaCoreNormSq a y) -
    deriv (fun v : ℝ =>
      suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau a v) y *
      (shiftedPairedEtaLogDerivativeImaginaryNumerator a y /
        shiftedPairedEtaCoreNormSq a y)

/-- The heat-gradient pairing with the explicit completion/factor correction. -/
def suzukiChebyshevLaplaceBoundaryHeatPairedEtaRegularGradientIntegrand
    (x tau a y : ℝ) : ℝ :=
  deriv (fun u : ℝ =>
    suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau u y) a *
      (shiftedPairedEtaArithmeticXiRegularCorrection a y).re -
    deriv (fun v : ℝ =>
      suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau a v) y *
      (shiftedPairedEtaArithmeticXiRegularCorrection a y).im

/-- The squared Euclidean magnitude of the real heat-kernel gradient. -/
def suzukiChebyshevLaplaceBoundaryHeatRealKernelGradientEnergyDensity
    (x tau a y : ℝ) : ℝ :=
  (deriv (fun u : ℝ =>
    suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau u y) a) ^ 2 +
  (deriv (fun v : ℝ =>
    suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau a v) y) ^ 2

/-- The heat-kernel gradient energy density is nonnegative. -/
theorem suzukiChebyshevLaplaceBoundaryHeatRealKernelGradientEnergyDensity_nonneg
    (x tau a y : ℝ) :
    0 ≤
      suzukiChebyshevLaplaceBoundaryHeatRealKernelGradientEnergyDensity
        x tau a y := by
  unfold suzukiChebyshevLaplaceBoundaryHeatRealKernelGradientEnergyDensity
  positivity

/-- The heat-gradient energy has an explicit Gaussian-polynomial form. -/
theorem suzukiChebyshevLaplaceBoundaryHeatRealKernelGradientEnergyDensity_eq
    (x tau a y : ℝ) :
    suzukiChebyshevLaplaceBoundaryHeatRealKernelGradientEnergyDensity
        x tau a y =
      4 * (Real.exp (-tau * ((x - y) ^ 2 + a ^ 2))) ^ 2 *
        ((2 * tau * a ^ 2 - 1) ^ 2 +
          (2 * tau * a * (x - y)) ^ 2) := by
  unfold suzukiChebyshevLaplaceBoundaryHeatRealKernelGradientEnergyDensity
  rw [(hasDerivAt_suzukiChebyshevLaplaceBoundaryHeatRealKernel_realCoordinate
      x tau a y).deriv,
    (hasDerivAt_suzukiChebyshevLaplaceBoundaryHeatRealKernel_imaginaryCoordinate
      x tau a y).deriv]
  ring

/-- Pointwise Cauchy--Schwarz controls the square of the singular eta
heat-gradient pairing by the heat-gradient energy times the eta energy. No
claim is made that the eta energy is integrable through its divisor. -/
theorem sq_suzukiChebyshevLaplaceBoundaryHeatPairedEtaSingularGradientIntegrand_le_energy
    (x tau a y : ℝ) :
    (suzukiChebyshevLaplaceBoundaryHeatPairedEtaSingularGradientIntegrand
      x tau a y) ^ 2 ≤
      suzukiChebyshevLaplaceBoundaryHeatRealKernelGradientEnergyDensity
          x tau a y *
        shiftedPairedEtaLogDerivativeEnergyDensity a y := by
  let s : ℂ := (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
  let A : ℝ := deriv (fun u : ℝ =>
    suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau u y) a
  let B : ℝ := deriv (fun v : ℝ =>
    suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau a v) y
  let X : ℝ := shiftedPairedEtaLogDerivativeRealNumerator a y /
    shiftedPairedEtaCoreNormSq a y
  let Y : ℝ := shiftedPairedEtaLogDerivativeImaginaryNumerator a y /
    shiftedPairedEtaCoreNormSq a y
  have henergy : X ^ 2 + Y ^ 2 =
      shiftedPairedEtaLogDerivativeEnergyDensity a y := by
    simpa [X, Y, shiftedPairedEtaLogDerivativeEnergyDensity,
      shiftedPairedEtaLogDerivativeRealNumerator,
      shiftedPairedEtaLogDerivativeImaginaryNumerator,
      shiftedPairedEtaCoreNormSq, s] using
      pairedEtaNormalizedNumerator_sq_add_sq s
  have hsquare : 0 ≤ (A * Y + B * X) ^ 2 := sq_nonneg _
  change (A * X - B * Y) ^ 2 ≤ (A ^ 2 + B ^ 2) *
    shiftedPairedEtaLogDerivativeEnergyDensity a y
  rw [← henergy]
  nlinarith

/-- The full paired-eta arithmetic boundary integrand splits exactly into
its normalized singular and explicit regular pieces. -/
theorem suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticBoundaryIntegrand_eq_singular_add_regular
    (x tau a y : ℝ) :
    suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticBoundaryIntegrand
        x tau a y =
      suzukiChebyshevLaplaceBoundaryHeatPairedEtaSingularBoundaryIntegrand
          x tau a y +
        suzukiChebyshevLaplaceBoundaryHeatPairedEtaRegularBoundaryIntegrand
          x tau a y := by
  unfold
    suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticBoundaryIntegrand
    shiftedPairedEtaArithmeticXiLogDerivative
    suzukiChebyshevLaplaceBoundaryHeatPairedEtaSingularBoundaryIntegrand
    suzukiChebyshevLaplaceBoundaryHeatPairedEtaRegularBoundaryIntegrand
    shiftedPairedEtaLogDerivativeRealNumerator
    shiftedPairedEtaCoreNormSq
    shiftedPairedEtaArithmeticXiRegularCorrection
  rw [pairedEtaArithmeticXiLogDerivative_re]
  ring

/-- The full paired-eta arithmetic gradient integrand splits exactly into
its normalized singular and explicit regular pieces. -/
theorem suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticGradientIntegrand_eq_singular_add_regular
    (x tau a y : ℝ) :
    suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticGradientIntegrand
        x tau a y =
      suzukiChebyshevLaplaceBoundaryHeatPairedEtaSingularGradientIntegrand
          x tau a y +
        suzukiChebyshevLaplaceBoundaryHeatPairedEtaRegularGradientIntegrand
          x tau a y := by
  unfold
    suzukiChebyshevLaplaceBoundaryHeatPairedEtaArithmeticGradientIntegrand
    shiftedPairedEtaArithmeticXiLogDerivative
    suzukiChebyshevLaplaceBoundaryHeatPairedEtaSingularGradientIntegrand
    suzukiChebyshevLaplaceBoundaryHeatPairedEtaRegularGradientIntegrand
    shiftedPairedEtaLogDerivativeRealNumerator
    shiftedPairedEtaLogDerivativeImaginaryNumerator
    shiftedPairedEtaCoreNormSq
    shiftedPairedEtaArithmeticXiRegularCorrection
  rw [pairedEtaArithmeticXiLogDerivative_re,
    pairedEtaArithmeticXiLogDerivative_im]
  ring

end
end RiemannGaussian
