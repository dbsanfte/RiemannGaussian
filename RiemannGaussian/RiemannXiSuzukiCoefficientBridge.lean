import RiemannGaussian.RiemannXiScrewResolventConvolution

/-!
# From Suzuki's screw coefficient to the finite resolvent mode

Suzuki's unconditional zero expansion for the arithmetic screw-line function
uses the coefficient

`(exp (-i * alpha * t) - 1) / alpha`.

This file defines that coefficient with its removable value `-i*t` at
`alpha = 0` and proves its real-time derivative is exactly the raw screw mode
`-i * exp (-i * alpha * t)`.  Exponentially convolving this derivative over
future time gives `-i` times the first-order resolvent mode.  Consequently,
the height-weighted coordinate of the finite RH-detecting Hilbert vector is
an exact scalar multiple of the future convolution of the derivative of
Suzuki's published coefficient.

This is a coefficient-level identity and is unconditional.  The next larger
step is to formalize Suzuki's arithmetic `L²` function `S_t`, its zero functions,
and their unconditional expansion, so this identity can be lifted from each
coefficient to the actual arithmetic Hilbert-space signal.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- Suzuki's spectral screw-line coefficient, continuously extended at the
removable point `alpha = 0`. -/
def suzukiSpectralScrewCoefficient
    (t : ℝ) (alpha : ℂ) : ℂ :=
  if alpha = 0 then
    -Complex.I * (t : ℂ)
  else
    (spectralScrewExponential t alpha - 1) / alpha

/-- The removable value of Suzuki's coefficient at zero spectral frequency. -/
@[simp] theorem suzukiSpectralScrewCoefficient_zero (t : ℝ) :
    suzukiSpectralScrewCoefficient t 0 = -Complex.I * (t : ℂ) := by
  simp [suzukiSpectralScrewCoefficient]

/-- Away from zero, the extended definition is the usual exponential-difference
quotient. -/
theorem suzukiSpectralScrewCoefficient_of_ne_zero
    (t : ℝ) {alpha : ℂ} (halpha : alpha ≠ 0) :
    suzukiSpectralScrewCoefficient t alpha =
      (spectralScrewExponential t alpha - 1) / alpha := by
  rw [suzukiSpectralScrewCoefficient, if_neg halpha]

/-- Multiplying by the spectral frequency and adding one recovers the raw
screw exponential, including at zero frequency. -/
theorem alpha_mul_suzukiSpectralScrewCoefficient_add_one
    (t : ℝ) (alpha : ℂ) :
    alpha * suzukiSpectralScrewCoefficient t alpha + 1 =
      spectralScrewExponential t alpha := by
  by_cases halpha : alpha = 0
  · subst alpha
    simp [spectralScrewExponential]
  · rw [suzukiSpectralScrewCoefficient_of_ne_zero t halpha]
    field_simp [halpha]
    ring

/-- The raw derivative mode of Suzuki's spectral screw coefficient. -/
def suzukiSpectralScrewCoefficientDerivative
    (t : ℝ) (alpha : ℂ) : ℂ :=
  -Complex.I * spectralScrewExponential t alpha

/-- Suzuki's extended coefficient has the raw screw exponential as its exact
real-time derivative at every spectral frequency. -/
theorem hasDerivAt_suzukiSpectralScrewCoefficient
    (t : ℝ) (alpha : ℂ) :
    HasDerivAt (fun u : ℝ ↦
      suzukiSpectralScrewCoefficient u alpha)
      (suzukiSpectralScrewCoefficientDerivative t alpha) t := by
  by_cases halpha : alpha = 0
  · subst alpha
    simp only [suzukiSpectralScrewCoefficient_zero]
    unfold suzukiSpectralScrewCoefficientDerivative
      spectralScrewExponential
    norm_num
    have hbase :=
      ((hasDerivAt_id (t : ℂ)).const_mul (-Complex.I)).comp_ofReal
    convert hbase using 1 <;> simp
  · have hinner : HasDerivAt
        (fun u : ℝ ↦ -Complex.I * alpha * (u : ℂ))
        (-Complex.I * alpha) t := by
      simpa only [mul_one] using!
        ((hasDerivAt_id (t : ℂ)).const_mul
          (-Complex.I * alpha)).comp_ofReal
    have hexp := (Complex.hasDerivAt_exp _).comp t hinner
    have hquot := (hexp.sub_const 1).div_const alpha
    rw [show (fun u : ℝ ↦
        suzukiSpectralScrewCoefficient u alpha) =
        fun u : ℝ ↦
          (Complex.exp (-Complex.I * alpha * (u : ℂ)) - 1) /
            alpha by
      funext u
      rw [suzukiSpectralScrewCoefficient_of_ne_zero u halpha]
      rfl]
    apply hquot.congr_deriv
    unfold suzukiSpectralScrewCoefficientDerivative
      spectralScrewExponential
    field_simp [halpha]

/-- The squared modulus of the coefficient derivative records twice the upper
spectral height in its exponential rate. -/
theorem normSq_suzukiSpectralScrewCoefficientDerivative
    (t : ℝ) (alpha : ℂ) :
    Complex.normSq
      (suzukiSpectralScrewCoefficientDerivative t alpha) =
      Real.exp (2 * alpha.im * t) := by
  unfold suzukiSpectralScrewCoefficientDerivative
  rw [Complex.normSq_mul, normSq_spectralScrewExponential]
  norm_num

/-- Exponential future convolution of Suzuki's coefficient derivative is
`-i` times the first-order spectral resolvent mode. -/
theorem integral_suzukiSpectralScrewCoefficientDerivative_future
    (t : ℝ) (rho : NontrivialZetaZero) :
    (∫ s : ℝ in Ioi 0,
      (Real.exp (-s) : ℂ) *
        suzukiSpectralScrewCoefficientDerivative (t + s)
          (zetaSpectralCoordinate rho.1)) =
      -Complex.I *
        complexSpectralScrewResolventMode (t : ℂ)
          (zetaSpectralCoordinate rho.1) := by
  rw [← integral_spectralScrewFutureConvolutionIntegrand t rho,
    ← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  unfold suzukiSpectralScrewCoefficientDerivative
    spectralScrewFutureConvolutionIntegrand
  ring

/-- Each coordinate of the finite resolvent screw Hilbert vector is exactly a
height amplitude times the future convolution of Suzuki's coefficient
derivative. -/
theorem zetaUpperResolventScrewFeature_eq_suzukiCoefficientDerivativeConvolution
    (t : ℝ) (rho : NontrivialZetaZero) :
    zetaUpperResolventScrewFeature t rho =
      Complex.I *
        (Real.sqrt (zetaUpperSpectralHeightSummand rho) : ℂ) *
          ∫ s : ℝ in Ioi 0,
            (Real.exp (-s) : ℂ) *
              suzukiSpectralScrewCoefficientDerivative (t + s)
                (zetaSpectralCoordinate rho.1) := by
  rw [integral_suzukiSpectralScrewCoefficientDerivative_future,
    zetaUpperResolventScrewFeature_eq_resolventMode]
  ring_nf
  rw [Complex.I_sq]
  ring

end

end RiemannGaussian
