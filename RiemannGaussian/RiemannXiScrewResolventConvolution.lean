import RiemannGaussian.RiemannXiResolventScrewGrowth

/-!
# Resolvent screw modes as exponential future convolutions

This file gives the first-order screw resolvent a time-domain meaning.  For a
spectral coordinate `alpha` in the zeta critical strip, Lean proves

`exp(-i*alpha*t) / (1 + i*alpha)
  = integral_0^infinity exp(-s) * exp(-i*alpha*(t+s)) ds`.

After multiplication by the upper-height amplitude, this is exactly the
coordinate used by the finite resolvent screw Hilbert vector.  Thus the
regularization is not an ad hoc weight: it is exponential future smoothing
of the raw screw evolution.

A general Banach-valued estimate is also proved.  If a future convolution is
integrable and its input has an exponential norm bound of rate less than one,
the convolution has the same rate with the exact factor `1/(1-epsilon)`.
Consequently exponential future convolution preserves subexponential growth.
This supplies a checked operator through which a future arithmetic
Suzuki-screw estimate can reach the finite RH-detecting spectral norm; the
remaining task is to identify the required arithmetic input signal.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- The exponentially damped future translate of one raw spectral screw
mode. -/
def spectralScrewFutureConvolutionIntegrand
    (t : ℝ) (alpha : ℂ) (s : ℝ) : ℂ :=
  (Real.exp (-s) : ℂ) *
    spectralScrewExponential (t + s) alpha

/-- The future-convolution integrand factors into its value at the observation
time and a decaying resolvent exponential. -/
theorem spectralScrewFutureConvolutionIntegrand_eq
    (t : ℝ) (alpha : ℂ) (s : ℝ) :
    spectralScrewFutureConvolutionIntegrand t alpha s =
      spectralScrewExponential t alpha *
        Complex.exp
          (-spectralScrewResolventDenominator alpha * (s : ℂ)) := by
  unfold spectralScrewFutureConvolutionIntegrand
    spectralScrewExponential spectralScrewResolventDenominator
  rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The critical strip makes the resolvent exponential decay on positive
future time. -/
theorem neg_spectralScrewResolventDenominator_re_neg
    (rho : NontrivialZetaZero) :
    (-spectralScrewResolventDenominator
      (zetaSpectralCoordinate rho.1)).re < 0 := by
  have habs := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  rw [neg_re]
  have hre : (spectralScrewResolventDenominator
      (zetaSpectralCoordinate rho.1)).re =
      1 - (zetaSpectralCoordinate rho.1).im := by
    simp [spectralScrewResolventDenominator]
    ring
  rw [hre]
  nlinarith [le_abs_self (zetaSpectralCoordinate rho.1).im]

/-- Every nontrivial zeta coordinate has an integrable exponentially damped
future screw mode. -/
theorem integrableOn_spectralScrewFutureConvolutionIntegrand
    (t : ℝ) (rho : NontrivialZetaZero) :
    IntegrableOn
      (spectralScrewFutureConvolutionIntegrand t
        (zetaSpectralCoordinate rho.1)) (Ioi 0) := by
  have hbase := integrableOn_exp_mul_complex_Ioi
    (neg_spectralScrewResolventDenominator_re_neg rho) 0
  refine (hbase.const_mul
    (spectralScrewExponential t
      (zetaSpectralCoordinate rho.1))).congr ?_
  filter_upwards with s
  exact (spectralScrewFutureConvolutionIntegrand_eq t
    (zetaSpectralCoordinate rho.1) s).symm

/-- Exponential future convolution is exactly division by the first-order
spectral screw resolvent. -/
theorem integral_spectralScrewFutureConvolutionIntegrand
    (t : ℝ) (rho : NontrivialZetaZero) :
    (∫ s : ℝ in Ioi 0,
      spectralScrewFutureConvolutionIntegrand t
        (zetaSpectralCoordinate rho.1) s) =
      complexSpectralScrewResolventMode (t : ℂ)
        (zetaSpectralCoordinate rho.1) := by
  let alpha : ℂ := zetaSpectralCoordinate rho.1
  let a : ℂ := -spectralScrewResolventDenominator alpha
  have ha : a.re < 0 := by
    exact neg_spectralScrewResolventDenominator_re_neg rho
  have hfun : (fun s : ℝ ↦
      spectralScrewFutureConvolutionIntegrand t alpha s) =
      fun s : ℝ ↦ spectralScrewExponential t alpha *
        Complex.exp (a * (s : ℂ)) := by
    funext s
    rw [spectralScrewFutureConvolutionIntegrand_eq]
  rw [hfun, MeasureTheory.integral_const_mul,
    integral_exp_mul_complex_Ioi ha 0]
  simp [a, complexSpectralScrewResolventMode,
    spectralScrewExponential]
  dsimp [alpha]
  rfl

/-- The unregularized height-amplitude screw coordinate attached to one upper
zeta zero. -/
def zetaUpperRawScrewFeature
    (t : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  (Real.sqrt (zetaUpperSpectralHeightSummand rho) : ℂ) *
    spectralScrewExponential t (zetaSpectralCoordinate rho.1)

/-- The raw coordinate's squared modulus is its positive upper-height
exponential mode. -/
theorem normSq_zetaUpperRawScrewFeature
    (t : ℝ) (rho : NontrivialZetaZero) :
    Complex.normSq (zetaUpperRawScrewFeature t rho) =
      zetaUpperSpectralHeightSummand rho *
        Real.exp (2 * (zetaSpectralCoordinate rho.1).im * t) := by
  rw [zetaUpperRawScrewFeature, Complex.normSq_mul,
    Complex.normSq_ofReal,
    Real.mul_self_sqrt (zetaUpperSpectralHeightSummand_nonneg rho),
    normSq_spectralScrewExponential]

/-- A regularized zeta screw coordinate is the explicit complex integral of
the exponentially damped raw future coordinate. -/
theorem zetaUpperResolventScrewFeature_eq_futureConvolution
    (t : ℝ) (rho : NontrivialZetaZero) :
    zetaUpperResolventScrewFeature t rho =
      ∫ s : ℝ in Ioi 0,
        (Real.exp (-s) : ℂ) *
          zetaUpperRawScrewFeature (t + s) rho := by
  rw [zetaUpperResolventScrewFeature_eq_resolventMode,
    ← integral_spectralScrewFutureConvolutionIntegrand t rho,
    ← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  unfold spectralScrewFutureConvolutionIntegrand
    zetaUpperRawScrewFeature
  ring

section FutureConvolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exponentially weighted future convolution of a normed-space-valued
signal. -/
def futureExponentialConvolution (F : ℝ → E) (t : ℝ) : E :=
  ∫ s : ℝ in Ioi 0, Real.exp (-s) • F (t + s)

/-- The zeta resolvent coordinate is the specialization of the general future
convolution operator to its raw screw coordinate. -/
theorem zetaUpperResolventScrewFeature_eq_futureExponentialConvolution
    (t : ℝ) (rho : NontrivialZetaZero) :
    zetaUpperResolventScrewFeature t rho =
      futureExponentialConvolution
        (fun u : ℝ ↦ zetaUpperRawScrewFeature u rho) t := by
  rw [zetaUpperResolventScrewFeature_eq_futureConvolution]
  unfold futureExponentialConvolution
  apply integral_congr_ae
  filter_upwards with s
  simp only [Complex.real_smul]

/-- A rate-`epsilon < 1` input bound passes through exponential future
convolution with the exact resolvent factor `1 / (1 - epsilon)`. -/
theorem norm_futureExponentialConvolution_le_of_exponential
    {F : ℝ → E} {t C epsilon : ℝ}
    (ht : 0 ≤ t) (hepsilon : epsilon < 1)
    (hint : IntegrableOn
      (fun s : ℝ ↦ Real.exp (-s) • F (t + s)) (Ioi 0))
    (hF : ∀ u : ℝ, 0 ≤ u →
      ‖F u‖ ≤ C * Real.exp (epsilon * u)) :
    ‖futureExponentialConvolution F t‖ ≤
      (C * Real.exp (epsilon * t)) / (1 - epsilon) := by
  let D : ℝ := 1 - epsilon
  let A : ℝ := C * Real.exp (epsilon * t)
  have hD : 0 < D := by
    dsimp [D]
    linarith
  have hbase : IntegrableOn
      (fun s : ℝ ↦ Real.exp (-(D * s))) (Ioi 0) := by
    convert integrableOn_exp_mul_Ioi (a := -D) (by linarith) 0 using 1
    funext s
    congr 1
    ring
  have hmajorant : IntegrableOn
      (fun s : ℝ ↦ A * Real.exp (-(D * s))) (Ioi 0) :=
    hbase.const_mul A
  have hpointwise : ∀ s ∈ Ioi (0 : ℝ),
      ‖Real.exp (-s) • F (t + s)‖ ≤
        A * Real.exp (-(D * s)) := by
    intro s hs
    have hs0 : 0 ≤ s := hs.le
    have htu : 0 ≤ t + s := add_nonneg ht hs0
    have hFu := hF (t + s) htu
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-s) * ‖F (t + s)‖ ≤
          Real.exp (-s) * (C * Real.exp (epsilon * (t + s))) :=
        mul_le_mul_of_nonneg_left hFu (Real.exp_pos _).le
      _ = A * Real.exp (-(D * s)) := by
        dsimp [A, D]
        calc
          Real.exp (-s) * (C * Real.exp (epsilon * (t + s))) =
              C * Real.exp (-s + epsilon * (t + s)) := by
            rw [Real.exp_add]
            ring
          _ = C * Real.exp (epsilon * t - (1 - epsilon) * s) := by
            congr 2
            ring
          _ = C * Real.exp (epsilon * t) *
              Real.exp (-((1 - epsilon) * s)) := by
            rw [show epsilon * t - (1 - epsilon) * s =
                epsilon * t + (-((1 - epsilon) * s)) by ring,
              Real.exp_add]
            ring
  calc
    ‖futureExponentialConvolution F t‖ =
        ‖∫ s : ℝ in Ioi 0, Real.exp (-s) • F (t + s)‖ := rfl
    _ ≤ ∫ s : ℝ in Ioi 0,
        ‖Real.exp (-s) • F (t + s)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s : ℝ in Ioi 0,
        A * Real.exp (-(D * s)) :=
      setIntegral_mono_on hint.norm hmajorant measurableSet_Ioi hpointwise
    _ = A * D⁻¹ := by
      rw [MeasureTheory.integral_const_mul,
        integral_exp_neg_mul_Ioi_zero hD]
    _ = (C * Real.exp (epsilon * t)) / (1 - epsilon) := by
      dsimp [A, D]
      rw [div_eq_mul_inv]

/-- Subexponential norm growth for a normed-space-valued signal on
nonnegative time. -/
def NormSubexponentialOnNonnegativeTime (F : ℝ → E) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖F t‖ ≤ C * Real.exp (epsilon * t)

/-- Whenever all future convolutions exist, exponential future smoothing
preserves subexponential norm growth. -/
theorem normSubexponential_futureExponentialConvolution
    {F : ℝ → E}
    (hint : ∀ t : ℝ, 0 ≤ t → IntegrableOn
      (fun s : ℝ ↦ Real.exp (-s) • F (t + s)) (Ioi 0))
    (hsub : NormSubexponentialOnNonnegativeTime F) :
    NormSubexponentialOnNonnegativeTime
      (futureExponentialConvolution F) := by
  intro epsilon hepsilon
  let delta : ℝ := min epsilon 1 / 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hdeltaOne : delta < 1 := by
    dsimp [delta]
    have hmin : min epsilon 1 ≤ 1 := min_le_right _ _
    linarith
  have hdeltaEpsilon : delta ≤ epsilon := by
    dsimp [delta]
    have hmin : min epsilon 1 ≤ epsilon := min_le_left _ _
    have hminPos : 0 < min epsilon 1 := lt_min hepsilon zero_lt_one
    linarith
  obtain ⟨C, hC, hbound⟩ := hsub delta hdelta
  let C' : ℝ := C / (1 - delta)
  have hden : 0 < 1 - delta := by linarith
  have hC' : 0 ≤ C' := div_nonneg hC hden.le
  refine ⟨C', hC', ?_⟩
  intro t ht
  have hconv := norm_futureExponentialConvolution_le_of_exponential
    ht hdeltaOne (hint t ht) hbound
  have hexp : Real.exp (delta * t) ≤ Real.exp (epsilon * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hdeltaEpsilon ht)
  calc
    ‖futureExponentialConvolution F t‖ ≤
        (C * Real.exp (delta * t)) / (1 - delta) := hconv
    _ = C' * Real.exp (delta * t) := by
      dsimp [C']
      field_simp [hden.ne']
    _ ≤ C' * Real.exp (epsilon * t) :=
      mul_le_mul_of_nonneg_left hexp hC'

end FutureConvolution

end

end RiemannGaussian
