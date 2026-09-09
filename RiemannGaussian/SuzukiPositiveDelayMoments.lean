/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.PositiveDelayAveraging
import RiemannGaussian.SignedLaplaceMoments
import RiemannGaussian.SuzukiTimeHeat
import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatFiniteRegularization

/-!
# Positive delay regularization of the actual Suzuki response

Every finite delay list containing the genuine zeros in a prescribed height
window removes those poles from the arithmetic Laplace response. The proof
uses the actual finite principal-part decomposition and entire divided
differences of the full multiplier. No residue is dropped without its exact
positive time-domain operation.

Once the window contains a disk extending past the origin, the remaining
double pole yields a uniform error bound for all signed factorial moments.
This is an averaged estimate, not a pointwise arithmetic lower bound.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter MeasureTheory Metric Set
open scoped Topology

/-- The original arithmetic signal with its literal causal support. -/
def suzukiCausalSignal : ℝ → ℝ :=
  (Ioi 0).indicator suzukiChebyshevLogAverageLaplaceSignal

/-- A finite positive delay average of the actual causal arithmetic signal. -/
def suzukiPositiveDelaySignal (L : List ℂ) : ℝ → ℝ :=
  positiveDelayAverage L suzukiCausalSignal

/-- The full complex response of the positive delay average. -/
def suzukiPositiveDelayResponse (L : List ℂ) (z : ℂ) : ℂ :=
  positiveDelayMultiplier L z * suzukiChebyshevLogAverageLaplaceCompletedContinuation z

private theorem causal_laplace_integrand (z : ℂ) (t : ℝ) :
    (suzukiCausalSignal t : ℂ) * Complex.exp (-z * (t : ℂ)) =
      suzukiChebyshevLogAverageComplexLaplaceIntegrand z t := by
  by_cases ht : t ∈ Ioi (0 : ℝ) <;>
    simp [suzukiCausalSignal, suzukiChebyshevLogAverageComplexLaplaceIntegrand, ht]

/-- The delayed signal has an absolutely convergent Laplace integral on
every safe vertical line. -/
theorem integrable_suzukiPositiveDelaySignal_laplace (L : List ℂ) {z : ℂ}
    (hz : 1 / 2 < z.re) :
    Integrable (fun t : ℝ => (suzukiPositiveDelaySignal L t : ℂ) *
      Complex.exp (-z * (t : ℂ))) := by
  apply integrable_positiveDelayAverage_laplace
  simpa only [causal_laplace_integrand] using
    integrable_suzukiChebyshevLogAverageComplexLaplaceIntegrand hz

/-- Exact transform of the delayed arithmetic signal, with the complete
signed integral and no support-completion error. -/
theorem integral_suzukiPositiveDelaySignal_laplace (L : List ℂ) {z : ℂ}
    (hz : 1 / 2 < z.re) :
    (∫ t : ℝ, (suzukiPositiveDelaySignal L t : ℂ) * Complex.exp (-z * (t : ℂ))) =
      suzukiPositiveDelayResponse L z := by
  have hi : Integrable (fun t : ℝ => (suzukiCausalSignal t : ℂ) *
      Complex.exp (-z * (t : ℂ))) := by
    simpa only [causal_laplace_integrand] using
      integrable_suzukiChebyshevLogAverageComplexLaplaceIntegrand hz
  rw [suzukiPositiveDelaySignal, integral_positiveDelayAverage_laplace L hi]
  simp_rw [causal_laplace_integrand]
  change _ * suzukiChebyshevLogAverageComplexLaplaceTransform z = _
  rw [suzukiChebyshevLogAverageComplexLaplaceTransform_eq_completedContinuation hz]
  rfl

/-- A positive delay average of the Suzuki signal retains its causal
support; negative time contributes nothing to any moment. -/
theorem suzukiPositiveDelaySignal_eq_zero_of_nonpositive (L : List ℂ) {t : ℝ}
    (ht : t ≤ 0) : suzukiPositiveDelaySignal L t = 0 := by
  apply positiveDelayAverage_eq_zero_of_nonpositive L _ ht
  intro u hu
  simp [suzukiCausalSignal, not_lt.mpr hu]

/-- A lower bound on a delayed value is attained or exceeded by an actual
Suzuki value within the finite backward delay span. -/
theorem exists_suzukiSignal_ge_positiveDelay (L : List ℂ) {t : ℝ}
    (ht : positiveDelaySpan L < t) :
    ∃ u ∈ Icc (t - positiveDelaySpan L) t,
      suzukiPositiveDelaySignal L t ≤ suzukiChebyshevLogAverageLaplaceSignal u := by
  obtain ⟨u, hu, hh⟩ := exists_positiveDelayAverage_le L suzukiCausalSignal t
  refine ⟨u, hu, ?_⟩
  have hu0 : 0 < u := by linarith [hu.1]
  simpa only [suzukiPositiveDelaySignal, suzukiCausalSignal,
    Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu0)] using hh

/-- Real exponential damping is absolutely integrable throughout the same
safe half-plane as the complete complex response. -/
theorem integrable_suzukiPositiveDelaySignal_real_laplace (L : List ℂ) {x : ℝ}
    (hx : 1 / 2 < x) :
    Integrable (fun t : ℝ => suzukiPositiveDelaySignal L t * Real.exp (-x * t)) := by
  apply (integrable_suzukiPositiveDelaySignal_laplace L (z := x) hx).re.congr
  filter_upwards with t
  change ((suzukiPositiveDelaySignal L t : ℂ) * Complex.exp (-(x : ℂ) * (t : ℂ))).re = _
  rw [show -(x : ℂ) * (t : ℂ) = ((-x * t : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.ofReal_re]

private theorem aemeasurable_signal (L : List ℂ) : AEMeasurable (suzukiPositiveDelaySignal L) volume := by
  have h := ((integrable_suzukiPositiveDelaySignal_real_laplace L (x := 1) (by norm_num)).aemeasurable.mul
    Real.continuous_exp.aemeasurable)
  apply h.congr
  filter_upwards with t
  change suzukiPositiveDelaySignal L t * Real.exp (-1 * t) * Real.exp t = _
  rw [mul_assoc, ← Real.exp_add]
  simp

/-- Every complex factorial moment is the literal signed time integral of
the delayed arithmetic signal. All derivative and integral interchanges are
justified by genuine exponential integrability. -/
theorem signedTaylorMoment_suzukiPositiveDelayResponse (L : List ℂ) {z : ℂ}
    (hz : 1 / 2 < z.re) (n : ℕ) :
    signedTaylorMoment n (suzukiPositiveDelayResponse L) z =
      ∫ t : ℝ, ((suzukiPositiveDelaySignal L t : ℂ) * (t : ℂ) ^ n *
        Complex.exp (-z * (t : ℂ))) / (n.factorial : ℂ) := by
  have hm := signed_real_laplace_moments (aemeasurable_signal L)
    (fun _ hx => integrable_suzukiPositiveDelaySignal_real_laplace L hx) hz
  have he : (fun w : ℂ => ∫ t : ℝ, (suzukiPositiveDelaySignal L t : ℂ) *
      Complex.exp (-w * (t : ℂ))) =ᶠ[𝓝 z] suzukiPositiveDelayResponse L := by
    have hopen : IsOpen {w : ℂ | 1 / 2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.eventually_mem hz] with w hw
    exact integral_suzukiPositiveDelaySignal_laplace L hw
  rw [← signedTaylorMoment_congr n he]
  exact (hm.2 n).2

/-- The exact factorial-weighted signed average at unit damping. On causal
support its kernel `t^n exp(-t)/n!` is nonnegative. -/
def suzukiPositiveDelayGammaMoment (L : List ℂ) (n : ℕ) : ℝ :=
  ∫ t : ℝ, suzukiPositiveDelaySignal L t * t ^ n * Real.exp (-t) / (n.factorial : ℝ)

/-- Every factorial-kernel moment of the delayed signal is absolutely
integrable, including before taking its signed real average. -/
theorem integrable_suzukiPositiveDelayGammaMoment (L : List ℂ) (n : ℕ) :
    Integrable (fun t : ℝ => suzukiPositiveDelaySignal L t * t ^ n *
      Real.exp (-t) / (n.factorial : ℝ)) := by
  have hm := ((signed_real_laplace_moments (aemeasurable_signal L)
    (fun _ hx => integrable_suzukiPositiveDelaySignal_real_laplace L hx) (z := 1) (by norm_num)).2 n).1
  have h := (hm.div_const (n.factorial : ℂ)).re
  apply h.congr
  filter_upwards with t
  change (((suzukiPositiveDelaySignal L t : ℂ) * (t : ℂ) ^ n *
    Complex.exp (-(1 : ℂ) * (t : ℂ))) / (n.factorial : ℂ)).re = _
  have he : ((suzukiPositiveDelaySignal L t * t ^ n * Real.exp (-t) /
      (n.factorial : ℝ) : ℝ) : ℂ) =
      ((suzukiPositiveDelaySignal L t : ℂ) * (t : ℂ) ^ n *
        Complex.exp (-(1 : ℂ) * (t : ℂ))) / (n.factorial : ℂ) := by
    push_cast
    simp
  rw [← he, Complex.ofReal_re]

/-- The real positive-kernel average retains the complete complex moment
exactly; it is not obtained from a triangle estimate. -/
theorem suzukiPositiveDelayGammaMoment_eq_signedTaylorMoment (L : List ℂ) (n : ℕ) :
    (suzukiPositiveDelayGammaMoment L n : ℂ) =
      signedTaylorMoment n (suzukiPositiveDelayResponse L) 1 := by
  rw [signedTaylorMoment_suzukiPositiveDelayResponse L (by norm_num),
    suzukiPositiveDelayGammaMoment, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with t
  push_cast
  simp

/-- The eta measure proves that every genuine shifted zero is nonreal, as
required by the exact positive delay cancellation. -/
theorem suzukiChebyshevLaplaceZeroCoordinate_im_ne_zero (rho : NontrivialZetaZero) :
    (suzukiChebyshevLaplaceZeroCoordinate rho).im ≠ 0 := by
  simpa [suzukiChebyshevLaplaceZeroCoordinate] using
    nontrivialZetaZero_im_ne_zero_of_etaMeasure rho

private theorem multiplier_principalPart_eq_dslope (L : List ℂ)
    (rho : NontrivialZetaZero)
    (hmem : suzukiChebyshevLaplaceZeroCoordinate rho ∈ L) {z : ℂ}
    (hz : z ≠ suzukiChebyshevLaplaceZeroCoordinate rho) :
    positiveDelayMultiplier L z * suzukiChebyshevLaplacePoleClearedPrincipalPart rho z =
      (analyticZetaZeroMultiplicity rho : ℂ) *
        dslope (positiveDelayMultiplier L) (suzukiChebyshevLaplaceZeroCoordinate rho) z := by
  rw [dslope_of_ne _ hz, slope,
    positiveDelayMultiplier_eq_zero_of_mem hmem
      (suzukiChebyshevLaplaceZeroCoordinate_im_ne_zero rho)]
  simp only [vsub_eq_sub, sub_zero, smul_eq_mul,
    suzukiChebyshevLaplacePoleClearedPrincipalPart, simplePoleKernel, div_eq_mul_inv]
  ring

/-- Every finite positive delay family covering the genuine zero window
has an analytic pole-cleared numerator on the entire finite slab. The
construction uses the original arithmetic response away from the divisor. -/
theorem exists_suzukiPositiveDelay_analyticNumerator {T : ℝ} (hT : 0 ≤ T)
    (L : List ℂ)
    (hcover : ∀ rho ∈ spectralZetaZeroWindow T,
      suzukiChebyshevLaplaceZeroCoordinate rho ∈ L) :
    ∃ Q : ℂ → ℂ,
      AnalyticOnNhd ℂ Q (suzukiChebyshevLaplaceFiniteSlab T) ∧
      ∀ z ∉ suzukiChebyshevLaplaceZeroWindow T,
        Q z = positiveDelayMultiplier L z *
          suzukiChebyshevLogAverageLaplacePoleClearedContinuation z := by
  obtain ⟨F, hF, hdecomp⟩ :=
    exists_suzukiChebyshevLaplacePoleClearedWindowAnalyticDecomposition hT
  let Q : ℂ → ℂ := fun z => positiveDelayMultiplier L z * F z +
    ∑ rho ∈ spectralZetaZeroWindow T, (analyticZetaZeroMultiplicity rho : ℂ) *
      dslope (positiveDelayMultiplier L) (suzukiChebyshevLaplaceZeroCoordinate rho) z
  refine ⟨Q, ?_, ?_⟩
  · intro z hz
    apply ((analyticAt_positiveDelayMultiplier L z).mul (hF z hz)).add
    apply analyticAt_finset_sum_apply
    intro rho _
    exact analyticAt_const.mul (analyticAt_dslope_of_analyticAt
      (analyticAt_positiveDelayMultiplier L _) (analyticAt_positiveDelayMultiplier L z))
  · intro z hz
    rw [hdecomp z hz, mul_add]
    unfold Q suzukiChebyshevLaplacePoleClearedWindowPrincipalSum
    rw [Finset.mul_sum, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro rho hrho
    apply (multiplier_principalPart_eq_dslope L rho (hcover rho hrho) _).symm
    intro heq
    apply hz
    exact Finset.mem_image.mpr ⟨rho, hrho, heq.symm⟩

private theorem safe_not_mem_zeroWindow {T : ℝ} {z : ℂ} (hz : 1 / 2 < z.re) :
    z ∉ suzukiChebyshevLaplaceZeroWindow T := by
  intro hm
  obtain ⟨rho, _, hrho⟩ := Finset.mem_image.mp hm
  have hre := NontrivialZetaZero.re_lt_one rho
  rw [← hrho] at hz
  norm_num [suzukiChebyshevLaplaceZeroCoordinate] at hz
  linarith

private theorem ball_subset_slab {T : ℝ} (hT : (5 : ℝ) / 4 ≤ T) :
    closedBall (1 : ℂ) (5 / 4) ⊆ suzukiChebyshevLaplaceFiniteSlab T := by
  intro z hz
  have hn : ‖z - 1‖ ≤ (5 : ℝ) / 4 := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have hr := (abs_re_le_norm (z - 1)).trans hn
  have hi := (abs_im_le_norm (z - 1)).trans hn
  simp only [sub_re, one_re, sub_im, one_im, sub_zero] at hr hi
  constructor
  · norm_num [Complex.add_re]
    linarith [(abs_le.mp hr).1]
  · exact hi.trans hT

/-- All factorial moments of the complete delayed response have a bounded
error after subtracting their linear double-pole term. This holds for every
finite delay family covering the indicated genuine zero window. -/
theorem exists_suzukiPositiveDelayMoment_uniform_error {T : ℝ}
    (hT : (5 : ℝ) / 4 ≤ T) (L : List ℂ)
    (hcover : ∀ rho ∈ spectralZetaZeroWindow T,
      suzukiChebyshevLaplaceZeroCoordinate rho ∈ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖signedTaylorMoment n (suzukiPositiveDelayResponse L) 1 -
        ((n + 1 : ℕ) : ℂ) * suzukiChebyshevLogAverageLaplacePoleClearedContinuation 0‖ ≤ C := by
  obtain ⟨Q, hQ, heq⟩ := exists_suzukiPositiveDelay_analyticNumerator
    (by linarith : 0 ≤ T) L hcover
  have hQ0 : Q 0 = suzukiChebyshevLogAverageLaplacePoleClearedContinuation 0 := by
    rw [heq 0, positiveDelayMultiplier_zero, one_mul]
    intro hm
    obtain ⟨rho, _, hrho⟩ := Finset.mem_image.mp hm
    have hn := suzukiChebyshevLaplaceZeroCoordinate_im_ne_zero rho
    apply hn
    rw [hrho]
    rfl
  have hagree : (fun z : ℂ => Q z / (z - 0) ^ 2) =ᶠ[𝓝 (1 : ℂ)]
      suzukiPositiveDelayResponse L := by
    have hopen : IsOpen {z : ℂ | 1 / 2 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.eventually_mem (by norm_num : (1 : ℂ) ∈ {z : ℂ | 1 / 2 < z.re})]
      with z hz
    have hz0 : z ≠ 0 := by intro he; subst z; norm_num at hz
    rw [heq z (safe_not_mem_zeroWindow hz),
      suzukiChebyshevLogAverageLaplacePoleClearedContinuation_eq_sq_mul_completed hz0]
    unfold suzukiPositiveDelayResponse
    simp only [sub_zero]
    field_simp
  obtain ⟨C, hC, hb⟩ := exists_doublePoleMoment_uniform_error
    (hQ.mono (ball_subset_slab hT)) (a := 0) (by norm_num) (by norm_num)
  refine ⟨C, hC, fun n => ?_⟩
  have hn := hb n
  rw [signedTaylorMoment_congr n hagree] at hn
  simpa only [sub_zero, one_pow, one_mul, hQ0] using hn

/-- The surviving real double-pole coefficient is exactly the negative
Archimedean slope. Reflection symmetry removes the central xi derivative. -/
theorem suzukiPoleClearedContinuation_zero_re :
    (suzukiChebyshevLogAverageLaplacePoleClearedContinuation 0).re =
      -suzukiArchimedeanSlopeConstant := by
  have hd : deriv riemannXi (1 / 2 : ℂ) = 0 := by
    have he := deriv_riemannXi_one_sub (1 / 2)
    norm_num at he
    linear_combination (1 / 2 : ℂ) * he
  have hl : logDeriv riemannXi (1 / 2 : ℂ) = 0 := by
    rw [logDeriv_apply, hd, zero_div]
  unfold suzukiChebyshevLogAverageLaplacePoleClearedContinuation
    suzukiChebyshevLogAverageLaplaceRegularCorrection
  simp only [zero_add, hl, zero_add]
  norm_num [Complex.log_re, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.div_re, suzukiArchimedeanSlopeConstant]
  ring

/-- Uniform two-sided error for the actual signed positive-kernel moments.
The leading linear term is independent of every choice of delay family. -/
theorem exists_suzukiPositiveDelayGammaMoment_uniform_error {T : ℝ}
    (hT : (5 : ℝ) / 4 ≤ T) (L : List ℂ)
    (hcover : ∀ rho ∈ spectralZetaZeroWindow T,
      suzukiChebyshevLaplaceZeroCoordinate rho ∈ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      |suzukiPositiveDelayGammaMoment L n + (n + 1 : ℝ) * suzukiArchimedeanSlopeConstant| ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_suzukiPositiveDelayMoment_uniform_error hT L hcover
  refine ⟨C, hC, fun n => ?_⟩
  have hn := (abs_re_le_norm _).trans (hb n)
  rw [← suzukiPositiveDelayGammaMoment_eq_signedTaylorMoment] at hn
  simpa [Complex.sub_re, Complex.mul_re, suzukiPoleClearedContinuation_zero_re] using hn

/-- An exact delay list from the complete genuine finite zero window.
It requires no numerical zero locations or coefficient search. -/
def suzukiZeroWindowDelayNodes (T : ℝ) : List ℂ :=
  (suzukiChebyshevLaplaceZeroWindow T).toList

/-- The actual finite zero window supplies every required cancellation
factor, so the signed moment bound has no undisclosed arithmetic premise. -/
theorem exists_suzukiZeroWindowDelayGammaMoment_uniform_error {T : ℝ}
    (hT : (5 : ℝ) / 4 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      |suzukiPositiveDelayGammaMoment (suzukiZeroWindowDelayNodes T) n +
        (n + 1 : ℝ) * suzukiArchimedeanSlopeConstant| ≤ C := by
  apply exists_suzukiPositiveDelayGammaMoment_uniform_error hT
  intro rho hrho
  apply Finset.mem_toList.mpr
  exact Finset.mem_image.mpr ⟨rho, hrho, rfl⟩

end
end RiemannGaussian
