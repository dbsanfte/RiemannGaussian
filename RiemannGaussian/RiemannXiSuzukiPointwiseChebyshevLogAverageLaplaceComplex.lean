import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplace

/-!
# The complex Laplace transform of Suzuki's logarithmic average

This file complexifies the verified one-sided Laplace representation of
Suzuki's weighted Chebyshev logarithmic-average error.  The integrand is
supported on positive logarithmic time and depends holomorphically on a
complex Laplace parameter.  Lean factors it into its real damping kernel and
a unit-norm oscillatory phase, then uses the previously proved real `L¹`
integrability to prove genuine complex integrability throughout
`Re z > 1/2`.

Lean proves differentiation under the infinite integral and hence holomorphy
throughout `Re z > 1/2`.  On the positive real ray, the complex transform is
the cast of the literal real Laplace integral.  The identity theorem then
promotes the real arithmetic formula to the whole convergence half-plane and
recovers the genuine spectral-xi logarithmic derivative at every corresponding
complex spectral point.  Nothing here continues the literal integral across
`Re z = 1/2`.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

/-- The half-plane of absolute convergence for the complex logarithmic-time Laplace transform. -/
def suzukiChebyshevLogAverageComplexLaplaceDomain : Set ℂ :=
  {z : ℂ | 1 / 2 < z.re}

/-- The complex Laplace domain `Re z > 1/2` is open. -/
theorem isOpen_suzukiChebyshevLogAverageComplexLaplaceDomain :
    IsOpen suzukiChebyshevLogAverageComplexLaplaceDomain := by
  exact isOpen_lt continuous_const Complex.continuous_re

private theorem sub_radius_lt_re_of_mem_complex_ball
    {z w : ℂ} {r : ℝ} (hw : w ∈ Metric.ball z r) :
    z.re - r < w.re := by
  have habs : |w.re - z.re| < r := calc
    |w.re - z.re| = |(w - z).re| := by rw [sub_re]
    _ ≤ ‖w - z‖ := Complex.abs_re_le_norm _
    _ = dist w z := by rw [dist_eq_norm]
    _ < r := by simpa [Metric.mem_ball, dist_comm] using hw
  have hneg : -|w.re - z.re| ≤ w.re - z.re := neg_abs_le _
  linarith

/-- The positive-time-supported complex Laplace integrand. -/
def suzukiChebyshevLogAverageComplexLaplaceIntegrand
    (z : ℂ) (t : ℝ) : ℂ :=
  Set.indicator (Set.Ioi (0 : ℝ))
    (fun u => (suzukiChebyshevLogAverageLaplaceSignal u : ℂ) *
      Complex.exp (-z * (u : ℂ))) t

/-- The literal complex one-sided Laplace transform of Suzuki's logarithmic-time signal. -/
def suzukiChebyshevLogAverageComplexLaplaceTransform (z : ℂ) : ℂ :=
  ∫ t : ℝ, suzukiChebyshevLogAverageComplexLaplaceIntegrand z t

/-- The unit-norm oscillatory phase left after extracting the real Laplace damping. -/
def suzukiChebyshevLogAverageComplexLaplacePhase (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (z.im : ℂ) * (t : ℂ))

/-- The complex integrand is its real-damping kernel times a unitary oscillatory phase. -/
theorem suzukiChebyshevLogAverageComplexLaplaceIntegrand_eq_phase_mul_realKernel
    (z : ℂ) (t : ℝ) :
    suzukiChebyshevLogAverageComplexLaplaceIntegrand z t =
      suzukiChebyshevLogAverageComplexLaplacePhase z t *
        ((Set.indicator (Set.Ioi (0 : ℝ))
          (suzukiChebyshevLogAverageLaplaceKernel z.re) t : ℝ) : ℂ) := by
  unfold suzukiChebyshevLogAverageComplexLaplaceIntegrand
    suzukiChebyshevLogAverageComplexLaplacePhase
  by_cases ht : t ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    have hexponent : -z * (t : ℂ) =
        ((-z.re * t : ℝ) : ℂ) +
          (-Complex.I * (z.im : ℂ) * (t : ℂ)) := by
      calc
        -z * (t : ℂ) =
            -((z.re : ℂ) + (z.im : ℂ) * Complex.I) * (t : ℂ) := by
          rw [Complex.re_add_im]
        _ = ((-z.re * t : ℝ) : ℂ) +
              (-Complex.I * (z.im : ℂ) * (t : ℂ)) := by
          push_cast
          ring
    rw [hexponent]
    rw [Complex.exp_add, ← Complex.ofReal_exp]
    unfold suzukiChebyshevLogAverageLaplaceKernel
    push_cast
    ring_nf
  · simp [ht]

/-- The pointwise parameter derivative of the supported complex Laplace integrand. -/
def suzukiChebyshevLogAverageComplexLaplaceDerivativeIntegrand
    (z : ℂ) (t : ℝ) : ℂ :=
  Set.indicator (Set.Ioi (0 : ℝ))
    (fun u => -(u : ℂ) *
      (suzukiChebyshevLogAverageLaplaceSignal u : ℂ) *
        Complex.exp (-z * (u : ℂ))) t

/-- For every fixed time, the complex Laplace integrand has the displayed complex derivative. -/
theorem hasDerivAt_suzukiChebyshevLogAverageComplexLaplaceIntegrand
    (z : ℂ) (t : ℝ) :
    HasDerivAt
      (fun w : ℂ => suzukiChebyshevLogAverageComplexLaplaceIntegrand w t)
      (suzukiChebyshevLogAverageComplexLaplaceDerivativeIntegrand z t) z := by
  by_cases ht : t ∈ Set.Ioi (0 : ℝ)
  · simp only [suzukiChebyshevLogAverageComplexLaplaceIntegrand,
      suzukiChebyshevLogAverageComplexLaplaceDerivativeIntegrand,
      Set.indicator_of_mem ht]
    have hinner : HasDerivAt (fun w : ℂ => -w * (t : ℂ)) (-(t : ℂ)) z := by
      simpa only [Pi.neg_apply, id_eq, neg_mul, one_mul] using
        (hasDerivAt_id z).neg.mul_const (t : ℂ)
    have hout := (hinner.cexp).const_mul
      (suzukiChebyshevLogAverageLaplaceSignal t : ℂ)
    exact hout.congr_deriv (by ring)
  · simpa [suzukiChebyshevLogAverageComplexLaplaceIntegrand,
      suzukiChebyshevLogAverageComplexLaplaceDerivativeIntegrand, ht] using
        hasDerivAt_const z (0 : ℂ)

/-- The pointwise derivative is multiplication of the original supported integrand by negative time. -/
theorem suzukiChebyshevLogAverageComplexLaplaceDerivativeIntegrand_eq_negTime_mul
    (z : ℂ) (t : ℝ) :
    suzukiChebyshevLogAverageComplexLaplaceDerivativeIntegrand z t =
      -(t : ℂ) * suzukiChebyshevLogAverageComplexLaplaceIntegrand z t := by
  unfold suzukiChebyshevLogAverageComplexLaplaceDerivativeIntegrand
    suzukiChebyshevLogAverageComplexLaplaceIntegrand
  by_cases ht : t ∈ Set.Ioi (0 : ℝ)
  · simp only [Set.indicator_of_mem ht]
    ring
  · simp [ht]

/-- The oscillatory phase has norm one at every time. -/
theorem norm_suzukiChebyshevLogAverageComplexLaplacePhase
    (z : ℂ) (t : ℝ) :
    ‖suzukiChebyshevLogAverageComplexLaplacePhase z t‖ = 1 := by
  unfold suzukiChebyshevLogAverageComplexLaplacePhase
  rw [Complex.norm_exp]
  simp

/-- Exact norm of the real logarithmic-time Laplace kernel. -/
theorem norm_suzukiChebyshevLogAverageLaplaceKernel (lambda t : ℝ) :
    ‖suzukiChebyshevLogAverageLaplaceKernel lambda t‖ =
      |suzukiChebyshevLogAverageLaplaceSignal t| * Real.exp (-lambda * t) := by
  unfold suzukiChebyshevLogAverageLaplaceKernel
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- At nonnegative time, increasing the real Laplace parameter decreases the kernel norm. -/
theorem norm_suzukiChebyshevLogAverageLaplaceKernel_anti
    {mu lambda t : ℝ} (ht : 0 ≤ t) (hparam : mu ≤ lambda) :
    ‖suzukiChebyshevLogAverageLaplaceKernel lambda t‖ ≤
      ‖suzukiChebyshevLogAverageLaplaceKernel mu t‖ := by
  rw [norm_suzukiChebyshevLogAverageLaplaceKernel,
    norm_suzukiChebyshevLogAverageLaplaceKernel]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- One logarithmic-time moment at stronger damping is dominated by a weaker Laplace kernel. -/
theorem time_mul_norm_suzukiChebyshevLogAverageLaplaceKernel_le
    {mu lambda t : ℝ} (hparam : mu < lambda) :
    t * ‖suzukiChebyshevLogAverageLaplaceKernel lambda t‖ ≤
      (lambda - mu)⁻¹ *
        ‖suzukiChebyshevLogAverageLaplaceKernel mu t‖ := by
  have hgap : 0 < lambda - mu := sub_pos.mpr hparam
  have hgapExp : (lambda - mu) * t ≤
      Real.exp ((lambda - mu) * t) := by
    calc
      (lambda - mu) * t ≤ (lambda - mu) * t + 1 := by linarith
      _ ≤ Real.exp ((lambda - mu) * t) := Real.add_one_le_exp _
  have htime : t ≤ (lambda - mu)⁻¹ *
      Real.exp ((lambda - mu) * t) := by
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hgap).2 (by simpa [mul_comm] using hgapExp)
  rw [norm_suzukiChebyshevLogAverageLaplaceKernel,
    norm_suzukiChebyshevLogAverageLaplaceKernel]
  calc
    t * (|suzukiChebyshevLogAverageLaplaceSignal t| *
        Real.exp (-lambda * t)) ≤
        ((lambda - mu)⁻¹ * Real.exp ((lambda - mu) * t)) *
          (|suzukiChebyshevLogAverageLaplaceSignal t| *
            Real.exp (-lambda * t)) := by
      apply mul_le_mul_of_nonneg_right htime
      positivity
    _ = (lambda - mu)⁻¹ *
        |suzukiChebyshevLogAverageLaplaceSignal t| *
          (Real.exp ((lambda - mu) * t) * Real.exp (-lambda * t)) := by
      ring
    _ = (lambda - mu)⁻¹ *
        |suzukiChebyshevLogAverageLaplaceSignal t| *
          Real.exp ((lambda - mu) * t + -lambda * t) := by
      rw [Real.exp_add]
    _ = (lambda - mu)⁻¹ *
        (|suzukiChebyshevLogAverageLaplaceSignal t| *
          Real.exp (-mu * t)) := by
      rw [show (lambda - mu) * t + -lambda * t = -mu * t by ring]
      ring

/-- The complex Laplace integrand is genuinely integrable throughout `Re z > 1/2`. -/
theorem integrable_suzukiChebyshevLogAverageComplexLaplaceIntegrand
    {z : ℂ} (hz : z ∈ suzukiChebyshevLogAverageComplexLaplaceDomain) :
    Integrable (suzukiChebyshevLogAverageComplexLaplaceIntegrand z) := by
  have hrealOn : IntegrableOn
      (suzukiChebyshevLogAverageLaplaceKernel z.re)
      (Set.Ioi (0 : ℝ)) :=
    integrableOn_suzukiChebyshevLogAverageLaplaceKernel hz
  have hreal : Integrable
      (Set.indicator (Set.Ioi (0 : ℝ))
        (suzukiChebyshevLogAverageLaplaceKernel z.re)) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hrealOn
  have hcast : Integrable (fun t : ℝ =>
      ((Set.indicator (Set.Ioi (0 : ℝ))
        (suzukiChebyshevLogAverageLaplaceKernel z.re) t : ℝ) : ℂ)) :=
    hreal.ofReal
  have hphaseMeas : AEStronglyMeasurable
      (suzukiChebyshevLogAverageComplexLaplacePhase z) := by
    apply Continuous.aestronglyMeasurable
    unfold suzukiChebyshevLogAverageComplexLaplacePhase
    fun_prop
  have hproduct : Integrable (fun t : ℝ =>
      suzukiChebyshevLogAverageComplexLaplacePhase z t *
        ((Set.indicator (Set.Ioi (0 : ℝ))
          (suzukiChebyshevLogAverageLaplaceKernel z.re) t : ℝ) : ℂ)) :=
    hcast.bdd_mul hphaseMeas (Eventually.of_forall fun t => by
      rw [norm_suzukiChebyshevLogAverageComplexLaplacePhase])
  exact hproduct.congr (Eventually.of_forall fun t =>
    (suzukiChebyshevLogAverageComplexLaplaceIntegrand_eq_phase_mul_realKernel
      z t).symm)

/-- The derivative-integrand norm is positive time times the norm of the real damping kernel. -/
theorem norm_suzukiChebyshevLogAverageComplexLaplaceDerivativeIntegrand
    (z : ℂ) (t : ℝ) :
    ‖suzukiChebyshevLogAverageComplexLaplaceDerivativeIntegrand z t‖ =
      Set.indicator (Set.Ioi (0 : ℝ))
        (fun u => u *
          ‖suzukiChebyshevLogAverageLaplaceKernel z.re u‖) t := by
  unfold suzukiChebyshevLogAverageComplexLaplaceDerivativeIntegrand
  by_cases ht : t ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    have htNorm : ‖t‖ = t := by
      rw [Real.norm_eq_abs, abs_of_nonneg ht.le]
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_exp]
    simp only [Complex.norm_real]
    rw [htNorm, norm_suzukiChebyshevLogAverageLaplaceKernel,
      Real.norm_eq_abs]
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, neg_re]
    ring_nf
  · simp [ht]

/-- The pointwise parameter derivative is genuinely integrable everywhere in `Re z > 1/2`. -/
theorem integrable_suzukiChebyshevLogAverageComplexLaplaceDerivativeIntegrand
    {z : ℂ} (hz : z ∈ suzukiChebyshevLogAverageComplexLaplaceDomain) :
    Integrable
      (suzukiChebyshevLogAverageComplexLaplaceDerivativeIntegrand z) := by
  change (1 / 2 : ℝ) < z.re at hz
  let mu : ℝ := (z.re + 1 / 2) / 2
  have hmu : 1 / 2 < mu := by
    change (1 / 2 : ℝ) < (z.re + 1 / 2) / 2
    linarith
  have hmuz : mu < z.re := by
    change (z.re + 1 / 2) / 2 < z.re
    linarith
  have hkernelOn : IntegrableOn
      (suzukiChebyshevLogAverageLaplaceKernel mu)
      (Set.Ioi (0 : ℝ)) :=
    integrableOn_suzukiChebyshevLogAverageLaplaceKernel hmu
  have hmajorOn : IntegrableOn
      (fun t : ℝ => (z.re - mu)⁻¹ *
        ‖suzukiChebyshevLogAverageLaplaceKernel mu t‖)
      (Set.Ioi (0 : ℝ)) :=
    hkernelOn.norm.const_mul (z.re - mu)⁻¹
  have hmajor : Integrable
      (Set.indicator (Set.Ioi (0 : ℝ))
        (fun t : ℝ => (z.re - mu)⁻¹ *
          ‖suzukiChebyshevLogAverageLaplaceKernel mu t‖)) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hmajorOn
  have htimeMeas : AEStronglyMeasurable (fun t : ℝ => -(t : ℂ)) := by
    fun_prop
  have hderivMeas : AEStronglyMeasurable
      (suzukiChebyshevLogAverageComplexLaplaceDerivativeIntegrand z) := by
    have hproduct := htimeMeas.mul
      (integrable_suzukiChebyshevLogAverageComplexLaplaceIntegrand
        hz).aestronglyMeasurable
    exact hproduct.congr (Eventually.of_forall fun t =>
      (suzukiChebyshevLogAverageComplexLaplaceDerivativeIntegrand_eq_negTime_mul
        z t).symm)
  apply hmajor.mono' hderivMeas
  exact Eventually.of_forall fun t => by
    rw [norm_suzukiChebyshevLogAverageComplexLaplaceDerivativeIntegrand]
    by_cases ht : t ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      exact time_mul_norm_suzukiChebyshevLogAverageLaplaceKernel_le hmuz
    · simp [ht]

/-- Differentiation under the infinite integral is valid throughout the absolute-convergence half-plane. -/
theorem hasDerivAt_suzukiChebyshevLogAverageComplexLaplaceTransform
    {z : ℂ} (hz : z ∈ suzukiChebyshevLogAverageComplexLaplaceDomain) :
    HasDerivAt suzukiChebyshevLogAverageComplexLaplaceTransform
      (∫ t : ℝ,
        suzukiChebyshevLogAverageComplexLaplaceDerivativeIntegrand z t) z := by
  change (1 / 2 : ℝ) < z.re at hz
  let r : ℝ := (z.re - 1 / 2) / 4
  let mu : ℝ := z.re - 2 * r
  let s : Set ℂ := Metric.ball z r
  let bound : ℝ → ℝ :=
    Set.indicator (Set.Ioi (0 : ℝ))
      (fun t => r⁻¹ *
        ‖suzukiChebyshevLogAverageLaplaceKernel mu t‖)
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hmu : 1 / 2 < mu := by
    dsimp [mu, r]
    linarith
  have hs : s ∈ 𝓝 z := by
    exact Metric.ball_mem_nhds z hr
  have hF_meas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable
        (suzukiChebyshevLogAverageComplexLaplaceIntegrand w) := by
    filter_upwards [hs] with w hw
    have hwDomain : w ∈ suzukiChebyshevLogAverageComplexLaplaceDomain := by
      change (1 / 2 : ℝ) < w.re
      have hwlower : z.re - r < w.re :=
        sub_radius_lt_re_of_mem_complex_ball hw
      dsimp [r] at hwlower
      linarith
    exact (integrable_suzukiChebyshevLogAverageComplexLaplaceIntegrand
      hwDomain).aestronglyMeasurable
  have hkernelOn : IntegrableOn
      (suzukiChebyshevLogAverageLaplaceKernel mu)
      (Set.Ioi (0 : ℝ)) :=
    integrableOn_suzukiChebyshevLogAverageLaplaceKernel hmu
  have hboundIntegrable : Integrable bound := by
    apply (integrable_indicator_iff measurableSet_Ioi).mpr
    exact hkernelOn.norm.const_mul r⁻¹
  have hbound : ∀ᵐ t : ℝ ∂volume, ∀ w ∈ s,
      ‖suzukiChebyshevLogAverageComplexLaplaceDerivativeIntegrand w t‖ ≤
        bound t := by
    exact Eventually.of_forall fun t w hw => by
      rw [norm_suzukiChebyshevLogAverageComplexLaplaceDerivativeIntegrand]
      by_cases ht : t ∈ Set.Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem ht]
        unfold bound
        rw [Set.indicator_of_mem ht]
        have hwlower : z.re - r < w.re :=
          sub_radius_lt_re_of_mem_complex_ball hw
        have hmoment : t *
            ‖suzukiChebyshevLogAverageLaplaceKernel w.re t‖ ≤
              r⁻¹ *
                ‖suzukiChebyshevLogAverageLaplaceKernel (w.re - r) t‖ := by
          have hgap : w.re - r < w.re := by linarith
          have hmoment' :=
            time_mul_norm_suzukiChebyshevLogAverageLaplaceKernel_le
              (t := t) hgap
          have hgapEq : w.re - (w.re - r) = r := by ring
          rw [hgapEq] at hmoment'
          exact hmoment'
        have hparam : mu ≤ w.re - r := by
          dsimp [mu]
          linarith
        have hanti :=
          norm_suzukiChebyshevLogAverageLaplaceKernel_anti ht.le hparam
        exact hmoment.trans
          (mul_le_mul_of_nonneg_left hanti (inv_nonneg.mpr hr.le))
      · simp [bound, ht]
  have hdiff : ∀ᵐ t : ℝ ∂volume, ∀ w ∈ s,
      HasDerivAt
        (fun u : ℂ => suzukiChebyshevLogAverageComplexLaplaceIntegrand u t)
        (suzukiChebyshevLogAverageComplexLaplaceDerivativeIntegrand w t) w := by
    exact Eventually.of_forall fun t w _hw =>
      hasDerivAt_suzukiChebyshevLogAverageComplexLaplaceIntegrand w t
  unfold suzukiChebyshevLogAverageComplexLaplaceTransform
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hF_meas
    (integrable_suzukiChebyshevLogAverageComplexLaplaceIntegrand hz)
    (integrable_suzukiChebyshevLogAverageComplexLaplaceDerivativeIntegrand
      hz).aestronglyMeasurable
    hbound hboundIntegrable hdiff).2

/-- The literal complex arithmetic Laplace transform is analytic on `Re z > 1/2`. -/
theorem analyticOn_suzukiChebyshevLogAverageComplexLaplaceTransform :
    AnalyticOn ℂ suzukiChebyshevLogAverageComplexLaplaceTransform
      suzukiChebyshevLogAverageComplexLaplaceDomain := by
  rw [analyticOn_iff_differentiableOn
    isOpen_suzukiChebyshevLogAverageComplexLaplaceDomain]
  intro z hz
  exact (hasDerivAt_suzukiChebyshevLogAverageComplexLaplaceTransform hz).differentiableAt
    |>.differentiableWithinAt

/-- The literal complex arithmetic Laplace transform is analytic on a neighbourhood of every
point of its absolute-convergence half-plane. -/
theorem analyticOnNhd_suzukiChebyshevLogAverageComplexLaplaceTransform :
    AnalyticOnNhd ℂ suzukiChebyshevLogAverageComplexLaplaceTransform
      suzukiChebyshevLogAverageComplexLaplaceDomain :=
  analyticOn_suzukiChebyshevLogAverageComplexLaplaceTransform.differentiableOn.analyticOnNhd
    isOpen_suzukiChebyshevLogAverageComplexLaplaceDomain

/-- The explicit zeta-logarithmic-derivative response to the complex arithmetic Laplace
transform.  Its displayed denominators are nonzero throughout `Re z > 1/2`. -/
def suzukiChebyshevLogAverageComplexZetaResponse (z : ℂ) : ℂ :=
  logDeriv riemannZeta (z + 1 / 2) / z ^ 2 + 4 / (z - 1 / 2)

/-- Translation by `1/2` maps the complex Laplace half-plane into the Euler-product
half-plane for zeta. -/
theorem mapsTo_add_half_suzukiChebyshevLogAverageComplexLaplaceDomain :
    MapsTo (fun z : ℂ => z + 1 / 2)
      suzukiChebyshevLogAverageComplexLaplaceDomain
      suzukiArithmeticZetaDomain := by
  intro z hz
  change (1 : ℝ) < (z + 1 / 2).re
  change (1 / 2 : ℝ) < z.re at hz
  norm_num [Complex.div_re]
  linarith

/-- The explicit zeta response is holomorphic throughout the absolute-convergence
half-plane of the arithmetic Laplace transform. -/
theorem analyticOnNhd_suzukiChebyshevLogAverageComplexZetaResponse :
    AnalyticOnNhd ℂ suzukiChebyshevLogAverageComplexZetaResponse
      suzukiChebyshevLogAverageComplexLaplaceDomain := by
  have hshift : AnalyticOnNhd ℂ (fun z : ℂ => z + 1 / 2)
      suzukiChebyshevLogAverageComplexLaplaceDomain :=
    analyticOnNhd_id.add analyticOnNhd_const
  have hlog : AnalyticOnNhd ℂ
      (fun z : ℂ => logDeriv riemannZeta (z + 1 / 2))
      suzukiChebyshevLogAverageComplexLaplaceDomain :=
    analyticOnNhd_logDeriv_riemannZeta_re_gt_one.comp hshift
      mapsTo_add_half_suzukiChebyshevLogAverageComplexLaplaceDomain
  have hsq : AnalyticOnNhd ℂ (fun z : ℂ => z ^ 2)
      suzukiChebyshevLogAverageComplexLaplaceDomain :=
    analyticOnNhd_id.pow 2
  have hfirst : AnalyticOnNhd ℂ
      (fun z : ℂ => logDeriv riemannZeta (z + 1 / 2) / z ^ 2)
      suzukiChebyshevLogAverageComplexLaplaceDomain :=
    hlog.div hsq fun z hz => by
      apply pow_ne_zero
      intro hz0
      subst z
      norm_num [suzukiChebyshevLogAverageComplexLaplaceDomain] at hz
  have hden : AnalyticOnNhd ℂ (fun z : ℂ => z - 1 / 2)
      suzukiChebyshevLogAverageComplexLaplaceDomain :=
    analyticOnNhd_id.sub analyticOnNhd_const
  have hpole : AnalyticOnNhd ℂ (fun z : ℂ => 4 / (z - 1 / 2))
      suzukiChebyshevLogAverageComplexLaplaceDomain :=
    analyticOnNhd_const.div hden fun z hz => by
      intro hzero
      have hzhalf : z = 1 / 2 := sub_eq_zero.mp hzero
      subst z
      norm_num [suzukiChebyshevLogAverageComplexLaplaceDomain] at hz
  exact hfirst.add hpole

/-- At a real parameter, the complex integrand is exactly the cast real Laplace kernel on positive time. -/
theorem suzukiChebyshevLogAverageComplexLaplaceIntegrand_ofReal
    (lambda t : ℝ) :
    suzukiChebyshevLogAverageComplexLaplaceIntegrand (lambda : ℂ) t =
      ((Set.indicator (Set.Ioi (0 : ℝ))
        (suzukiChebyshevLogAverageLaplaceKernel lambda) t : ℝ) : ℂ) := by
  rw [suzukiChebyshevLogAverageComplexLaplaceIntegrand_eq_phase_mul_realKernel]
  simp [suzukiChebyshevLogAverageComplexLaplacePhase]

/-- On the real safe ray, the complex transform is the cast of the literal real one-sided Laplace integral. -/
theorem suzukiChebyshevLogAverageComplexLaplaceTransform_ofReal
    (lambda : ℝ) :
    suzukiChebyshevLogAverageComplexLaplaceTransform (lambda : ℂ) =
      (((∫ t in Set.Ioi (0 : ℝ),
        suzukiChebyshevLogAverageLaplaceKernel lambda t) : ℝ) : ℂ) := by
  unfold suzukiChebyshevLogAverageComplexLaplaceTransform
  rw [integral_congr_ae (Eventually.of_forall fun t =>
    suzukiChebyshevLogAverageComplexLaplaceIntegrand_ofReal lambda t)]
  calc
    (∫ t : ℝ, ((Set.indicator (Set.Ioi (0 : ℝ))
        (suzukiChebyshevLogAverageLaplaceKernel lambda) t : ℝ) : ℂ)) =
        (((∫ t : ℝ, Set.indicator (Set.Ioi (0 : ℝ))
          (suzukiChebyshevLogAverageLaplaceKernel lambda) t) : ℝ) : ℂ) :=
      integral_ofReal
    _ = (((∫ t in Set.Ioi (0 : ℝ),
        suzukiChebyshevLogAverageLaplaceKernel lambda t) : ℝ) : ℂ) := by
      rw [integral_indicator measurableSet_Ioi]

/-- On the real safe ray, the complex arithmetic Laplace transform equals its explicit
zeta-logarithmic-derivative response. -/
theorem suzukiChebyshevLogAverageComplexLaplaceTransform_ofReal_eq_zetaResponse
    {lambda : ℝ} (hlambda : 1 / 2 < lambda) :
    suzukiChebyshevLogAverageComplexLaplaceTransform (lambda : ℂ) =
      suzukiChebyshevLogAverageComplexZetaResponse (lambda : ℂ) := by
  rw [suzukiChebyshevLogAverageComplexLaplaceTransform_ofReal]
  have hchange := integral_suzukiChebyshevLogAverageLaplaceKernel_eq_mellin
    (sigma := lambda + 1 / 2)
  rw [show lambda + 1 / 2 - 1 / 2 = lambda by ring] at hchange
  rw [hchange]
  rw [ofReal_integral_neg_suzukiChebyshevLogAverageError_mul_mellinWeight_eq_logDeriv
    (sigma := lambda + 1 / 2) (by linarith)]
  unfold suzukiChebyshevLogAverageComplexZetaResponse
  rw [logDeriv_apply]
  push_cast
  congr 1 <;> ring

/-- The literal arithmetic Laplace transform equals the explicit zeta response on the entire
half-plane `Re z > 1/2`.  The extension from the real safe ray uses the identity theorem, with
the real ray embedded as an accumulating subset at `z = 1`. -/
theorem suzukiChebyshevLogAverageComplexLaplaceTransform_eqOn_zetaResponse :
    Set.EqOn suzukiChebyshevLogAverageComplexLaplaceTransform
      suzukiChebyshevLogAverageComplexZetaResponse
      suzukiChebyshevLogAverageComplexLaplaceDomain := by
  have hreal : ∃ᶠ (x : ℝ) in 𝓝[≠] (1 : ℝ),
      suzukiChebyshevLogAverageComplexLaplaceTransform (x : ℂ) =
        suzukiChebyshevLogAverageComplexZetaResponse (x : ℂ) := by
    have hsafe : ∀ᶠ (x : ℝ) in 𝓝 (1 : ℝ), 1 / 2 < x :=
      eventually_gt_nhds (by norm_num)
    exact ((hsafe.filter_mono nhdsWithin_le_nhds).mono fun x hx =>
      suzukiChebyshevLogAverageComplexLaplaceTransform_ofReal_eq_zetaResponse hx).frequently
  have hcomplex : ∃ᶠ (z : ℂ) in 𝓝[≠] (1 : ℂ),
      suzukiChebyshevLogAverageComplexLaplaceTransform z =
        suzukiChebyshevLogAverageComplexZetaResponse z := by
    rw [frequently_iff_seq_forall] at hreal ⊢
    obtain ⟨xs, hxs, heq⟩ := hreal
    refine ⟨fun n => (xs n : ℂ), ?_, fun n => heq n⟩
    rw [tendsto_nhdsWithin_iff] at hxs ⊢
    constructor
    · simpa using (tendsto_ofReal_iff.mpr hxs.1)
    · simpa using hxs.2
  exact
    analyticOnNhd_suzukiChebyshevLogAverageComplexLaplaceTransform.eqOn_of_preconnected_of_frequently_eq
      analyticOnNhd_suzukiChebyshevLogAverageComplexZetaResponse
      (by
        simpa [suzukiChebyshevLogAverageComplexLaplaceDomain] using
          (convex_halfSpace_re_gt (1 / 2 : ℝ)).isPreconnected)
      (z₀ := (1 : ℂ))
      (by norm_num [suzukiChebyshevLogAverageComplexLaplaceDomain]) hcomplex

/-- Pointwise form of the full complex arithmetic Laplace identity on `Re z > 1/2`. -/
theorem suzukiChebyshevLogAverageComplexLaplaceTransform_eq_zetaResponse
    {z : ℂ} (hz : z ∈ suzukiChebyshevLogAverageComplexLaplaceDomain) :
    suzukiChebyshevLogAverageComplexLaplaceTransform z =
      suzukiChebyshevLogAverageComplexZetaResponse z :=
  suzukiChebyshevLogAverageComplexLaplaceTransform_eqOn_zetaResponse hz

/-- Multiplication by `-i` sends a complex Laplace parameter to the spectral point whose
completed-zeta coordinate is `z + 1/2`. -/
theorem completedSpectralCoordinate_neg_I_mul_complexLaplaceParameter (z : ℂ) :
    completedSpectralCoordinate (-Complex.I * z) = z + 1 / 2 := by
  unfold completedSpectralCoordinate
  rw [show Complex.I * (-Complex.I * z) = z by
    rw [← mul_assoc]
    rw [show Complex.I * -Complex.I = 1 by
      rw [mul_neg, Complex.I_mul_I]
      norm_num]
    rw [one_mul]]
  ring

/-- At the complex Laplace spectral point, the spectral negative logarithmic derivative is
minus the completed-xi logarithmic derivative at `z + 1/2`. -/
theorem xiSpectralNegativeLogDerivative_neg_I_mul_complexLaplaceParameter (z : ℂ) :
    xiSpectralNegativeLogDerivative (-Complex.I * z) =
      -logDeriv riemannXi (z + 1 / 2) := by
  unfold xiSpectralNegativeLogDerivative
  rw [completedSpectralCoordinate_neg_I_mul_complexLaplaceParameter]
  rw [logDeriv_apply]
  ring

/-- Throughout `Re z > 1/2`, the literal complex arithmetic Laplace transform recovers the
genuine spectral-xi negative logarithmic derivative at `-i z`, with every completed-zeta
correction term explicit. -/
theorem xiSpectralNegativeLogDerivative_neg_I_mul_eq_complexLaplaceTransform_of_mem
    {z : ℂ} (hz : z ∈ suzukiChebyshevLogAverageComplexLaplaceDomain) :
    xiSpectralNegativeLogDerivative (-Complex.I * z) =
      -(z ^ 2) *
          (suzukiChebyshevLogAverageComplexLaplaceTransform z -
            4 / (z - 1 / 2)) -
        suzukiChebyshevMellinCompletedCorrection (z + 1 / 2) := by
  have hs : (1 : ℝ) < (z + 1 / 2).re :=
    mapsTo_add_half_suzukiChebyshevLogAverageComplexLaplaceDomain hz
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    norm_num [suzukiChebyshevLogAverageComplexLaplaceDomain] at hz
  have hD : z ^ 2 ≠ 0 := pow_ne_zero 2 hz0
  rw [suzukiChebyshevLogAverageComplexLaplaceTransform_eq_zetaResponse hz]
  unfold suzukiChebyshevLogAverageComplexZetaResponse
  rw [logDeriv_riemannZeta_eq_logDeriv_riemannXi_sub_mellinCompletedCorrection hs]
  rw [show logDeriv riemannXi (z + 1 / 2) =
      -xiSpectralNegativeLogDerivative (-Complex.I * z) by
    rw [xiSpectralNegativeLogDerivative_neg_I_mul_complexLaplaceParameter]
    ring]
  let D : ℂ := z ^ 2
  let X : ℂ := xiSpectralNegativeLogDerivative (-Complex.I * z)
  let C : ℂ := suzukiChebyshevMellinCompletedCorrection (z + 1 / 2)
  let P : ℂ := 4 / (z - 1 / 2)
  change X = -D * ((-X - C) / D + P - P) - C
  rw [show (-X - C) / D + P - P = (-X - C) / D by ring]
  rw [div_eq_mul_inv]
  calc
    X = -((D * D⁻¹) * (-X - C)) - C := by
      rw [mul_inv_cancel₀ hD]
      ring
    _ = -D * ((-X - C) * D⁻¹) - C := by ring

/-- The safe-ray spectral-xi logarithmic derivative is recovered through the literal complex Laplace transform. -/
theorem xiSpectralNegativeLogDerivative_neg_I_mul_eq_complexLaplaceTransform
    {lambda : ℝ} (hlambda : 1 / 2 < lambda) :
    xiSpectralNegativeLogDerivative (-Complex.I * (lambda : ℂ)) =
      -((lambda ^ 2 : ℝ) : ℂ) *
          (suzukiChebyshevLogAverageComplexLaplaceTransform (lambda : ℂ) -
            ((4 / (lambda - 1 / 2) : ℝ) : ℂ)) -
        suzukiChebyshevMellinCompletedCorrection
          ((lambda + 1 / 2 : ℝ) : ℂ) := by
  rw [suzukiChebyshevLogAverageComplexLaplaceTransform_ofReal]
  exact xiSpectralNegativeLogDerivative_neg_I_mul_eq_laplaceTransform hlambda

end

end RiemannGaussian
