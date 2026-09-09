/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatPuncture
import RiemannGaussian.EtaZetaPrimeProduct
import RiemannGaussian.PositiveLaplaceLandau
import RiemannGaussian.SuzukiQuadraticMassObstruction

/-!
# Arithmetic Suzuki positivity implies the Riemann hypothesis

This module closes the analytic direction from positivity of the literal
Suzuki function on `t >= log 2` to Mathlib's `RiemannHypothesis`.

The exact prime formula and a source-exact Archimedean upper bound make the
actual logarithmic-average Laplace signal nonnegative. The positive measure
then satisfies the Landau continuation theorem: its genuine integral
converges for every positive damping because the completed response is
analytic along the positive real axis. The latter fact uses the existing
eta-mass exclusion of real zeta zeros.

The actual complex integral is consequently holomorphic throughout `Re z > 0`.
Clearing the xi denominator extends its safe-half-plane identity across the
putative divisor. At every hypothetical right-half zero, the established
positive multiplicity residue must then be zero, a contradiction. The
functional equation supplies the other half of the critical strip.

The arithmetic positivity premise remains open. This module proves the
complete conditional implication, not that premise and not unconditional RH.
-/

namespace RiemannGaussian
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped Topology ENNReal

/-- Exact identification of the logarithmic-average signal and the literal prime term. -/
theorem suzukiChebyshevLogAverageLaplaceSignal_eq_main_sub_prime
    {t : ℝ} (ht : 0 ≤ t) :
    suzukiChebyshevLogAverageLaplaceSignal t =
      4 * Real.exp (t / 2) - suzukiPointwisePrimeContribution t := by
  have hexp : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  have hfloor : 1 ≤ ⌊Real.exp t⌋₊ := (Nat.le_floor_iff (Real.exp_nonneg t)).mpr
    (by exact_mod_cast hexp)
  have hsum := Finset.add_sum_Ioc_eq_sum_Icc
    (f := suzukiPointwisePrimeTerm t) hfloor
  simp only [suzukiPointwisePrimeTerm, ArithmeticFunction.vonMangoldt_apply_one,
    zero_div, zero_mul, zero_add] at hsum
  unfold suzukiChebyshevLogAverageLaplaceSignal
  rw [suzukiChebyshevLogAverageError_eq_sum_log_sub_log_of_one_le hexp,
    Real.log_exp, ← Real.exp_mul]
  rw [hsum]
  unfold suzukiPointwisePrimeContribution suzukiArithmeticPrimeWindow suzukiPointwisePrimeTerm
  rw [show t * (1 / 2 : ℝ) = t / 2 by ring]
  ring

/-- Tail positivity of the literal Suzuki function makes its actual logarithmic-average
Laplace signal positive on all positive time, including the prime-free initial interval. -/
theorem suzukiChebyshevLogAverageLaplaceSignal_pos_of_psi_nonnegative
    (hpsi : ∀ t : ℝ, Real.log 2 ≤ t → 0 ≤ riemannXiSuzukiPsiNonnegative t)
    {t : ℝ} (ht : 0 < t) :
    0 < suzukiChebyshevLogAverageLaplaceSignal t := by
  rw [suzukiChebyshevLogAverageLaplaceSignal_eq_main_sub_prime ht.le]
  by_cases htail : Real.log 2 ≤ t
  · have h := hpsi t htail
    unfold riemannXiSuzukiPsiNonnegative at h
    linarith [suzukiPointwiseArchimedean_lt_four_mul_exp_half ht.le]
  · rw [suzukiPointwisePrimeContribution_eq_zero_of_lt_log_two ht.le (lt_of_not_ge htail)]
    rw [sub_zero]
    exact mul_pos (by norm_num) (Real.exp_pos _)

/-- Xi has no zero on the real axis; the existing eta-mass theorem excludes them. -/
theorem riemannXi_ofReal_ne_zero (x : ℝ) : riemannXi (x : ℂ) ≠ 0 := by
  intro hx
  let rho : NontrivialZetaZero := ⟨(x : ℂ), isNontrivialZetaZero_of_riemannXi_eq_zero hx⟩
  exact NontrivialZetaZero.im_ne_zero_of_eta_mass rho (by simp [rho])

/-- The real completed response is analytic along the full positive Laplace axis. -/
theorem analyticOnNhd_suzukiCompletedResponse_neg_real :
    AnalyticOnNhd ℝ (fun x : ℝ =>
      (suzukiChebyshevLogAverageLaplaceCompletedContinuation (-x : ℂ)).re) (Iio 0) := by
  intro x hx
  change x < 0 at hx
  have hm : (-x : ℂ) ∈ suzukiChebyshevLogAverageLaplaceContinuationDomain := by
    refine ⟨?_, ?_, ?_⟩
    · intro hz
      have hre := congrArg Complex.re hz
      norm_num at hre
      linarith
    · norm_num [Complex.div_re]
      linarith
    · convert riemannXi_ofReal_ne_zero (-x + 1 / 2) using 1
      push_cast
      rfl
  have h := analyticOnNhd_suzukiChebyshevLogAverageLaplaceCompletedContinuation (-x) hm
  exact (h.comp (analyticAt_id.neg)).re_ofReal

/-- The actual logarithmic-average signal is measurable on positive time. -/
theorem aemeasurable_suzukiChebyshevLogAverageLaplaceSignal :
    AEMeasurable suzukiChebyshevLogAverageLaplaceSignal (volume.restrict (Ioi 0)) := by
  have h := (integrableOn_suzukiChebyshevLogAverageLaplaceKernel
    (lambda := 1) (by norm_num)).aestronglyMeasurable
  have he : AEStronglyMeasurable Real.exp (volume.restrict (Ioi (0 : ℝ))) :=
    Real.continuous_exp.aestronglyMeasurable
  have hh := (h.mul he).aemeasurable
  convert hh using 1
  funext t
  simp only [suzukiChebyshevLogAverageLaplaceKernel, Pi.mul_apply, neg_mul, one_mul]
  rw [mul_assoc, ← Real.exp_add]
  simp

/-- The positive-part measure of the literal signal. Under signal positivity,
its weighted integrals are exactly the original arithmetic Laplace integrals. -/
def suzukiPositiveLaplaceMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun t => ENNReal.ofReal (suzukiChebyshevLogAverageLaplaceSignal t))

private theorem ae_nonneg_time_suzukiPositiveLaplaceMeasure :
    ∀ᵐ t ∂suzukiPositiveLaplaceMeasure, 0 ≤ t := by
  rw [suzukiPositiveLaplaceMeasure,
    ae_withDensity_iff' aemeasurable_suzukiChebyshevLogAverageLaplaceSignal.ennreal_ofReal]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact fun _ => le_of_lt ht

private theorem integral_suzukiPositiveLaplaceMeasure
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ suzukiChebyshevLogAverageLaplaceSignal t)
    (f : ℝ → ℂ) :
    (∫ t, f t ∂suzukiPositiveLaplaceMeasure) =
      ∫ t in Ioi (0 : ℝ), (suzukiChebyshevLogAverageLaplaceSignal t : ℂ) * f t := by
  rw [suzukiPositiveLaplaceMeasure,
    integral_withDensity_eq_integral_toReal_smul₀
      aemeasurable_suzukiChebyshevLogAverageLaplaceSignal.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [ENNReal.toReal_ofReal (hpos t ht), Complex.real_smul]

private theorem complexMGF_suzukiPositiveLaplaceMeasure
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ suzukiChebyshevLogAverageLaplaceSignal t)
    (z : ℂ) :
    complexMGF id suzukiPositiveLaplaceMeasure (-z) =
      suzukiChebyshevLogAverageComplexLaplaceTransform z := by
  rw [complexMGF, integral_suzukiPositiveLaplaceMeasure hpos]
  unfold suzukiChebyshevLogAverageComplexLaplaceTransform
    suzukiChebyshevLogAverageComplexLaplaceIntegrand
  rw [integral_indicator measurableSet_Ioi]
  rfl

private theorem mem_integrableExpSet_suzukiPositiveLaplaceMeasure_safe
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ suzukiChebyshevLogAverageLaplaceSignal t)
    {x : ℝ} (hx : x < -1 / 2) :
    x ∈ integrableExpSet id suzukiPositiveLaplaceMeasure := by
  change Integrable (fun t : ℝ => Real.exp (x * t)) _
  rw [suzukiPositiveLaplaceMeasure,
    integrable_withDensity_iff_integrable_smul₀'
      aemeasurable_suzukiChebyshevLogAverageLaplaceSignal.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hi := integrableOn_suzukiChebyshevLogAverageLaplaceKernel
    (lambda := -x) (by linarith)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp [ENNReal.toReal_ofReal (hpos t ht), suzukiChebyshevLogAverageLaplaceKernel]

/-- Positivity forces genuine convergence of the arithmetic Laplace measure
at every positive damping, not merely meromorphic continuation there. -/
theorem Iio_zero_subset_interior_integrableExpSet_suzukiPositiveLaplaceMeasure
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ suzukiChebyshevLogAverageLaplaceSignal t) :
    Iio (0 : ℝ) ⊆ interior (integrableExpSet id suzukiPositiveLaplaceMeasure) := by
  apply Iio_subset_interior_integrableExpSet_of_analytic_mgf
    measurable_id.aemeasurable ae_nonneg_time_suzukiPositiveLaplaceMeasure
    (a := -1 / 2)
    (fun _ hx => mem_integrableExpSet_suzukiPositiveLaplaceMeasure_safe hpos hx)
    analyticOnNhd_suzukiCompletedResponse_neg_real
  intro x hx
  change x < -1 / 2 at hx
  have heq := complexMGF_suzukiPositiveLaplaceMeasure hpos (-x : ℂ)
  rw [suzukiChebyshevLogAverageComplexLaplaceTransform_eq_completedContinuation
    (by change (1 / 2 : ℝ) < (-x : ℂ).re; simp only [neg_re, ofReal_re]; linarith)] at heq
  have hre := congrArg Complex.re heq
  simpa only [neg_neg, complexMGF_ofReal, ofReal_re] using hre.symm

/-- Under arithmetic signal positivity the literal complex transform is
holomorphic throughout the open positive half-plane. -/
theorem analyticOnNhd_suzukiLaplaceTransform_of_signal_nonnegative
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ suzukiChebyshevLogAverageLaplaceSignal t) :
    AnalyticOnNhd ℂ suzukiChebyshevLogAverageComplexLaplaceTransform
      {z : ℂ | 0 < z.re} := by
  intro z hz
  change 0 < z.re at hz
  have hi : (-z).re ∈ interior (integrableExpSet id suzukiPositiveLaplaceMeasure) :=
    Iio_zero_subset_interior_integrableExpSet_suzukiPositiveLaplaceMeasure hpos
      (by simp only [mem_Iio, neg_re]; linarith)
  have h := (analyticAt_complexMGF hi).comp (analyticAt_id.neg)
  apply h.congr
  filter_upwards with w
  exact complexMGF_suzukiPositiveLaplaceMeasure hpos w


/-- Clearing the actual xi denominator gives a holomorphic identity on the whole
positive half-plane, including the putative divisor. -/
theorem deriv_riemannXi_eq_mul_of_suzukiLaplace_extension
    (H : ℂ → ℂ)
    (hH : AnalyticOnNhd ℂ H {z : ℂ | 0 < z.re})
    (hagree : ∀ z : ℂ, 1 / 2 < z.re →
      H z = suzukiChebyshevLogAverageComplexLaplaceTransform z)
    {z : ℂ} (hz : 0 < z.re) :
    deriv riemannXi (z + 1 / 2) = riemannXi (z + 1 / 2) *
      (z ^ 2 * H z -
        suzukiChebyshevLogAverageLaplaceRegularCorrection z) := by
  let D : Set ℂ := {z | 0 < z.re}
  have hshift : AnalyticOnNhd ℂ (fun z : ℂ => z + 1 / 2) D :=
    analyticOnNhd_id.add analyticOnNhd_const
  have hxi : AnalyticOnNhd ℂ (fun z : ℂ => riemannXi (z + 1 / 2)) D :=
    analyticOnNhd_riemannXi.comp hshift (fun _ _ => mem_univ _)
  have hderiv : AnalyticOnNhd ℂ (fun z : ℂ => deriv riemannXi (z + 1 / 2)) D :=
    analyticOnNhd_riemannXi.deriv.comp hshift (fun _ _ => mem_univ _)
  have hreg : AnalyticOnNhd ℂ suzukiChebyshevLogAverageLaplaceRegularCorrection D :=
    analyticOnNhd_suzukiChebyshevLogAverageLaplaceRegularCorrection.mono (by
      intro w hw
      change 0 < w.re at hw
      change 0 < (w + 1 / 2).re
      norm_num [Complex.div_re]
      linarith)
  have hrhs := hxi.mul (((analyticOnNhd_id.pow 2).mul
    hH).sub hreg)
  have hlocal : (fun w : ℂ => deriv riemannXi (w + 1 / 2)) =ᶠ[𝓝 (1 : ℂ)]
      (fun w : ℂ => riemannXi (w + 1 / 2) *
        (w ^ 2 * H w -
          suzukiChebyshevLogAverageLaplaceRegularCorrection w)) := by
    have hsafe : ∀ᶠ w in 𝓝 (1 : ℂ), (1 / 2 : ℝ) < w.re :=
      isOpen_suzukiChebyshevLogAverageComplexLaplaceDomain.mem_nhds
        (by change (1 / 2 : ℝ) < (1 : ℂ).re; norm_num)
    filter_upwards [hsafe] with w hw
    have hxi0 := (mem_suzukiChebyshevLogAverageLaplaceContinuationDomain_of_half_le_re hw.le).2.2
    have hw0 : w ≠ 0 := by
      intro he
      subst w
      norm_num at hw
    rw [hagree w hw,
      suzukiChebyshevLogAverageComplexLaplaceTransform_eq_completedContinuation hw]
    unfold suzukiChebyshevLogAverageLaplaceCompletedContinuation
      suzukiChebyshevLogAverageLaplaceRegularCorrection logDeriv
    simp only [Pi.div_apply]
    generalize riemannXi (w + 1 / 2) = a at hxi0 ⊢
    field_simp [hxi0, hw0]
    ring
  have hconn : IsPreconnected D := (convex_Ioi (0 : ℝ)).linear_preimage reLm |>.isPreconnected
  exact hderiv.eqOn_of_preconnected_of_eventuallyEq hrhs hconn
    (show (1 : ℂ) ∈ D by change 0 < (1 : ℂ).re; norm_num) hlocal hz

/-- A genuinely holomorphic arithmetic transform cannot carry the positive
multiplicity residue of any zero to the right of the critical line. -/
theorem nontrivialZero_re_le_half_of_suzukiLaplace_extension
    (H : ℂ → ℂ)
    (hH : AnalyticOnNhd ℂ H {z : ℂ | 0 < z.re})
    (hagree : ∀ z : ℂ, 1 / 2 < z.re →
      H z = suzukiChebyshevLogAverageComplexLaplaceTransform z)
    (rho : NontrivialZetaZero) : rho.1.re ≤ 1 / 2 := by
  by_contra hrho
  have hrho : (1 / 2 : ℝ) < rho.1.re := lt_of_not_ge hrho
  let p := suzukiChebyshevLaplaceZeroCoordinate rho
  have hp : 0 < p.re := by
    dsimp [p, suzukiChebyshevLaplaceZeroCoordinate]
    norm_num [Complex.div_re]
    linarith
  let G : ℂ → ℂ := fun z =>
    z ^ 2 * H z -
      suzukiChebyshevLogAverageLaplaceRegularCorrection z
  have hG : AnalyticAt ℂ G p := by
    have hreg := analyticOnNhd_suzukiChebyshevLogAverageLaplaceRegularCorrection p
      (by change 0 < (p + 1 / 2).re; norm_num [Complex.div_re]; linarith)
    exact ((analyticAt_id.pow 2).mul
      (hH p hp)).sub hreg
  have hnear : ∀ᶠ z in 𝓝[≠] p, logDeriv riemannXi (z + 1 / 2) = G z := by
    have hpositive : ∀ᶠ z in 𝓝 p, 0 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp
    filter_upwards [hpositive.filter_mono nhdsWithin_le_nhds,
      eventually_mem_suzukiChebyshevLogAverageLaplacePoleClearedDomain_punctured rho]
      with z hz hxi
    rw [logDeriv, Pi.div_apply,
      deriv_riemannXi_eq_mul_of_suzukiLaplace_extension H hH hagree hz]
    exact mul_div_cancel_left₀ (G z) hxi.2
  have hzero : Tendsto (fun z : ℂ => (z - p) * G z) (𝓝[≠] p) (𝓝 0) := by
    have h : Tendsto (fun z : ℂ => (z - p) * G z) (𝓝 p) (𝓝 ((p - p) * G p)) :=
      (tendsto_id.sub tendsto_const_nhds).mul hG.continuousAt.tendsto
    simpa only [sub_self, zero_mul] using h.mono_left nhdsWithin_le_nhds
  have hzero' : Tendsto (fun z : ℂ => (z - p) * logDeriv riemannXi (z + 1 / 2))
      (𝓝[≠] p) (𝓝 0) := hzero.congr' (hnear.mono fun z he =>
        congrArg (fun v : ℂ => (z - p) * v) he.symm)
  have heq := tendsto_nhds_unique
    (tendsto_suzukiChebyshevLaplaceZeroCoordinate_mul_logDeriv_riemannXi rho) hzero'
  have hm : (analyticZetaZeroMultiplicity rho : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (analyticZetaZeroMultiplicity_positive rho))
  exact hm heq

/-- A holomorphic continuation of the actual arithmetic transform throughout
the positive half-plane implies Mathlib's RH. -/
theorem riemannHypothesis_of_suzukiLaplace_extension
    (H : ℂ → ℂ)
    (hH : AnalyticOnNhd ℂ H {z : ℂ | 0 < z.re})
    (hagree : ∀ z : ℂ, 1 / 2 < z.re →
      H z = suzukiChebyshevLogAverageComplexLaplaceTransform z) :
    RiemannHypothesis := by
  intro s hs htriv hone
  let rho : NontrivialZetaZero := ⟨s, hs, htriv, hone⟩
  have hupper := nontrivialZero_re_le_half_of_suzukiLaplace_extension H hH hagree rho
  have hlower := nontrivialZero_re_le_half_of_suzukiLaplace_extension H hH hagree rho.conjugatePartner
  simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re,
    Complex.one_re, Complex.conj_re] at hlower
  change s.re ≤ 1 / 2 at hupper
  change 1 - s.re ≤ 1 / 2 at hlower
  linarith

/-- Clearing the actual xi denominator under the arithmetic positivity hypothesis. -/
theorem deriv_riemannXi_eq_mul_suzukiLaplaceTransform_of_signal_nonnegative
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ suzukiChebyshevLogAverageLaplaceSignal t)
    {z : ℂ} (hz : 0 < z.re) :
    deriv riemannXi (z + 1 / 2) = riemannXi (z + 1 / 2) *
      (z ^ 2 * suzukiChebyshevLogAverageComplexLaplaceTransform z -
        suzukiChebyshevLogAverageLaplaceRegularCorrection z) :=
  deriv_riemannXi_eq_mul_of_suzukiLaplace_extension _
    (analyticOnNhd_suzukiLaplaceTransform_of_signal_nonnegative hpos) (fun _ _ => rfl) hz

/-- Signal positivity excludes every nontrivial zero right of the critical line. -/
theorem nontrivialZero_re_le_half_of_suzuki_signal_nonnegative
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ suzukiChebyshevLogAverageLaplaceSignal t)
    (rho : NontrivialZetaZero) : rho.1.re ≤ 1 / 2 :=
  nontrivialZero_re_le_half_of_suzukiLaplace_extension _
    (analyticOnNhd_suzukiLaplaceTransform_of_signal_nonnegative hpos) (fun _ _ => rfl) rho

/-- The literal nonnegative logarithmic-average signal implies Mathlib's RH. -/
theorem riemannHypothesis_of_suzuki_signal_nonnegative
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ suzukiChebyshevLogAverageLaplaceSignal t) :
    RiemannHypothesis :=
  riemannHypothesis_of_suzukiLaplace_extension _
    (analyticOnNhd_suzukiLaplaceTransform_of_signal_nonnegative hpos) (fun _ _ => rfl)

/-- Tail positivity of Suzuki's actual arithmetic function implies Mathlib's RH;
all Laplace convergence, analytic continuation and multiplicity steps are discharged. -/
theorem riemannHypothesis_of_suzuki_psi_nonnegative_tail
    (hpsi : ∀ t : ℝ, Real.log 2 ≤ t → 0 ≤ riemannXiSuzukiPsiNonnegative t) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_suzuki_signal_nonnegative
    (fun _ ht => (suzukiChebyshevLogAverageLaplaceSignal_pos_of_psi_nonnegative hpsi ht).le)

end
end RiemannGaussian
