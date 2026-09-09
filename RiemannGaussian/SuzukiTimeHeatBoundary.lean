/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiTimeHeat

/-!
# The signed boundary correction in Suzuki time heat

On nonpositive time there are no prime hinges. Consequently the full-line
heat average of the affine-centered Legendre signal differs from the
causal Suzuki heat by one explicit positive elementary integral. For
nonnegative center `a` it is at most `4*exp(-a^2/(4*tau))`.

This controls the actual support-completion boundary, uniformly in the
arithmetic coefficients. It does not bound the surviving prime signal.
-/

namespace RiemannGaussian
noncomputable section
open Filter MeasureTheory Set
open scoped Topology

private theorem timeGaussian_integrable {tau : ℝ} (htau : 0 < tau) (a : ℝ) :
    Integrable (fun u : ℝ => Real.exp (-(a - u) ^ 2 / (4 * tau))) := by
  have h := (integrable_exp_neg_mul_sq (show 0 < 1 / (4 * tau) by positivity)).comp_sub_left a
  convert h using 1
  ext u
  congr 1
  ring

private theorem timeGaussian_mass {tau : ℝ} (htau : 0 < tau) (a : ℝ) :
    (Real.sqrt (Real.pi / tau) / (2 * Real.pi)) *
      (∫ u : ℝ, Real.exp (-(a - u) ^ 2 / (4 * tau))) = 1 := by
  have heq (u : ℝ) : -(a - u) ^ 2 / (4 * tau) =
      -(1 / (4 * tau)) * (a - u) ^ 2 := by ring
  simp_rw [heq]
  rw [integral_sub_left_eq_self
    (fun v : ℝ => Real.exp (-(1 / (4 * tau)) * v ^ 2)) volume a,
    integral_gaussian, suzukiLogTimeHeat_normalization htau]
  rw [show Real.pi / (1 / (4 * tau)) = 4 * Real.pi * tau by field_simp]
  exact one_div_mul_cancel (Real.sqrt_pos.mpr (by positivity)).ne'

/-- Before the first prime event, the full Legendre signal is exactly its
exponential-affine background. In particular this holds on negative time. -/
theorem suzukiLegendreSignal_nonpositive {u : ℝ} (hu : u ≤ 0) :
    suzukiLegendreSignal u = suzukiArchimedeanIntercept + 4 * Real.exp (u / 2) +
      suzukiArchimedeanSlopeConstant * u := by
  have hzero (n : ℕ) : screwNegativeHinge (suzukiPrimeWeight n) (suzukiPrimeLocation n) u = 0 := by
    apply screwNegativeHinge_eq_zero_of_le_location
    apply hu.trans
    exact Real.log_nonneg (by norm_cast; omega)
  simp only [suzukiLegendreSignal, screwHingeModel, hzero, tsum_zero, add_zero]

/-- The sole correction from completing the causal signal to the full
affine-centered Legendre signal. Its sign is kept in the definition. -/
def suzukiTimeHeatBoundary (tau a : ℝ) : ℝ :=
  (Real.sqrt (Real.pi / tau) / (2 * Real.pi)) *
    ∫ u : ℝ in Iic 0, 4 * Real.exp (u / 2) * Real.exp (-(a - u) ^ 2 / (4 * tau))

private theorem boundary_integrable {tau : ℝ} (htau : 0 < tau) (a : ℝ) :
    IntegrableOn (fun u : ℝ => 4 * Real.exp (u / 2) *
      Real.exp (-(a - u) ^ 2 / (4 * tau))) (Iic 0) := by
  apply ((timeGaussian_integrable htau a).integrableOn.const_mul 4).mono'
  · exact (show Continuous (fun u : ℝ => 4 * Real.exp (u / 2) *
      Real.exp (-(a - u) ^ 2 / (4 * tau))) by fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
    change u ≤ 0 at hu
    rw [Real.norm_of_nonneg (by positivity)]
    have he : Real.exp (u / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hu])
    nlinarith [Real.exp_pos (-(a - u) ^ 2 / (4 * tau))]

private theorem centeredLegendre_split (u : ℝ) :
    suzukiLegendreSignal u - suzukiArchimedeanSlopeConstant * u -
      suzukiArchimedeanIntercept =
      (Ioi 0).indicator suzukiChebyshevLogAverageLaplaceSignal u +
        (Iic 0).indicator (fun v => 4 * Real.exp (v / 2)) u := by
  by_cases hu : 0 < u
  · rw [indicator_of_mem (show u ∈ Ioi 0 from hu), indicator_of_notMem (show u ∉ Iic 0 by simpa using hu),
      suzukiLegendreSignal_eq_laplace_add_affine hu.le]
    ring
  · rw [indicator_of_notMem (show u ∉ Ioi 0 from hu), indicator_of_mem (show u ∈ Iic 0 from le_of_not_gt hu),
      suzukiLegendreSignal_nonpositive (le_of_not_gt hu)]
    ring

private theorem centeredLegendre_heat_split (a tau u : ℝ) :
    (suzukiLegendreSignal u - suzukiArchimedeanSlopeConstant * u -
      suzukiArchimedeanIntercept) * Real.exp (-(a - u) ^ 2 / (4 * tau)) =
      (Ioi 0).indicator (fun v => suzukiChebyshevLogAverageLaplaceSignal v *
        Real.exp (-(a - v) ^ 2 / (4 * tau))) u +
      (Iic 0).indicator (fun v => 4 * Real.exp (v / 2) *
        Real.exp (-(a - v) ^ 2 / (4 * tau))) u := by
  rw [centeredLegendre_split, add_mul,
    indicator_mul_left (Ioi 0) suzukiChebyshevLogAverageLaplaceSignal
      (fun v => Real.exp (-(a - v) ^ 2 / (4 * tau))),
    indicator_mul_left (Iic 0) (fun v => 4 * Real.exp (v / 2))
      (fun v => Real.exp (-(a - v) ^ 2 / (4 * tau)))]
/-- The full-line affine-centered Legendre heat integral is genuinely
integrable. Its causal and nonpositive-time pieces are both accounted for. -/
theorem integrable_centeredSuzukiLegendre_timeGaussian {tau : ℝ}
    (htau : 0 < tau) (a : ℝ) :
    Integrable (fun u : ℝ =>
      (suzukiLegendreSignal u - suzukiArchimedeanSlopeConstant * u -
        suzukiArchimedeanIntercept) * Real.exp (-(a - u) ^ 2 / (4 * tau))) := by
  simp_rw [centeredLegendre_heat_split]
  exact ((integrable_indicator_iff measurableSet_Ioi).mpr
    (integrableOn_suzukiSignal_timeGaussian htau a)).add
      ((integrable_indicator_iff measurableSet_Iic).mpr (boundary_integrable htau a))

/-- Exact signed completion formula before bounding the boundary term. -/
theorem centeredSuzukiLegendre_timeHeat_eq {tau : ℝ} (htau : 0 < tau) (a : ℝ) :
    (Real.sqrt (Real.pi / tau) / (2 * Real.pi)) *
      (∫ u : ℝ, (suzukiLegendreSignal u - suzukiArchimedeanSlopeConstant * u -
        suzukiArchimedeanIntercept) * Real.exp (-(a - u) ^ 2 / (4 * tau))) =
      suzukiLogTimeHeat tau a + suzukiTimeHeatBoundary tau a := by
  simp_rw [centeredLegendre_heat_split]
  rw [integral_add
    ((integrable_indicator_iff measurableSet_Ioi).mpr (integrableOn_suzukiSignal_timeGaussian htau a))
    ((integrable_indicator_iff measurableSet_Iic).mpr (boundary_integrable htau a)),
    integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Iic, mul_add]
  rfl

/-- The completion boundary is positive and exponentially small at
nonnegative centers. This estimate is independent of zeta-zero assumptions
and of the surviving signed prime sum. -/
theorem suzukiTimeHeatBoundary_bounds {tau a : ℝ} (htau : 0 < tau) (ha : 0 ≤ a) :
    0 ≤ suzukiTimeHeatBoundary tau a ∧
      suzukiTimeHeatBoundary tau a ≤ 4 * Real.exp (-a ^ 2 / (4 * tau)) := by
  constructor
  · unfold suzukiTimeHeatBoundary
    exact mul_nonneg (by positivity) (integral_nonneg fun _ => by positivity)
  · have hpoint (u : ℝ) (hu : u ∈ Iic 0) :
        4 * Real.exp (u / 2) * Real.exp (-(a - u) ^ 2 / (4 * tau)) ≤
          (4 * Real.exp (-a ^ 2 / (4 * tau))) * Real.exp (-(0 - u) ^ 2 / (4 * tau)) := by
      change u ≤ 0 at hu
      have he : Real.exp (u / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hu])
      have hx : -(a - u) ^ 2 / (4 * tau) ≤
          -a ^ 2 / (4 * tau) + -(0 - u) ^ 2 / (4 * tau) := by
        rw [← add_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [mul_nonpos_of_nonneg_of_nonpos ha hu]
      have hexp := Real.exp_le_exp.mpr hx
      rw [Real.exp_add] at hexp
      nlinarith [Real.exp_pos (-(a - u) ^ 2 / (4 * tau))]
    have hi := integral_mono_ae (boundary_integrable htau a)
      ((timeGaussian_integrable htau 0).integrableOn.const_mul
        (4 * Real.exp (-a ^ 2 / (4 * tau))))
      (by filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu using hpoint u hu)
    rw [integral_const_mul] at hi
    have hmass := setIntegral_le_integral (s := Iic (0 : ℝ)) (timeGaussian_integrable htau 0)
      (Eventually.of_forall fun _ => (Real.exp_pos _).le)
    have hc : 0 ≤ Real.sqrt (Real.pi / tau) / (2 * Real.pi) := by positivity
    unfold suzukiTimeHeatBoundary
    calc
      _ ≤ (Real.sqrt (Real.pi / tau) / (2 * Real.pi)) *
          ((4 * Real.exp (-a ^ 2 / (4 * tau))) *
            ∫ u : ℝ in Iic 0, Real.exp (-(0 - u) ^ 2 / (4 * tau))) :=
        mul_le_mul_of_nonneg_left hi hc
      _ ≤ (Real.sqrt (Real.pi / tau) / (2 * Real.pi)) *
          ((4 * Real.exp (-a ^ 2 / (4 * tau))) *
            ∫ u : ℝ, Real.exp (-(0 - u) ^ 2 / (4 * tau))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass (by positivity)) hc
      _ = 4 * Real.exp (-a ^ 2 / (4 * tau)) := by
        rw [mul_left_comm, timeGaussian_mass htau 0, mul_one]

/-- Every eventually positive sublinear width schedule makes the actual
completion boundary exponentially small in the center. -/
theorem suzukiTimeHeatBoundary_eventually_bounds_of_sublinear
    {tau : ℝ → ℝ} (hpos : ∀ᶠ a : ℝ in atTop, 0 < tau a)
    (htau : Tendsto (fun a => tau a / a) atTop (𝓝 0)) :
    ∀ᶠ a : ℝ in atTop, 0 ≤ suzukiTimeHeatBoundary (tau a) a ∧
      suzukiTimeHeatBoundary (tau a) a ≤ 4 * Real.exp (-a / 4) := by
  filter_upwards [hpos, htau.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    eventually_gt_atTop (0 : ℝ)] with a hpa hta ha
  have hwidth : tau a ≤ a := by
    have h := (div_lt_iff₀ ha).mp hta
    linarith
  have hexponent : -a ^ 2 / (4 * tau a) ≤ -a / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * tau a)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hwidth ha.le]
  have hb := suzukiTimeHeatBoundary_bounds hpa ha.le
  exact ⟨hb.1, hb.2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
    (by norm_num))⟩

/-- The signed boundary correction tends to zero for every eventually
positive sublinear heat-width schedule. The remaining arithmetic integral
is not part of this error estimate. -/
theorem tendsto_suzukiTimeHeatBoundary_zero_of_sublinear
    {tau : ℝ → ℝ} (hpos : ∀ᶠ a : ℝ in atTop, 0 < tau a)
    (htau : Tendsto (fun a => tau a / a) atTop (𝓝 0)) :
    Tendsto (fun a => suzukiTimeHeatBoundary (tau a) a) atTop (𝓝 0) := by
  have hb := suzukiTimeHeatBoundary_eventually_bounds_of_sublinear hpos htau
  have hexp : Tendsto (fun a : ℝ => 4 * Real.exp (-a / 4)) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 4))).const_mul 4
    simpa only [mul_zero, neg_div, Function.comp_apply, id_eq] using h
  exact squeeze_zero' (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2) hexp

/-- The actual support-completion error is negligible compared with every
hypothetical right-half-zero source, for every eventually positive
sublinear width schedule. This leaves the full signed arithmetic response
as the independent inequality still needed for a contradiction. -/
theorem tendsto_suzukiTimeHeatBoundary_div_source_zero
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {tau : ℝ → ℝ} (hpos : ∀ᶠ a : ℝ in atTop, 0 < tau a)
    (htau : Tendsto (fun a => tau a / a) atTop (𝓝 0)) :
    Tendsto (fun a => suzukiTimeHeatBoundary (tau a) a /
      ‖suzukiTimeHeatZeroSource rho a (tau a)‖) atTop (𝓝 0) :=
  (tendsto_suzukiTimeHeatBoundary_zero_of_sublinear hpos htau).div_atTop
    (tendsto_norm_suzukiTimeHeatZeroSource_atTop_of_sublinear rho hrho htau)

end
end RiemannGaussian
