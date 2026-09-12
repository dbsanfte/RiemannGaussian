/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.AnalyticStripBoundaryIntegral
import RiemannGaussian.ClippedLogNorm
import RiemannGaussian.ZetaStripBoundaryEnvelope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The actual radial strip boundary limit with retained negative depth

Only the left logarithm is clipped, at an arbitrary nonnegative depth.
The right logarithm stays fully signed on its nonzero Euler half-plane.
The original real projection supplies a uniform integrable dominator on
the complete height line. Every radial integral and its boundary limit is
therefore an ordinary Bochner integral, with all exchanges justified.
-/

namespace RiemannGaussian.ZetaStripBoundaryLimit
noncomputable section
open Complex Filter MeasureTheory Metric Set
open AnalyticStripBoundary AnalyticStripBoundaryIntegral
open ZetaGaussianLocalizer ZetaStripDisc ZetaStripBoundaryEnvelope
open scoped Topology

/-- The right arc retains its original signed logarithmic projection. -/
def rightProjection (c : ℂ) (η r u : ℝ) : ℝ :=
  (1 / Real.cosh u) * (-((r : ℂ) * right u).re *
    Real.log ‖carrier c η ((r : ℂ) * right u)‖)

/-- The left arc retains all negative depth above the arbitrary clipping floor. -/
def leftProjection (c : ℂ) (η M r u : ℝ) : ℝ :=
  (1 / Real.cosh u) * (-((r : ℂ) * left u).re *
    ClippedLogNorm.value M (carrier c η ((r : ℂ) * left u)))

/-- One finite constant dominates both projected arcs; its height dependence
is used per channel and is not summed over phase frequencies. -/
def envelope (c : ℂ) (η M : ℝ) : ℝ :=
  (52 + 2 * |c.im| + 8 * η / Real.pi) +
    (1 + 1 / (c.re - 1)) * (1 + 2 / (c.re - 1)) + M

private theorem norm_radial_right {r : ℝ} (hr : 0 ≤ r) (u : ℝ) :
    ‖(r : ℂ) * right u‖ = r := by rw [norm_mul, norm_real, Real.norm_eq_abs, norm_right,
      abs_of_nonneg hr, mul_one]

private theorem norm_radial_left {r : ℝ} (hr : 0 ≤ r) (u : ℝ) :
    ‖(r : ℂ) * left u‖ = r := by rw [norm_mul, norm_real, Real.norm_eq_abs, norm_left,
      abs_of_nonneg hr, mul_one]

private theorem radial_right_re (r u : ℝ) :
    ((r : ℂ) * right u).re = r * (1 / Real.cosh u) := by
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, right_re]

private theorem radial_left_re (r u : ℝ) :
    ((r : ℂ) * left u).re = -(r * (1 / Real.cosh u)) := by
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, left_re, mul_neg]

/-- The complete clipped left arc has a uniform absolute integrable envelope. -/
theorem norm_leftProjection_le {c : ℂ} {η M r : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hlo : (1 / 2 : ℝ) ≤ c.re - η) (hhi : c.re + η ≤ 3 / 2)
    (hM : 0 ≤ M) (hr : 0 ≤ r) (hr1 : r < 1) (u : ℝ) :
    ‖leftProjection c η M r u‖ ≤ envelope c η M * (1 / Real.cosh u) := by
  let w := (r : ℂ) * left u
  have hw : ‖w‖ < 1 := by simpa only [w, norm_radial_left hr] using hr1
  have hre : w.re ≤ 0 := by
    dsimp [w]
    rw [radial_left_re]
    exact neg_nonpos.mpr (mul_nonneg hr (one_div_nonneg.mpr (Real.cosh_pos u).le))
  have hC : 0 ≤ 52 + 2 * |c.im| + 8 * η / Real.pi := by positivity
  have hD : 0 ≤ (1 + 1 / (c.re - 1)) * (1 + 2 / (c.re - 1)) := by
    have : 0 < c.re - 1 := by linarith
    positivity
  have h := ClippedLogNorm.abs_weighted_le hM (abs_nonneg w.re)
    ((Complex.abs_re_le_norm w).trans hw.le) hC (left_projection_le hη hlo hhi hw)
  rw [abs_of_nonpos hre] at h
  have hh := mul_le_mul_of_nonneg_left h (one_div_nonneg.mpr (Real.cosh_pos u).le)
  rw [leftProjection, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr (Real.cosh_pos u))]
  change (1 / Real.cosh u) * |(-w.re) * ClippedLogNorm.value M (carrier c η w)| ≤ _
  exact hh.trans (by dsimp [envelope]; nlinarith [one_div_nonneg.mpr (Real.cosh_pos u).le])

/-- The full signed right arc also has absolute domination; no right clipping is used. -/
theorem norm_rightProjection_le {c : ℂ} {η M r : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hlo : (1 / 2 : ℝ) ≤ c.re - η) (hhi : c.re + η ≤ 3 / 2)
    (hM : 0 ≤ M) (hr : 0 ≤ r) (hr1 : r < 1) (u : ℝ) :
    ‖rightProjection c η r u‖ ≤ envelope c η M * (1 / Real.cosh u) := by
  let w := (r : ℂ) * right u
  have hw : ‖w‖ < 1 := by simpa only [w, norm_radial_right hr] using hr1
  have hre : 0 ≤ w.re := by dsimp [w]; rw [radial_right_re]; positivity
  have hl := left_projection_le hη hlo hhi hw
  have hu := right_projection_le hc hη hw hre
  rw [abs_of_nonneg hre] at hl
  have hC : 0 ≤ 52 + 2 * |c.im| + 8 * η / Real.pi := by positivity
  have hD : 0 ≤ (1 + 1 / (c.re - 1)) * (1 + 2 / (c.re - 1)) := by
    have : 0 < c.re - 1 := by linarith
    positivity
  have h : |(-w.re) * Real.log ‖carrier c η w‖| ≤ envelope c η M := by
    rw [abs_le]
    dsimp [envelope]
    constructor <;> nlinarith
  rw [rightProjection, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr (Real.cosh_pos u)), mul_comm (envelope c η M)]
  exact mul_le_mul_of_nonneg_left h (one_div_nonneg.mpr (Real.cosh_pos u).le)

private theorem continuous_right : Continuous right := by
  unfold right
  simp only [Real.tanh_eq_sinh_div_cosh]
  fun_prop (disch := intro u; exact (Real.cosh_pos u).ne')

private theorem continuous_left : Continuous left := by
  unfold left
  simp only [Real.tanh_eq_sinh_div_cosh]
  fun_prop (disch := intro u; exact (Real.cosh_pos u).ne')

private theorem continuous_carrier_radial_right {c : ℂ} {η r : ℝ}
    (hη : 0 < η) (hleft : η < c.re) (hr : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun u => carrier c η ((r : ℂ) * right u)) := by
  apply (analyticOnNhd_carrier hη hleft hr1).continuousOn.comp_continuous
    (continuous_const.mul continuous_right)
  intro u
  simp only [mem_closedBall, dist_zero_right, Pi.mul_apply, norm_radial_right hr, le_refl]

private theorem continuous_carrier_radial_left {c : ℂ} {η r : ℝ}
    (hη : 0 < η) (hleft : η < c.re) (hr : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun u => carrier c η ((r : ℂ) * left u)) := by
  apply (analyticOnNhd_carrier hη hleft hr1).continuousOn.comp_continuous
    (continuous_const.mul continuous_left)
  intro u
  simp only [mem_closedBall, dist_zero_right, Pi.mul_apply, norm_radial_left hr, le_refl]

private theorem carrier_radial_right_ne_zero {c : ℂ} {η r : ℝ}
    (hc : 1 < c.re) (hη : 0 < η) (hr : 0 ≤ r) (hr1 : r < 1) (u : ℝ) :
    carrier c η ((r : ℂ) * right u) ≠ 0 := by
  have hw : ‖(r : ℂ) * right u‖ < 1 := by rw [norm_radial_right hr]; exact hr1
  apply regularized_ne_zero
  have hs : c.re ≤ (AnalyticStripMap.map c η ((r : ℂ) * right u)).re := by
    by_contra! h
    have hh := (AnalyticStripMap.map_re_lt_center_iff c hη hw).mp h
    rw [radial_right_re] at hh
    exact (not_lt_of_ge (by positivity)) hh
  linarith

/-- The radial clipped left integrand is continuous, including where the carrier vanishes. -/
theorem continuous_leftProjection {c : ℂ} {η r : ℝ} (hη : 0 < η)
    (hleft : η < c.re) (hr : 0 ≤ r) (hr1 : r < 1) (M : ℝ) :
    Continuous (leftProjection c η M r) := by
  have hf := (ClippedLogNorm.continuous M).comp (continuous_carrier_radial_left hη hleft hr hr1)
  unfold leftProjection
  exact (continuous_const.div Real.continuous_cosh (fun u => (Real.cosh_pos u).ne')).mul
    ((Complex.continuous_re.comp (continuous_const.mul continuous_left)).neg.mul hf)

/-- The right radial signed logarithm is continuous on its actual nonzero Euler side. -/
theorem continuous_rightProjection {c : ℂ} {η r : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hleft : η < c.re) (hr : 0 ≤ r) (hr1 : r < 1) : Continuous (rightProjection c η r) := by
  have hf := (continuous_carrier_radial_right hη hleft hr hr1).norm.log
    (fun u => norm_ne_zero_iff.mpr (carrier_radial_right_ne_zero hc hη hr hr1 u))
  unfold rightProjection
  exact (continuous_const.div Real.continuous_cosh (fun u => (Real.cosh_pos u).ne')).mul
    ((Complex.continuous_re.comp (continuous_const.mul continuous_right)).neg.mul hf)

/-- Every finite clipped left integral is a genuine integrable function. -/
theorem integrable_leftProjection {c : ℂ} {η M r : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hlo : (1 / 2 : ℝ) ≤ c.re - η) (hhi : c.re + η ≤ 3 / 2)
    (hM : 0 ≤ M) (hr : 0 ≤ r) (hr1 : r < 1) : Integrable (leftProjection c η M r) := by
  apply (integrable_sech.const_mul (envelope c η M)).mono'
    (continuous_leftProjection hη (by linarith) hr hr1 M).aestronglyMeasurable
  exact ae_of_all _ (norm_leftProjection_le hc hη hlo hhi hM hr hr1)

/-- Every finite right integral is genuinely integrable with its full sign. -/
theorem integrable_rightProjection {c : ℂ} {η r : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hlo : (1 / 2 : ℝ) ≤ c.re - η) (hhi : c.re + η ≤ 3 / 2)
    (hr : 0 ≤ r) (hr1 : r < 1) : Integrable (rightProjection c η r) := by
  apply (integrable_sech.const_mul (envelope c η 0)).mono'
    (continuous_rightProjection hc hη (by linarith) hr hr1).aestronglyMeasurable
  exact ae_of_all _ (norm_rightProjection_le hc hη hlo hhi (le_refl 0) hr hr1)

private theorem continuousAt_carrier_right {c : ℂ} {η : ℝ}
    (hpos : 0 < c.re + η) (u : ℝ) : ContinuousAt (carrier c η) (right u) := by
  have hs : 0 < (AnalyticStripMap.map c η (right u)).re := by
    rw [map_right]
    simpa only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero] using hpos
  exact (analyticAt_regularized hs).continuousAt.comp
    (continuousAt_map_boundary c η (by rw [right_re]; exact one_div_ne_zero (Real.cosh_pos u).ne'))

private theorem continuousAt_carrier_left {c : ℂ} {η : ℝ}
    (hpos : 0 < c.re - η) (u : ℝ) : ContinuousAt (carrier c η) (left u) := by
  have hs : 0 < (AnalyticStripMap.map c η (left u)).re := by
    rw [map_left]
    simpa only [add_re, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero] using hpos
  exact (analyticAt_regularized hs).continuousAt.comp
    (continuousAt_map_boundary c η (by
      rw [left_re]
      exact neg_ne_zero.mpr (one_div_ne_zero (Real.cosh_pos u).ne')))

/-- At every finite height the clipped left radial projection has its ordinary boundary limit. -/
theorem leftProjection_tendsto {c : ℂ} {η M : ℝ} (hleft : 0 < c.re - η)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 1)) (u : ℝ) :
    Tendsto (fun n => leftProjection c η M (r n) u) atTop (𝓝 (leftProjection c η M 1 u)) := by
  have hw : Tendsto (fun n => (r n : ℂ) * left u) atTop (𝓝 (left u)) := by
    simpa only [ofReal_one, one_mul] using! (Complex.continuous_ofReal.tendsto 1 |>.comp hr).mul_const (left u)
  have hf := ((ClippedLogNorm.continuous M).continuousAt.comp
    (continuousAt_carrier_left hleft u)).tendsto.comp hw
  have hx := ((Complex.continuous_re.tendsto _).comp hw).neg
  simpa only [leftProjection, ofReal_one, one_mul] using! (hx.mul hf).const_mul (1 / Real.cosh u)

/-- At every finite height the right projection converges without changing its logarithm. -/
theorem rightProjection_tendsto {c : ℂ} {η : ℝ} (hright : 1 < c.re + η)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 1)) (u : ℝ) :
    Tendsto (fun n => rightProjection c η (r n) u) atTop (𝓝 (rightProjection c η 1 u)) := by
  have hw : Tendsto (fun n => (r n : ℂ) * right u) atTop (𝓝 (right u)) := by
    simpa only [ofReal_one, one_mul] using! (Complex.continuous_ofReal.tendsto 1 |>.comp hr).mul_const (right u)
  have hn : carrier c η (right u) ≠ 0 := by
    apply regularized_ne_zero
    rw [map_right]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    linarith
  have hf := ((continuousAt_carrier_right (by linarith) u).norm.log
    (norm_ne_zero_iff.mpr hn)).tendsto.comp hw
  have hx := ((Complex.continuous_re.tendsto _).comp hw).neg
  simpa only [rightProjection, ofReal_one, one_mul] using! (hx.mul hf).const_mul (1 / Real.cosh u)

/-- The full left radial integral converges at every retained negative depth,
without assuming integrability of the untruncated negative part. -/
theorem integral_leftProjection_tendsto {c : ℂ} {η M : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hlo : (1 / 2 : ℝ) ≤ c.re - η) (hhi : c.re + η ≤ 3 / 2) (hM : 0 ≤ M)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 1)) (hr0 : ∀ n, 0 ≤ r n) (hr1 : ∀ n, r n < 1) :
    Tendsto (fun n => ∫ u : ℝ, leftProjection c η M (r n) u) atTop
      (𝓝 (∫ u : ℝ, leftProjection c η M 1 u)) := by
  apply tendsto_integral_of_dominated_convergence (fun u => envelope c η M * (1 / Real.cosh u))
  · intro n
    exact (continuous_leftProjection hη (by linarith) (hr0 n) (hr1 n) M).aestronglyMeasurable
  · exact integrable_sech.const_mul _
  · intro n
    exact ae_of_all _ (norm_leftProjection_le hc hη hlo hhi hM (hr0 n) (hr1 n))
  · exact ae_of_all _ (leftProjection_tendsto (by linarith) hr)

/-- The complete right signed integral has its ordinary boundary limit,
ready for the full phase-family Euler cancellation. -/
theorem integral_rightProjection_tendsto {c : ℂ} {η : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hlo : (1 / 2 : ℝ) ≤ c.re - η) (hhi : c.re + η ≤ 3 / 2)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 1)) (hr0 : ∀ n, 0 ≤ r n) (hr1 : ∀ n, r n < 1) :
    Tendsto (fun n => ∫ u : ℝ, rightProjection c η (r n) u) atTop
      (𝓝 (∫ u : ℝ, rightProjection c η 1 u)) := by
  apply tendsto_integral_of_dominated_convergence (fun u => envelope c η 0 * (1 / Real.cosh u))
  · intro n
    exact (continuous_rightProjection hc hη (by linarith) (hr0 n) (hr1 n)).aestronglyMeasurable
  · exact integrable_sech.const_mul _
  · intro n
    exact ae_of_all _ (norm_rightProjection_le hc hη hlo hhi (le_refl 0) (hr0 n) (hr1 n))
  · exact ae_of_all _ (rightProjection_tendsto (by linarith) hr)

/-- The full clipped left boundary integral is genuinely integrable.
Its negative part is controlled by the chosen finite depth. -/
theorem integrable_leftBoundary {c : ℂ} {η M : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hlo : (1 / 2 : ℝ) ≤ c.re - η) (hhi : c.re + η ≤ 3 / 2) (hM : 0 ≤ M) :
    Integrable (leftProjection c η M 1) := by
  obtain ⟨r, hr, hs⟩ := exists_sphere_tendsto hc hη (by linarith)
  have hm : ∀ n, AEStronglyMeasurable (leftProjection c η M (r n)) volume := fun n =>
    (continuous_leftProjection hη (by linarith) (hs n).1.le (hs n).2.1 M).aestronglyMeasurable
  have ht := leftProjection_tendsto (M := M) (by linarith : 0 < c.re - η) hr
  apply (integrable_sech.const_mul (envelope c η M)).mono'
    (aestronglyMeasurable_of_tendsto_ae atTop hm (ae_of_all _ ht))
  apply ae_of_all
  intro u
  exact le_of_tendsto (ht u).norm (Eventually.of_forall fun n =>
    norm_leftProjection_le hc hη hlo hhi hM (hs n).1.le (hs n).2.1 u)

/-- The complete signed right boundary has a genuine absolute integral.
No negative clipping or absolute-value replacement appears in its value. -/
theorem integrable_rightBoundary {c : ℂ} {η : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hlo : (1 / 2 : ℝ) ≤ c.re - η) (hhi : c.re + η ≤ 3 / 2) :
    Integrable (rightProjection c η 1) := by
  obtain ⟨r, hr, hs⟩ := exists_sphere_tendsto hc hη (by linarith)
  have hm : ∀ n, AEStronglyMeasurable (rightProjection c η (r n)) volume := fun n =>
    (continuous_rightProjection hc hη (by linarith) (hs n).1.le (hs n).2.1).aestronglyMeasurable
  have ht := rightProjection_tendsto (by linarith : 1 < c.re + η) hr
  apply (integrable_sech.const_mul (envelope c η 0)).mono'
    (aestronglyMeasurable_of_tendsto_ae atTop hm (ae_of_all _ ht))
  apply ae_of_all
  intro u
  exact le_of_tendsto (ht u).norm (Eventually.of_forall fun n =>
    norm_rightProjection_le hc hη hlo hhi (le_refl 0) (hs n).1.le (hs n).2.1 u)

/-- The positive left projection has its exact physical line value and squared secant weight. -/
theorem leftProjection_one (c : ℂ) (η M u : ℝ) :
    leftProjection c η M 1 u = (1 / Real.cosh u) ^ 2 *
      ClippedLogNorm.value M (regularized (c - η + ((2 * η / Real.pi * u : ℝ) : ℂ) * I)) := by
  unfold leftProjection ZetaStripDisc.carrier AnalyticStripDisc.pullback
  simp only [ofReal_one, one_mul, left_re, neg_neg, Function.comp_apply, map_left]
  ring

/-- The right projection keeps the opposite sign and the same exact squared secant weight. -/
theorem rightProjection_one (c : ℂ) (η u : ℝ) :
    rightProjection c η 1 u = -((1 / Real.cosh u) ^ 2 *
      Real.log ‖regularized (c + η + ((2 * η / Real.pi * u : ℝ) : ℂ) * I)‖) := by
  unfold rightProjection ZetaStripDisc.carrier AnalyticStripDisc.pullback
  simp only [ofReal_one, one_mul, right_re, Function.comp_apply, map_right]
  ring

end
end RiemannGaussian.ZetaStripBoundaryLimit
