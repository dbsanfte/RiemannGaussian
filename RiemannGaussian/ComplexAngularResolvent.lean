/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiReflectionMassExhaustion
import Mathlib.Analysis.Complex.Isometry

/-!
# The signed angular kernel of a normalized reflection endpoint

This kernel retains the second angular harmonic of the leading local
weight-derivative term. Its phase changes sign under a quarter-turn.
The radial estimates are kept separate from that exact cancellation.
-/

open Complex Filter MeasureTheory Set Topology
namespace RiemannGaussian
noncomputable section

/-- The full second angular harmonic, with its smoothing denominator. -/
def complexAngularResolventKernel (r a : ℝ) (z : ℂ) : ℂ :=
  ((r ^ 2 / (1 + r ^ 2 * normSq z * a) ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ z / z)

/-- A quarter-turn negates the complete kernel at every radius. -/
theorem complexAngularResolventKernel_mul_I (r a : ℝ) (z : ℂ) :
    complexAngularResolventKernel r a (I * z) = -complexAngularResolventKernel r a z := by
  unfold complexAngularResolventKernel
  simp only [map_mul, normSq_I, one_mul, conj_I]
  by_cases hz : z = 0
  · simp [hz]
  · field_simp

/-- The angular phase has norm at most one, including its central value. -/
theorem norm_complexAngularResolventKernel_le_radial (r a : ℝ) (z : ℂ) :
    ‖complexAngularResolventKernel r a z‖ ≤ r ^ 2 / (1 + r ^ 2 * normSq z * a) ^ 2 := by
  have hphase : ‖starRingEnd ℂ z / z‖ ≤ 1 := by
    rw [norm_div, norm_conj]
    exact div_self_le_one ‖z‖
  rw [complexAngularResolventKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact mul_le_of_le_one_right (by positivity) hphase

/-- A radius-independent estimate for the radial amplitude, away from
the center. This bound is used only after a coefficient difference has
provided an additional vanishing factor. -/
theorem radialAngularAmplitude_le {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (r : ℝ) :
    r ^ 2 / (1 + r ^ 2 * t * a) ^ 2 ≤ 1 / (t * a) := by
  have hu : 0 ≤ r ^ 2 * t * a := by positivity
  apply (div_le_div_iff₀ (sq_pos_of_pos (by positivity)) (mul_pos ht ha)).mpr
  nlinarith [sq_nonneg (r ^ 2 * t * a)]

/-- The radial amplitude has a parameter Lipschitz bound uniform in
the smoothing radius, as long as the local quadratic coefficient stays
above one fixed positive lower bound. -/
theorem radialAngularAmplitude_sub_le {d t a b : ℝ}
    (hd : 0 < d) (ht : 0 < t) (ha : d ≤ a) (hb : d ≤ b) (r : ℝ) :
    |r ^ 2 / (1 + r ^ 2 * t * a) ^ 2 - r ^ 2 / (1 + r ^ 2 * t * b) ^ 2| ≤
      (2 / (d ^ 2 * t)) * |a - b| := by
  let f := fun u : ℝ => r ^ 2 / (1 + r ^ 2 * t * u) ^ 2
  let f' := fun u : ℝ => -2 * r ^ 4 * t / (1 + r ^ 2 * t * u) ^ 3
  have hder : ∀ u ∈ Ici d, HasDerivAt f (f' u) u := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hd hu
    have hpos : 0 < 1 + r ^ 2 * t * u := by positivity
    have hx := (((hasDerivAt_id u).const_mul (r^2*t)).const_add 1).pow 2
    convert! (hasDerivAt_const u (r^2)).div hx (pow_ne_zero 2 hpos.ne') using 1
    dsimp only [f', Pi.pow_apply, id_eq]
    field_simp
    ring
  have hbound : ∀ u ∈ Ici d, ‖f' u‖ ≤ 2 / (d^2*t) := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hd hu
    let D := 1 + r^2*t*u
    have hD : 1 ≤ D := by dsimp [D]; nlinarith [mul_nonneg (sq_nonneg r) (mul_pos ht hu0).le]
    have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
    have hsmall : r^2*t*d ≤ D := by
      dsimp [D]
      nlinarith [mul_le_mul_of_nonneg_left hu (show 0 ≤ r^2*t by positivity)]
    have hsquare : (r^2*t*d)^2 ≤ D^2 :=
      pow_le_pow_left₀ (by positivity) hsmall 2
    have hcube : D^2 ≤ D^3 := by nlinarith [mul_nonneg (sq_nonneg D) (sub_nonneg.mpr hD)]
    change ‖-2*r^4*t/D^3‖ ≤ _
    rw [Real.norm_eq_abs, show -2*r^4*t = -(2*r^4*t) by ring, neg_div, abs_neg,
      abs_of_nonneg (by positivity)]
    apply (div_le_div_iff₀ (pow_pos hD0 3) (by positivity)).mpr
    nlinarith [hsquare.trans hcube]
  simpa only [f, Real.norm_eq_abs] using
    (convex_Ici d).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu => (hder u hu).hasDerivWithinAt) hbound hb ha

/-- Each fixed radial kernel is genuinely integrable on a finite disk. -/
theorem integrableOn_complexAngularResolventKernel (r : ℝ) {a : ℝ} (ha : 0 ≤ a) (R : ℝ) :
    IntegrableOn (complexAngularResolventKernel r a) (Metric.closedBall 0 R) volume := by
  have hm : AEStronglyMeasurable (complexAngularResolventKernel r a) volume := by
    have hrad : Measurable (fun z : ℂ => r^2/(1+r^2*normSq z*a)^2) := by fun_prop
    exact ((Complex.continuous_ofReal.measurable.comp hrad).mul
      (Complex.continuous_conj.measurable.div measurable_id)).aestronglyMeasurable
  apply Measure.integrableOn_of_bounded (isCompact_closedBall (0 : ℂ) R).measure_lt_top.ne hm
  filter_upwards with z
  apply (norm_complexAngularResolventKernel_le_radial r a z).trans
  apply div_le_self (sq_nonneg r)
  apply one_le_pow₀
  have hn := normSq_nonneg z
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg r) hn) ha]

/-- The entire complex integral of the leading angular kernel is zero
on every centered disk. A quarter-turn preserves area and negates the
kernel; no absolute value is taken before this cancellation. -/
theorem complexAngularResolventKernel_disk_cancellation (r : ℝ) {a : ℝ} (ha : 0 ≤ a) (R : ℝ) :
    IntegrableOn (complexAngularResolventKernel r a) (Metric.closedBall 0 R) volume ∧
      (∫ z in Metric.closedBall (0 : ℂ) R, complexAngularResolventKernel r a z) = 0 := by
  refine ⟨integrableOn_complexAngularResolventKernel r ha R, ?_⟩
  let u : Circle := ⟨I, mem_sphere_zero_iff_norm.mpr norm_I⟩
  let e := rotation u
  have he : ∀ z : ℂ, e z = I * z := fun _ => rfl
  have hpre : e ⁻¹' Metric.closedBall (0 : ℂ) R = Metric.closedBall 0 R := by
    ext z
    simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right, e.norm_map]
  have h := e.measurePreserving.setIntegral_preimage_emb
    e.toHomeomorph.measurableEmbedding (complexAngularResolventKernel r a) (Metric.closedBall 0 R)
  rw [hpre] at h
  simp_rw [he, complexAngularResolventKernel_mul_I] at h
  rw [integral_neg] at h
  linear_combination -(1/2 : ℂ) * h

/-- At every fixed noncentral point the full complex kernel tends to
zero as smoothing grows. No interchange with an integral is made here. -/
theorem tendsto_complexAngularResolventKernel_atTop {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun r : ℝ => complexAngularResolventKernel r a z) atTop (𝓝 0) := by
  have hn : 0 < normSq z := normSq_pos.mpr hz
  have ht : 0 < normSq z * a := mul_pos (normSq_pos.mpr hz) ha
  have hbound : ∀ r : ℝ, 0 < r →
      ‖complexAngularResolventKernel r a z‖ ≤ 1 / (r ^ 2 * (normSq z * a) ^ 2) := by
    intro r hr
    apply (norm_complexAngularResolventKernel_le_radial r a z).trans
    apply (div_le_div_iff₀ (sq_pos_of_pos (by positivity)) (by positivity)).mpr
    have hu : 0 < r ^ 2 * normSq z * a := by positivity
    nlinarith [sq_nonneg (r ^ 2 * normSq z * a)]
  have hlim : Tendsto (fun r : ℝ => 1 / (r ^ 2 * (normSq z * a) ^ 2)) atTop (𝓝 0) := by
    have hp : Tendsto (fun r : ℝ => r ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
    have h := (tendsto_const_nhds (x := 1 / (normSq z * a) ^ 2)).div_atTop hp
    simpa only [div_div, mul_comm] using h
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact hbound r hr

end
end RiemannGaussian
