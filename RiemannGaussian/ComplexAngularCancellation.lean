/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ComplexAngularResolvent

/-!
# Stability of the signed angular cancellation

Freezing the smooth coefficients of the second angular harmonic leaves
only a simple-pole majorant, uniformly in smoothing. This preserves the
exact disk cancellation of the frozen leading term.
-/

open Complex Filter MeasureTheory Set Topology
open scoped ContDiff
namespace RiemannGaussian
noncomputable section

/-- Changing the quadratic coefficient has a radius-uniform estimate. -/
theorem norm_complexAngularResolventKernel_sub_le {d a b : ℝ} (hd : 0 < d)
    (ha : d ≤ a) (hb : d ≤ b) {z : ℂ} (hz : z ≠ 0) (r : ℝ) :
    ‖complexAngularResolventKernel r a z - complexAngularResolventKernel r b z‖ ≤
      (2/(d^2*normSq z))*|a-b| := by
  have hphase : ‖starRingEnd ℂ z / z‖ ≤ 1 := by
    rw [norm_div, norm_conj]
    exact div_self_le_one ‖z‖
  unfold complexAngularResolventKernel
  rw [← sub_mul, ← ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_of_le_one_right (abs_nonneg _) hphase).trans
    (radialAngularAmplitude_sub_le hd (normSq_pos.mpr hz) ha hb r)

/-- After freezing both coefficients, Lipschitz variation supplies the
one extra radial factor needed for a planar integrable bound. -/
theorem norm_complexAngularResolventKernel_coefficient_error_le
    {d a b L M : ℝ} (hd : 0 < d) (ha : d ≤ a) (hb : d ≤ b)
    {u v z : ℂ} (hz : z ≠ 0) (hu : ‖u-v‖ ≤ L*‖z‖) (hab : |a-b| ≤ M*‖z‖) (r : ℝ) :
    ‖u*complexAngularResolventKernel r a z - v*complexAngularResolventKernel r b z‖ ≤
      (L/d + 2*‖v‖*M/d^2)/‖z‖ := by
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have ht : 0 < normSq z := normSq_pos.mpr hz
  have hrad : ‖complexAngularResolventKernel r a z‖ ≤ 1/(normSq z*d) := by
    apply (norm_complexAngularResolventKernel_le_radial r a z).trans
    apply (radialAngularAmplitude_le (lt_of_lt_of_le hd ha) ht r).trans
    exact one_div_le_one_div_of_le (by positivity) (by gcongr)
  have hdiff := norm_complexAngularResolventKernel_sub_le hd ha hb hz r
  have hL : 0 ≤ L := by nlinarith [norm_nonneg (u-v)]
  have hM : 0 ≤ M := by nlinarith [abs_nonneg (a-b)]
  calc
    _ = ‖(u-v)*complexAngularResolventKernel r a z +
        v*(complexAngularResolventKernel r a z-complexAngularResolventKernel r b z)‖ := by
      congr 1
      ring
    _ ≤ ‖u-v‖*‖complexAngularResolventKernel r a z‖ +
        ‖v‖*‖complexAngularResolventKernel r a z-complexAngularResolventKernel r b z‖ := by
      simpa only [norm_mul] using norm_add_le ((u-v)*complexAngularResolventKernel r a z)
        (v*(complexAngularResolventKernel r a z-complexAngularResolventKernel r b z))
    _ ≤ (L*‖z‖)*(1/(normSq z*d)) + ‖v‖*((2/(d^2*normSq z))*(M*‖z‖)) := by
      gcongr
      exact hdiff.trans (mul_le_mul_of_nonneg_left hab (by positivity))
    _ = _ := by
      rw [normSq_eq_norm_sq]
      field_simp

/-- Smooth coefficients with positive central quadratic coefficient have
a single simple-pole bound, on a fixed neighborhood, for every smoothing
parameter. The frozen leading harmonic remains separate. -/
theorem exists_complexAngularResolventKernel_local_error_bound
    {N : ℂ → ℂ} {Q : ℂ → ℝ} {a : ℂ}
    (hN : ContDiffAt ℝ 1 N a) (hQ : ContDiffAt ℝ 1 Q a) (hQa : 0 < Q a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ z in 𝓝[≠] a, ∀ r : ℝ,
      ‖N z*complexAngularResolventKernel r (Q z) (z-a) -
          N a*complexAngularResolventKernel r (Q a) (z-a)‖ ≤ C/‖z-a‖ := by
  obtain ⟨L, s, hs, hLs⟩ := hN.exists_lipschitzOnWith
  obtain ⟨M, t, ht, hMt⟩ := hQ.exists_lipschitzOnWith
  let d := Q a / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hda : d ≤ Q a := by dsimp [d]; linarith
  have hQd : ∀ᶠ z in 𝓝 a, d ≤ Q z :=
    (hQ.continuousAt.eventually (eventually_ge_nhds (by dsimp [d]; linarith)))
  refine ⟨(L:ℝ)/d + 2*‖N a‖*(M:ℝ)/d^2, by positivity, ?_⟩
  filter_upwards [(show ∀ᶠ z in 𝓝 a, z ∈ s from hs).filter_mono nhdsWithin_le_nhds,
    (show ∀ᶠ z in 𝓝 a, z ∈ t from ht).filter_mono nhdsWithin_le_nhds,
    hQd.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hzs hzt hdz hza r
  apply norm_complexAngularResolventKernel_coefficient_error_le hd hdz hda (sub_ne_zero.mpr hza)
  · simpa only [dist_eq_norm] using hLs.dist_le_mul z hzs a (mem_of_mem_nhds hs)
  · simpa only [dist_eq_norm, Real.norm_eq_abs] using hMt.dist_le_mul z hzt a (mem_of_mem_nhds ht)

/-- Translation preserves both genuine integrability and exact angular
cancellation on a disk centered at an arbitrary complex point. -/
theorem complexAngularResolventKernel_translated_disk_cancellation
    (r : ℝ) {q : ℝ} (hq : 0 ≤ q) (a : ℂ) (R : ℝ) :
    IntegrableOn (fun z => complexAngularResolventKernel r q (z-a)) (Metric.closedBall a R) volume ∧
      (∫ z in Metric.closedBall a R, complexAngularResolventKernel r q (z-a)) = 0 := by
  let e : ℂ → ℂ := fun z => -a+z
  have he : e = fun z : ℂ => z-a := by funext z; simp [e, sub_eq_add_neg, add_comm]
  have hpre : e ⁻¹' Metric.closedBall (0 : ℂ) R = Metric.closedBall a R := by
    ext z
    simp only [he, mem_preimage, Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have hm := measurePreserving_add_left volume (-a)
  have hi := (hm.integrableOn_comp_preimage
    (MeasurableEquiv.addLeft (-a)).measurableEmbedding).2
      (integrableOn_complexAngularResolventKernel r hq R)
  have heq := hm.setIntegral_preimage_emb
    (MeasurableEquiv.addLeft (-a)).measurableEmbedding
      (complexAngularResolventKernel r q) (Metric.closedBall 0 R)
  change IntegrableOn (fun z => complexAngularResolventKernel r q (e z))
    (e ⁻¹' Metric.closedBall 0 R) volume at hi
  change (∫ z in e ⁻¹' Metric.closedBall 0 R, complexAngularResolventKernel r q (e z)) = _ at heq
  rw [hpre, he] at hi heq
  exact ⟨hi, heq.trans (complexAngularResolventKernel_disk_cancellation r hq R).2⟩

/-- A signed family with a fixed angular leading term converges to zero
in integral when its difference has a uniform simple-pole majorant and
its actual pointwise limit is zero. All integrability assumptions and the
exceptional central point are explicit. -/
theorem tendsto_integral_disk_of_angular_error
    {F : ℝ → ℂ → ℂ} {a : ℂ} {R q C : ℝ} {v : ℂ} (hq : 0 < q)
    (hF : ∀ r : ℝ, 0 < r → IntegrableOn (F r) (Metric.closedBall a R) volume)
    (hbound : ∀ z ∈ Metric.closedBall a R, z ≠ a → ∀ r : ℝ, 0 < r →
      ‖F r z - v*complexAngularResolventKernel r q (z-a)‖ ≤ C/‖z-a‖)
    (hlim : ∀ z ∈ Metric.closedBall a R, z ≠ a → Tendsto (fun r => F r z) atTop (𝓝 0)) :
    Tendsto (fun r => ∫ z in Metric.closedBall a R, F r z) atTop (𝓝 0) := by
  let G := fun r z => F r z - v*complexAngularResolventKernel r q (z-a)
  have hG : ∀ r : ℝ, 0 < r → IntegrableOn (G r) (Metric.closedBall a R) volume := by
    intro r hr
    exact (hF r hr).sub
      ((complexAngularResolventKernel_translated_disk_cancellation r hq.le a R).1.const_mul v)
  have hC : IntegrableOn (fun z : ℂ => C/‖z-a‖) (Metric.closedBall a R) volume := by
    have hi := ((locallyIntegrable_complex_inv_sub a).integrableOn_isCompact
      (isCompact_closedBall a R)).norm.const_mul C
    simpa only [IntegrableOn, norm_inv, div_eq_mul_inv] using! hi
  have hD := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Metric.closedBall a R)) (F := G) (f := fun _ => (0 : ℂ))
    (fun z => C/‖z-a‖)
    (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr; exact (hG r hr).aestronglyMeasurable)
    (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      filter_upwards [ae_restrict_mem measurableSet_closedBall,
        ae_restrict_of_ae (volume.ae_ne a)] with z hz hza
      exact hbound z hz hza r hr)
    hC
    (by
      filter_upwards [ae_restrict_mem measurableSet_closedBall,
        ae_restrict_of_ae (volume.ae_ne a)] with z hz hza
      have hk := (tendsto_complexAngularResolventKernel_atTop hq (sub_ne_zero.mpr hza)).const_mul v
      simpa only [mul_zero, sub_zero] using (hlim z hz hza).sub hk)
  simp only [integral_zero] at hD
  apply hD.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  dsimp only [G]
  rw [integral_sub (hF r hr)
    ((complexAngularResolventKernel_translated_disk_cancellation r hq.le a R).1.const_mul v),
    integral_const_mul, (complexAngularResolventKernel_translated_disk_cancellation r hq.le a R).2,
    mul_zero, sub_zero]

end
end RiemannGaussian
