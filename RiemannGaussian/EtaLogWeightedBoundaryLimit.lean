import RiemannGaussian.EtaLogWeightedBoundary
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The critical eta boundary distribution on logarithmic time

The quantitative complex-test estimate implies a uniform limiting boundary
distribution on the interval from zero to one. A general scale interface
allows the displacement to be a fixed multiple of an exponentially small
heat width, without changing the test function's logarithmic scale.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The complete actual boundary measure converges against every bounded
Lipschitz complex test when its time scale is asymptotic to `log (1/r)`.
Both the phase-sensitive test and the exact scaling are retained. -/
theorem pairedEtaWeightedMismatch_scaled_tendsto {ι : Type*} {l : Filter ι}
    {r R : ι → ℝ} (hr : Tendsto r l (𝓝[>] (0 : ℝ))) (hR : Tendsto R l atTop)
    (hscale : Tendsto (fun i ↦ Real.log (1 / r i) / R i) l (𝓝 1))
    {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F)
    {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    Tendsto (fun i ↦ (r i * R i)⁻¹ • pairedEtaWeightedMismatch (r i) (R i) F)
      l (𝓝 (∫ z in 0..1, F z)) := by
  have hRinv : Tendsto (fun i ↦ (R i)⁻¹) l (𝓝 0) := tendsto_inv_atTop_zero.comp hR
  have hdom : Tendsto (fun i ↦
      (12 * B + 4 * (K : ℝ) * (Real.log (1 / r i) / R i)) / R i) l (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      ((hscale.const_mul (4 * (K : ℝ))).const_add (12 * B)).mul hRinv
  have herror : Tendsto (fun i ↦
      (r i * R i)⁻¹ • pairedEtaWeightedMismatch (r i) (R i) F -
        ∫ z in 0..Real.log (1 / r i) / R i, F z) l (𝓝 0) := by
    apply squeeze_zero_norm' _ hdom
    have hrsmall : ∀ᶠ i in l, r i < 1 / 8 := hr.eventually
      (nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)))
    filter_upwards [hr.eventually self_mem_nhdsWithin, hrsmall,
      hR.eventually (eventually_gt_atTop 0)] with i hri hsmall hRi
    have hrpos : 0 < r i := hri
    have hden : 0 < r i * R i := mul_pos hrpos hRi
    have hnormid : (r i * R i)⁻¹ • pairedEtaWeightedMismatch (r i) (R i) F -
        (∫ z in 0..Real.log (1 / r i) / R i, F z) =
        (r i * R i)⁻¹ • (pairedEtaWeightedMismatch (r i) (R i) F -
          r i • (∫ t in 0..Real.log (1 / r i), F (t / R i))) := by
      rw [intervalIntegral.integral_comp_div F hRi.ne', zero_div,
        smul_sub, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hden.ne', one_smul]
    rw [hnormid, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hden)]
    calc
      _ ≤ (r i * R i)⁻¹ * (r i * (12 * B + 4 * (K : ℝ) / R i * Real.log (1 / r i))) :=
        mul_le_mul_of_nonneg_left
          (pairedEtaWeightedMismatch_critical_error_le hrpos hsmall.le hRi hF hB)
          (inv_nonneg.mpr hden.le)
      _ = _ := by field_simp
  have hprimitive : Tendsto (fun i ↦ ∫ z in 0..Real.log (1 / r i) / R i, F z)
      l (𝓝 (∫ z in 0..1, F z)) :=
    ((intervalIntegral.continuous_primitive (fun a b ↦ hF.continuous.intervalIntegrable a b) 0).tendsto 1).comp hscale
  simpa only [sub_add_cancel, zero_add] using herror.add hprimitive

/-- The basic critical boundary distribution, normalized by its actual
displacement times its logarithmic scale. -/
theorem pairedEtaWeightedMismatch_critical_tendsto {F : ℝ → ℂ} {K : ℝ≥0}
    (hF : LipschitzWith K F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    Tendsto (fun r : ℝ ↦ (r * Real.log (1 / r))⁻¹ •
      pairedEtaWeightedMismatch r (Real.log (1 / r)) F)
      (𝓝[>] 0) (𝓝 (∫ z in 0..1, F z)) := by
  have hlog : Tendsto (fun r : ℝ ↦ Real.log (1 / r)) (𝓝[>] (0 : ℝ)) atTop := by
    have hi : Tendsto (fun r : ℝ ↦ 1 / r) (𝓝[>] (0 : ℝ)) atTop := by
      simpa only [one_div] using
        (tendsto_inv_nhdsGT_zero : Tendsto (fun r : ℝ ↦ r⁻¹) (𝓝[>] 0) atTop)
    exact Real.tendsto_log_atTop.comp hi
  apply pairedEtaWeightedMismatch_scaled_tendsto tendsto_id hlog _ hF hB
  apply tendsto_const_nhds.congr'
  filter_upwards [hlog.eventually (eventually_gt_atTop 0)] with r hr
  exact (div_self hr.ne').symm

/-- Exponentially small displacements times a fixed positive Gaussian
coordinate use the same logarithmic boundary distribution. -/
theorem pairedEtaWeightedMismatch_exp_scaled_tendsto {v : ℝ} (hv : 0 < v)
    {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    Tendsto (fun R : ℝ ↦ (Real.exp (-R) * R)⁻¹ •
      pairedEtaWeightedMismatch (Real.exp (-R) * v) R F)
      atTop (𝓝 (v • (∫ z in 0..1, F z))) := by
  have hr0 : Tendsto (fun R : ℝ ↦ Real.exp (-R) * v) atTop (𝓝 0) := by
    simpa only [zero_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.mul_const v
  have hr : Tendsto (fun R : ℝ ↦ Real.exp (-R) * v) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hr0, Eventually.of_forall fun R ↦ mul_pos (Real.exp_pos _) hv⟩
  have hscale : Tendsto (fun R : ℝ ↦ Real.log (1 / (Real.exp (-R) * v)) / R)
      atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 1)).sub
      ((tendsto_inv_atTop_zero : Tendsto (fun R : ℝ ↦ R⁻¹) atTop (𝓝 0)).const_mul (Real.log v))
    simp only [mul_zero, sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one,
      Real.log_mul (Real.exp_ne_zero _) hv.ne', Real.log_exp]
    field_simp
    ring
  have h := (pairedEtaWeightedMismatch_scaled_tendsto hr tendsto_id hscale hF hB).const_smul v
  simp only [id_eq] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [smul_smul]
  congr 1
  field_simp

end

end RiemannGaussian
