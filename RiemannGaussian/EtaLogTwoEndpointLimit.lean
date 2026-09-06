import RiemannGaussian.EtaLogTwoEndpoint

/-!
# The complex two-endpoint finite-part law

The evaluated finite part of the actual eta mismatch converges at both
logarithmic endpoints. A general scale-offset interface retains the
`-log(v)` term required when the displacement is a fixed multiple of a
Gaussian heat width.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The displacement times its critical logarithmic scale tends to zero. -/
theorem etaDisplacement_mul_log_tendsto_zero :
    Tendsto (fun r : ℝ ↦ r * Real.log (1 / r)) (𝓝[>] 0) (𝓝 0) := by
  simpa only [Real.rpow_one, one_div, Real.log_inv, neg_zero, mul_neg, neg_mul, mul_comm] using
    (tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one).neg

/-- The full complex finite part at both fixed logarithmic endpoints.
The offset between the arithmetic and test scales remains visible in the
upper endpoint coefficient. -/
theorem pairedEtaWeightedMismatch_two_endpoint_tendsto {ι : Type*} {l : Filter ι}
    {r R : ι → ℝ} (hr : Tendsto r l (𝓝[>] (0 : ℝ))) (hR : Tendsto R l atTop)
    {d : ℝ} (hscale : Tendsto (fun i ↦ Real.log (1 / r i) - R i) l (𝓝 d))
    {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    Tendsto (fun i ↦ (r i)⁻¹ • pairedEtaWeightedMismatch (r i) (R i) F -
      R i • (∫ z in 0..1, F z)) l
      (𝓝 ((Real.eulerMascheroniConstant - 1) • F 0 +
        (1 - Real.log (Real.pi / 2) + d) • F 1)) := by
  have hr0 : Tendsto r l (𝓝 (0 : ℝ)) := hr.mono_right nhdsWithin_le_nhds
  have hRinv : Tendsto (fun i ↦ (R i)⁻¹) l (𝓝 0) := tendsto_inv_atTop_zero.comp hR
  have hrH := etaDisplacement_mul_log_tendsto_zero.comp hr
  have hrR : Tendsto (fun i ↦ r i * R i) l (𝓝 0) := by
    convert hrH.sub (hr0.mul hscale) using 1 <;>
      first | (funext i; dsimp only [Function.comp_apply]; ring) | simp
  have hdom : Tendsto (fun i ↦ r i * B * (140 + R i + |Real.log (1 / r i) - R i|) +
      ((K : ℝ) / R i) * (76 + 12 * (Real.log (1 / r i) - R i) ^ 2)) l (𝓝 0) := by
    have hfirst := (((hr0.const_mul 140).add hrR).add (hr0.mul hscale.abs)).const_mul B
    have hsecond := (hRinv.const_mul (K : ℝ)).mul ((hscale.pow 2).const_mul 12 |>.const_add 76)
    convert hfirst.add hsecond using 1 <;>
      first | (funext i; simp only [div_eq_mul_inv]; ring) | simp
  have herror : Tendsto (fun i ↦
      (r i)⁻¹ • pairedEtaWeightedMismatch (r i) (R i) F - R i • (∫ z in 0..1, F z) -
        ((harmonic (pairedEtaShiftBoundaryCutoff (r i)) : ℝ) - 1 -
          Real.log ((pairedEtaShiftBoundaryCutoff (r i) : ℝ) + 1)) • F 0 -
        (1 - Real.log (Real.pi / 2) + (Real.log (1 / r i) - R i)) • F 1) l (𝓝 0) := by
    apply squeeze_zero_norm' _ hdom
    have hrsmall : ∀ᶠ i in l, r i < 1 / 8 := hr.eventually
      (nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)))
    filter_upwards [hr.eventually self_mem_nhdsWithin, hrsmall,
      hR.eventually (eventually_gt_atTop 0)] with i hri hsmall hRi
    exact pairedEtaWeightedMismatch_endpoint_error_le hri hsmall.le hRi hF hB
  have hA : Tendsto (fun i ↦ (harmonic (pairedEtaShiftBoundaryCutoff (r i)) : ℝ) - 1 -
      Real.log ((pairedEtaShiftBoundaryCutoff (r i) : ℝ) + 1)) l
      (𝓝 (Real.eulerMascheroniConstant - 1)) := by
    have h := Real.tendsto_harmonic_sub_log_add_one.comp (pairedEtaShiftBoundaryCutoff_tendsto_atTop.comp hr)
    convert h.sub_const 1 using 1
    funext i
    dsimp only [Function.comp_apply]
    ring
  have hQ := hscale.const_add (1 - Real.log (Real.pi / 2))
  have hmain := (hA.smul_const (F 0)).add (hQ.smul_const (F 1))
  convert herror.add hmain using 1 <;> first | (funext i; abel) | simp

/-- The critical boundary law has separate lower and upper endpoint
constants for every bounded Lipschitz complex test. -/
theorem pairedEtaWeightedMismatch_critical_finite_part_tendsto {F : ℝ → ℂ} {K : ℝ≥0}
    (hF : LipschitzWith K F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    Tendsto (fun r : ℝ ↦ r⁻¹ • pairedEtaWeightedMismatch r (Real.log (1 / r)) F -
      Real.log (1 / r) • (∫ z in 0..1, F z)) (𝓝[>] 0)
      (𝓝 ((Real.eulerMascheroniConstant - 1) • F 0 + (1 - Real.log (Real.pi / 2)) • F 1)) := by
  have hlog : Tendsto (fun r : ℝ ↦ Real.log (1 / r)) (𝓝[>] (0 : ℝ)) atTop := by
    have hi : Tendsto (fun r : ℝ ↦ 1 / r) (𝓝[>] 0) atTop := by
      simpa only [one_div] using
        (tendsto_inv_nhdsGT_zero : Tendsto (fun r : ℝ ↦ r⁻¹) (𝓝[>] 0) atTop)
    exact Real.tendsto_log_atTop.comp hi
  have hscale : Tendsto (fun r : ℝ ↦ Real.log (1 / r) - Real.log (1 / r)) (𝓝[>] 0) (𝓝 0) := by simp
  simpa only [add_zero, id_eq] using pairedEtaWeightedMismatch_two_endpoint_tendsto tendsto_id hlog hscale hF hB

/-- At a fixed positive Gaussian coordinate, the actual complex weighted
finite part retains the additional upper-endpoint coefficient `-log(v)`. -/
theorem pairedEtaWeightedMismatch_exp_scaled_finite_part_tendsto {v : ℝ} (hv : 0 < v)
    {F : ℝ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    Tendsto (fun R : ℝ ↦ (Real.exp (-R))⁻¹ • pairedEtaWeightedMismatch (Real.exp (-R) * v) R F -
      (v * R) • (∫ z in 0..1, F z)) atTop
      (𝓝 (v • ((Real.eulerMascheroniConstant - 1) • F 0 +
        (1 - Real.log (Real.pi / 2) - Real.log v) • F 1))) := by
  have hr0 : Tendsto (fun R : ℝ ↦ Real.exp (-R) * v) atTop (𝓝 0) := by
    simpa only [zero_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.mul_const v
  have hr : Tendsto (fun R : ℝ ↦ Real.exp (-R) * v) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hr0, Eventually.of_forall fun R ↦ mul_pos (Real.exp_pos _) hv⟩
  have hscale : Tendsto (fun R : ℝ ↦ Real.log (1 / (Real.exp (-R) * v)) - R) atTop (𝓝 (-Real.log v)) := by
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall fun R ↦ by
      dsimp only
      rw [Real.log_div one_ne_zero (by positivity), Real.log_one,
        Real.log_mul (Real.exp_ne_zero _) hv.ne', Real.log_exp]
      ring
  have h := (pairedEtaWeightedMismatch_two_endpoint_tendsto hr tendsto_id hscale hF hB).const_smul v
  simp only [← sub_eq_add_neg, id_eq] at h
  apply h.congr'
  exact Eventually.of_forall fun R ↦ by
    simp only [smul_sub, smul_smul]
    rw [show v * (Real.exp (-R) * v)⁻¹ = (Real.exp (-R))⁻¹ by field_simp]

/-- The proposed exponentially parametrized two-endpoint law is a direct
specialization of the actual real-displacement theorem. -/
theorem pairedEtaWeightedMismatch_exp_finite_part_tendsto {F : ℝ → ℂ} {K : ℝ≥0}
    (hF : LipschitzWith K F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) :
    Tendsto (fun R : ℝ ↦ (Real.exp (-R))⁻¹ • pairedEtaWeightedMismatch (Real.exp (-R)) R F -
      R • (∫ z in 0..1, F z)) atTop
      (𝓝 ((Real.eulerMascheroniConstant - 1) • F 0 + (1 - Real.log (Real.pi / 2)) • F 1)) := by
  simpa only [mul_one, one_mul, one_smul, Real.log_one, sub_zero] using
    pairedEtaWeightedMismatch_exp_scaled_finite_part_tendsto zero_lt_one hF hB

end

end RiemannGaussian
