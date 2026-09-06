import RiemannGaussian.EtaLogTailWallis
import RiemannGaussian.EtaLogWeightedBoundary
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The evaluated scalar finite part of the critical eta boundary law

The actual critical mismatch has the next constant
`eulerMascheroniConstant - log (pi / 2)`. The proof combines the exact
arithmetic tail with the harmonic limit, then rigorously changes from
`exp(r)-1` back to the original real displacement `r`.
-/

open Filter MeasureTheory Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The actual arithmetic cutoff tends to infinity through all positive
real displacements approaching zero. -/
theorem pairedEtaShiftBoundaryCutoff_tendsto_atTop :
    Tendsto pairedEtaShiftBoundaryCutoff (𝓝[>] (0 : ℝ)) atTop := by
  apply tendsto_nat_floor_atTop.comp
  have hi := (tendsto_inv_nhdsGT_zero : Tendsto (fun r : ℝ ↦ r⁻¹) (𝓝[>] 0) atTop)
    |>.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  convert hi using 1
  funext r
  simp [div_eq_mul_inv, mul_inv_rev, mul_comm]

/-- The arithmetic displacement `exp(r)-1` tends to zero on the original
positive displacement filter. -/
theorem etaExpDisplacement_tendsto_zero :
    Tendsto (fun r : ℝ ↦ Real.exp r - 1) (𝓝[>] 0) (𝓝 0) := by
  simpa using ((Real.continuous_exp.tendsto 0).mono_left nhdsWithin_le_nhds).sub_const 1

/-- The exponential and original displacement scales are asymptotically
equal, with the exact normalization retained. -/
theorem etaExpDisplacement_div_tendsto_one :
    Tendsto (fun r : ℝ ↦ (Real.exp r - 1) / r) (𝓝[>] 0) (𝓝 1) := by
  simpa only [zero_add, Real.exp_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    (Real.hasDerivAt_exp 0).tendsto_slope_zero_right

/-- Quantitative relative error between the exponential and original
positive displacements. -/
theorem etaExpDisplacement_ratio_error_bounds {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (Real.exp r - 1) / r - 1 ∈ Icc (0 : ℝ) r := by
  have hl : r ≤ Real.exp r - 1 := by linarith [Real.add_one_le_exp r]
  have hu := Real.abs_exp_sub_one_sub_id_le (show |r| ≤ 1 by rwa [abs_of_pos hr])
  have hu' := (le_abs_self (Real.exp r - 1 - r)).trans hu
  constructor
  · have h := (le_div_iff₀ hr).mpr (by simpa using hl : 1 * r ≤ Real.exp r - 1)
    linarith
  · have h := (div_le_iff₀ hr).mpr (show Real.exp r - 1 ≤ (r + 1) * r by nlinarith)
    linarith

/-- At the arithmetic scale, the evaluated finite part converges to the
Euler--Wallis constant on the full positive real displacement filter. -/
theorem pairedEtaMismatch_half_exp_finite_part_tendsto :
    Tendsto (fun r : ℝ ↦ pairedEtaMismatch (1 / 2) r / (Real.exp r - 1) + Real.log (Real.exp r - 1))
      (𝓝[>] 0) (𝓝 (Real.eulerMascheroniConstant - Real.log (Real.pi / 2))) := by
  have herror : Tendsto (fun r : ℝ ↦
      (pairedEtaMismatch (1 / 2) r / (Real.exp r - 1) + Real.log (Real.exp r - 1)) -
        ((harmonic (pairedEtaShiftBoundaryCutoff r) : ℝ) -
          Real.log (pairedEtaShiftBoundaryCutoff r) - Real.log (Real.pi / 2)))
      (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa using etaExpDisplacement_tendsto_zero.const_mul 32)
    filter_upwards [self_mem_nhdsWithin,
      (nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)))] with r hr hrsmall
    rw [Real.norm_eq_abs]
    exact pairedEtaMismatch_half_finite_part_harmonic_error_le hr hrsmall.le
  have hmain := (Real.tendsto_harmonic_sub_log.comp pairedEtaShiftBoundaryCutoff_tendsto_atTop)
    |>.sub_const (Real.log (Real.pi / 2))
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using herror.add hmain

/-- The potentially singular logarithmic correction caused by changing
the displacement normalization still vanishes. -/
theorem etaExpDisplacement_ratio_log_tendsto_zero :
    Tendsto (fun r : ℝ ↦ ((Real.exp r - 1) / r - 1) * Real.log (Real.exp r - 1))
      (𝓝[>] 0) (𝓝 0) := by
  have hdom : Tendsto (fun r : ℝ ↦ r * (-Real.log r)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one, neg_zero, neg_mul, mul_neg, mul_comm] using
      (tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one).neg
  apply squeeze_zero_norm' _ hdom
  filter_upwards [self_mem_nhdsWithin,
    (nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)))] with r hr hrsmall
  have hrpos : 0 < r := hr
  have hratio := etaExpDisplacement_ratio_error_bounds hrpos (by linarith [hrsmall.out])
  have he : 0 < Real.exp r - 1 := sub_pos.mpr (by simpa using Real.exp_lt_exp.mpr hrpos)
  have he1 := (pairedEtaShiftBoundaryCutoff_rescaled_bounds hrpos hrsmall.le).1
  have hlogeps : Real.log (Real.exp r - 1) ≤ 0 := Real.log_nonpos he.le he1
  have hlogle : Real.log r ≤ Real.log (Real.exp r - 1) :=
    Real.log_le_log hrpos (by linarith [Real.add_one_le_exp r])
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hratio.1, abs_of_nonpos hlogeps]
  exact mul_le_mul hratio.2 (by linarith : -Real.log (Real.exp r - 1) ≤ -Real.log r)
    (by linarith) hrpos.le

/-- The original scalar eta boundary law has an evaluated constant after
its critical logarithmic divergence. -/
theorem pairedEtaMismatch_half_finite_part_tendsto :
    Tendsto (fun r : ℝ ↦ pairedEtaMismatch (1 / 2) r / r - Real.log (1 / r))
      (𝓝[>] 0) (𝓝 (Real.eulerMascheroniConstant - Real.log (Real.pi / 2))) := by
  have hlogratio : Tendsto (fun r : ℝ ↦ Real.log ((Real.exp r - 1) / r)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.log_one, Function.comp_def] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp etaExpDisplacement_div_tendsto_one
  have h := ((etaExpDisplacement_div_tendsto_one.mul pairedEtaMismatch_half_exp_finite_part_tendsto).sub
    etaExpDisplacement_ratio_log_tendsto_zero).sub hlogratio
  simp only [one_mul, sub_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrpos : 0 < r := hr
  have he : Real.exp r - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (by simpa using Real.exp_lt_exp.mpr hrpos))
  rw [Real.log_div he hrpos.ne', Real.log_div one_ne_zero hrpos.ne', Real.log_one]
  field_simp
  ring

/-- A constant complex test recovers the actual scalar critical mismatch
without any restriction on the unused logarithmic test scale. -/
theorem pairedEtaWeightedMismatch_const (r R : ℝ) (c : ℂ) :
    pairedEtaWeightedMismatch r R (fun _ ↦ c) = pairedEtaMismatch (1 / 2) r • c := by
  simp only [pairedEtaWeightedMismatch, pairedEtaMismatch,
    show (2 : ℝ) * (1 / 2) = 1 by norm_num, neg_one_mul, integral_smul_const]

/-- The scalar finite part holds for every constant complex test, retaining
its complex value and allowing any logarithmic scale function. -/
theorem pairedEtaWeightedMismatch_const_finite_part_tendsto (R : ℝ → ℝ) (c : ℂ) :
    Tendsto (fun r : ℝ ↦ r⁻¹ • pairedEtaWeightedMismatch r (R r) (fun _ ↦ c) -
      Real.log (1 / r) • c) (𝓝[>] 0)
      (𝓝 ((Real.eulerMascheroniConstant - Real.log (Real.pi / 2)) • c)) := by
  simpa only [pairedEtaWeightedMismatch_const, smul_smul, ← sub_smul,
    div_eq_mul_inv, mul_comm] using pairedEtaMismatch_half_finite_part_tendsto.smul_const c

end

end RiemannGaussian
