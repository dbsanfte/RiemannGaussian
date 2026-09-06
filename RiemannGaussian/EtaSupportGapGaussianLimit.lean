import RiemannGaussian.EtaSupportGapGaussianCutoff
import RiemannGaussian.Hybrid.EtaSupportGapPhaseCoercivity

/-!
# Critical limits of actual eta displacement and phase heat matrices

Explicit arithmetic error estimates are converted into limits after
normalization by `h log(1/h)`. The ordinate can vary arbitrarily with the
heat width. Fixed scaled phases and their finite mixed matrices are
downstream specializations.
-/

open Complex Filter MeasureTheory Set Topology Matrix
open scoped Classical ENNReal Interval Topology BigOperators

namespace RiemannGaussian

noncomputable section

/-- The critical logarithmic scale diverges along positive widths tending to zero. -/
theorem tendsto_etaHeatLogScale_atTop :
    Tendsto (fun h : ℝ ↦ Real.log (1 / h)) (𝓝[>] (0 : ℝ)) atTop := by
  have hi : Tendsto (fun h : ℝ ↦ 1 / h) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [one_div] using (tendsto_inv_nhdsGT_zero : Tendsto (fun h : ℝ ↦ h⁻¹) (𝓝[>] 0) atTop)
  exact Real.tendsto_log_atTop.comp hi

/-- An eventual order-`h` error gives a vanishing relative critical error,
even when the comparison profile itself varies with the width. -/
theorem tendsto_etaHeat_relative_error_of_bound {f P : ℝ → ℝ} {C : ℝ}
    (hbound : ∀ᶠ h : ℝ in 𝓝[>] 0, |f h - h * Real.log (1 / h) * P h| ≤ C * h) :
    Tendsto (fun h ↦ f h / (h * Real.log (1 / h)) - P h) (𝓝[>] 0) (𝓝 0) := by
  have hdom : Tendsto (fun h : ℝ ↦ C / Real.log (1 / h)) (𝓝[>] 0) (𝓝 0) := by
    have hd := (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 0)).comp
      tendsto_etaHeatLogScale_atTop
    simpa only [div_eq_mul_inv, mul_zero, one_mul, Function.comp_def] using hd.const_mul C
  apply squeeze_zero_norm' _ hdom
  have hlt : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hbound, self_mem_nhdsWithin, hlt] with h hb hh hhone
  have hhpos : 0 < h := hh
  have hlog : 0 < Real.log (1 / h) := Real.log_pos ((one_lt_div hhpos).2 hhone)
  have hden : 0 < h * Real.log (1 / h) := mul_pos hhpos hlog
  rw [Real.norm_eq_abs,
    show f h / (h * Real.log (1 / h)) - P h =
      (f h - h * Real.log (1 / h) * P h) / (h * Real.log (1 / h)) by field_simp,
    abs_div, abs_of_pos hden]
  calc
    _ ≤ (C * h) / (h * Real.log (1 / h)) := div_le_div_of_nonneg_right hb hden.le
    _ = C / Real.log (1 / h) := by field_simp

/-- Relative convergence of the critical actual heat law for an arbitrary
width-dependent real ordinate; no regularity of that ordinate is required. -/
theorem pairedEtaSupportGapGaussianLeakage_relative_error_tendsto (gamma : ℝ → ℝ) :
    Tendsto (fun h : ℝ ↦
      pairedEtaSupportGapGaussianLeakage (1 / 2) h (fun t ↦ gamma h * t) /
        (h * Real.log (1 / h)) - pairedEtaHeatPhaseProfile (h * gamma h)) (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_etaHeat_relative_error_of_bound (C := 32)
  have hlt : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hlt] with h hh hhone
  exact pairedEtaSupportGapGaussianLeakage_uniform_error_le hh hhone.le (gamma h)

/-- The normalized actual heat transfer converges to the full profile at
each fixed scaled phase. -/
theorem pairedEtaSupportGapGaussianLeakage_scaled_tendsto (kappa : ℝ) :
    Tendsto (fun h : ℝ ↦
      pairedEtaSupportGapGaussianLeakage (1 / 2) h (fun t ↦ (kappa / h) * t) /
        (h * Real.log (1 / h))) (𝓝[>] 0) (𝓝 (pairedEtaHeatPhaseProfile kappa)) := by
  have hr := pairedEtaSupportGapGaussianLeakage_relative_error_tendsto (fun h ↦ kappa / h)
  have heq : (fun h : ℝ ↦
      pairedEtaSupportGapGaussianLeakage (1 / 2) h (fun t ↦ (kappa / h) * t) /
        (h * Real.log (1 / h)) - pairedEtaHeatPhaseProfile (h * (kappa / h))) =ᶠ[𝓝[>] 0]
      (fun h ↦ pairedEtaSupportGapGaussianLeakage (1 / 2) h (fun t ↦ (kappa / h) * t) /
        (h * Real.log (1 / h)) - pairedEtaHeatPhaseProfile kappa) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hhpos : 0 < h := hh
    rw [show h * (kappa / h) = kappa by field_simp]
  have hc := (hr.congr' heq).add_const (pairedEtaHeatPhaseProfile kappa)
  simpa only [sub_add_cancel, zero_add] using hc

/-- The same scaled-phase limit holds in the actual finite time square with
cutoff `log(1/h)`. -/
theorem pairedEtaSupportGapGaussianLeakageCutoff_scaled_tendsto (kappa : ℝ) :
    Tendsto (fun h : ℝ ↦
      pairedEtaSupportGapGaussianLeakageCutoff (1 / 2) h (fun t ↦ (kappa / h) * t)
        (Real.log (1 / h)) / (h * Real.log (1 / h))) (𝓝[>] 0) (𝓝 (pairedEtaHeatPhaseProfile kappa)) := by
  have hr : Tendsto (fun h : ℝ ↦
      pairedEtaSupportGapGaussianLeakageCutoff (1 / 2) h (fun t ↦ (kappa / h) * t)
        (Real.log (1 / h)) / (h * Real.log (1 / h)) - pairedEtaHeatPhaseProfile kappa)
      (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_etaHeat_relative_error_of_bound (C := 32 + 2 * Real.exp (1 / 4))
    have hlt : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [self_mem_nhdsWithin, hlt] with h hh hhone
    have hhpos : 0 < h := hh
    have hb := pairedEtaSupportGapGaussianLeakageCutoff_uniform_error_le hhpos hhone.le (kappa / h)
    simpa only [show h * (kappa / h) = kappa by field_simp] using hb
  simpa only [sub_add_cancel, zero_add] using hr.add_const (pairedEtaHeatPhaseProfile kappa)

/-- The critical arithmetic displacement itself has leading coefficient one. -/
theorem pairedEtaMismatch_critical_tendsto :
    Tendsto (fun r : ℝ ↦ pairedEtaMismatch (1 / 2) r / (r * Real.log (1 / r)))
      (𝓝[>] 0) (𝓝 1) := by
  have hr : Tendsto (fun r : ℝ ↦ pairedEtaMismatch (1 / 2) r / (r * Real.log (1 / r)) - 1)
      (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_etaHeat_relative_error_of_bound (C := 5)
    have hlt : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 / 8 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
    filter_upwards [self_mem_nhdsWithin, hlt] with r hr hrsmall
    simpa only [mul_one] using pairedEtaMismatch_critical_error_le hr hrsmall.le
  simpa only [sub_add_cancel, zero_add] using hr.add_const 1

/-- The actual uncoloured critical heat law has the exact normalized limit. -/
theorem pairedEtaSupportGapGaussianLeakage_critical_tendsto :
    Tendsto (fun h : ℝ ↦ pairedEtaSupportGapGaussianLeakage (1 / 2) h (fun _ ↦ 0) /
      (h * Real.log (1 / h))) (𝓝[>] 0) (𝓝 (2 / Real.sqrt Real.pi)) := by
  simpa only [zero_div, zero_mul, pairedEtaHeatPhaseProfile_zero] using
    pairedEtaSupportGapGaussianLeakage_scaled_tendsto 0

/-- Entrywise convergence of the entire fixed phase matrix in its product
topology. Finite families retain every mixed entry in this limit. -/
theorem pairedEtaSupportGapScaledPhaseGram_tendsto {ι : Type*} (kappa : ι → ℝ) :
    Tendsto (fun h : ℝ ↦ (1 / (h * Real.log (1 / h))) • pairedEtaSupportGapScaledPhaseGram h kappa)
      (𝓝[>] 0) (𝓝 (pairedEtaHeatProfileGram kappa)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hf : (fun h : ℝ ↦ ((1 / (h * Real.log (1 / h))) •
      pairedEtaSupportGapScaledPhaseGram h kappa) i j) =
      (fun h ↦ pairedEtaSupportGapGaussianLeakage (1 / 2) h
        (fun t ↦ ((kappa j - kappa i) / h) * t) / (h * Real.log (1 / h))) := by
    funext h
    simp only [Matrix.smul_apply, smul_eq_mul, pairedEtaSupportGapScaledPhaseGram,
      pairedEtaSupportGapPhaseGram]
    have hphase : (fun t : ℝ ↦ kappa j / h * t - kappa i / h * t) =
        (fun t ↦ ((kappa j - kappa i) / h) * t) := by funext t; ring
    rw [hphase]
    ring
  rw [hf]
  exact pairedEtaSupportGapGaussianLeakage_scaled_tendsto (kappa j - kappa i)

end

end RiemannGaussian
