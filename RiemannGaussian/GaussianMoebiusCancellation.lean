import RiemannGaussian.GaussianMoebiusScaleEnvelope

/-!
# An unconditional cancellation rate for the actual Gaussian Möbius sum

At fixed heat time one, the height choice T=a yields an eventual bound
exp(a-a/(1000000 log(a+22))). Every scale and convergence requirement is
discharged for the actual arithmetic sum. Its ratio to exp(a) tends to
zero. This is not a fixed power saving and does not prove the uniform
weighted estimate for the original signed eta current.
-/

open Filter
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- Every fixed power of the actual logarithmic height is negligible compared with arithmetic scale. -/
theorem tendsto_localZetaLogHeight_pow_div_zero (n : ℕ) :
    Tendsto (fun a : ℝ ↦ localZetaLogHeight a ^ n / a) atTop (𝓝 0) := by
  have hshift : Tendsto (fun a : ℝ ↦ a + 22) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-22) n one_ne_zero).comp hshift
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
  simp [localZetaLogHeight, abs_of_nonneg ha]

/-- The fixed squared-logarithm cost is eventually at most half the proved left-line gain. -/
theorem eventually_gaussianMoebiusScaleCost_le_half_gain :
    ∀ᶠ a : ℝ in atTop, gaussianMoebiusScaleExponent * localZetaLogHeight a ^ 2 ≤
      a / (1000000 * localZetaLogHeight a) := by
  have hzero : Tendsto
      (fun a : ℝ ↦ (1000000 * gaussianMoebiusScaleExponent) * (localZetaLogHeight a ^ 3 / a))
      atTop (𝓝 0) := by
    simpa using (tendsto_localZetaLogHeight_pow_div_zero 3).const_mul (1000000 * gaussianMoebiusScaleExponent)
  have hsmall : ∀ᶠ a : ℝ in atTop,
      (1000000 * gaussianMoebiusScaleExponent) * (localZetaLogHeight a ^ 3 / a) < 1 :=
    hzero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with a ha haone
  have hapos : 0 < a := by linarith
  have hL : 0 < localZetaLogHeight a := by linarith [two_lt_localZetaLogHeight a]
  rw [← mul_div_assoc, div_lt_iff₀ hapos] at ha
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- The actual convergent Gaussian Möbius sum has an unconditional reciprocal-logarithm exponential gain at unit heat time. -/
theorem gaussianMoebiusSum_one_le_reciprocal_log_gain_eventually :
    ∀ᶠ a : ℝ in atTop, |gaussianMoebiusSum a 1| ≤
      Real.exp (a - a / (1000000 * localZetaLogHeight a)) := by
  filter_upwards [eventually_ge_atTop (22 : ℝ),
    eventually_ge_atTop (Real.exp (1 / (500000 * zetaReciprocalLowHeightWidth))),
    eventually_gaussianMoebiusScaleCost_le_half_gain] with a ha hlarge hcost
  apply (gaussianMoebiusSum_one_le_logSquare_envelope ha hlarge).trans
  apply Real.exp_le_exp.mpr
  have hhalf : a / (500000 * localZetaLogHeight a) = 2 * (a / (1000000 * localZetaLogHeight a)) := by ring
  linarith

/-- The proved exponential gain grows without bound on the actual logarithmic arithmetic scale. -/
theorem tendsto_gaussianMoebiusReciprocalLogGain_atTop :
    Tendsto (fun a : ℝ ↦ a / (1000000 * localZetaLogHeight a)) atTop atTop := by
  have hzero : Tendsto (fun a : ℝ ↦ 1000000 * localZetaLogHeight a / a) atTop (𝓝 0) := by
    have h := (tendsto_localZetaLogHeight_pow_div_zero 1).const_mul 1000000
    simpa only [pow_one, mul_div_assoc, mul_zero] using h
  have hpos : ∀ᶠ a : ℝ in atTop, 0 < 1000000 * localZetaLogHeight a / a := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
    have hL : 0 < localZetaLogHeight a := by linarith [two_lt_localZetaLogHeight a]
    positivity
  have hright : Tendsto (fun a : ℝ ↦ 1000000 * localZetaLogHeight a / a) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  have h := hright.inv_tendsto_nhdsGT_zero
  change Tendsto (fun a : ℝ ↦ (1000000 * localZetaLogHeight a / a)⁻¹) atTop atTop at h
  simpa only [inv_div] using h

/-- The actual signed Gaussian Möbius sum is negligible compared with the unsaved exponential arithmetic scale. -/
theorem gaussianMoebiusSum_one_exp_ratio_tendsto_zero :
    Tendsto (fun a : ℝ ↦ gaussianMoebiusSum a 1 / Real.exp a) atTop (𝓝 0) := by
  have hexp : Tendsto (fun a : ℝ ↦ Real.exp (-(a / (1000000 * localZetaLogHeight a)))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_gaussianMoebiusReciprocalLogGain_atTop)
  refine squeeze_zero_norm' ?_ hexp
  filter_upwards [gaussianMoebiusSum_one_le_reciprocal_log_gain_eventually] with a ha
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.exp_pos a)]
  apply (div_le_div_of_nonneg_right ha (Real.exp_pos a).le).trans_eq
  rw [← Real.exp_sub]
  congr 1
  ring

/-- On the original multiplicative scale, the actual unit-time logarithmic Gaussian Möbius sum is o(X). -/
theorem gaussianMoebiusSum_log_one_div_tendsto_zero :
    Tendsto (fun X : ℝ ↦ gaussianMoebiusSum (Real.log X) 1 / X) atTop (𝓝 0) := by
  have h := gaussianMoebiusSum_one_exp_ratio_tendsto_zero.comp Real.tendsto_log_atTop
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  simp [Real.exp_log hX]

end

end RiemannGaussian
