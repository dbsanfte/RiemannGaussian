import RiemannGaussian.MoebiusGaussianCutoff

/-!
# Cancellation for the ordinary finite Möbius sum

The literal finite prefix is recovered from its exact Gaussian smoothing.
The complete cutoff error, including rounding, becomes arbitrarily small
relative to the arithmetic scale. Cancellation of the smoothed cumulative
source then proves sublinear cancellation for the unsmoothed finite sum.
-/

open Filter MeasureTheory
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The normalized ordinary finite prefix is bounded by its complete smoothing error, one rounding unit, and the actual cumulative Gaussian source. -/
theorem abs_moebiusLogPrefix_exp_ratio_le {tau : ℝ} (htau : 0 < tau) (a : ℝ) :
    |moebiusLogPrefix a / Real.exp a| ≤
      (∫ v : ℝ, moebiusCutoffGaussian tau v * |Real.exp v - 1|) / moebiusCutoffGaussianMass tau +
        Real.exp (-a) +
        |gaussianMoebiusCumulative a tau / Real.exp a| / moebiusCutoffGaussianMass tau := by
  have hc := moebiusCutoffGaussianMass_pos htau
  have he := abs_moebiusFinitePrefix_gaussian_error_le htau a
  have htri : moebiusCutoffGaussianMass tau * |moebiusLogPrefix a| ≤
      |moebiusCutoffGaussianMass tau * moebiusLogPrefix a - gaussianMoebiusCumulative a tau| +
        |gaussianMoebiusCumulative a tau| := by
    calc
      _ = |moebiusCutoffGaussianMass tau * moebiusLogPrefix a| := by rw [abs_mul, abs_of_pos hc]
      _ = |(moebiusCutoffGaussianMass tau * moebiusLogPrefix a - gaussianMoebiusCumulative a tau) +
          gaussianMoebiusCumulative a tau| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have hb := htri.trans (add_le_add he le_rfl)
  have hd := div_le_div_of_nonneg_right hb
    (mul_pos hc (Real.exp_pos a)).le
  rw [abs_div, abs_of_pos (Real.exp_pos a)]
  calc
    _ = (moebiusCutoffGaussianMass tau * |moebiusLogPrefix a|) /
        (moebiusCutoffGaussianMass tau * Real.exp a) := by field_simp
    _ ≤ _ := hd
    _ = _ := by
      rw [abs_div, abs_of_pos (Real.exp_pos a), Real.exp_neg]
      field_simp

/-- The actual unsmoothed finite Möbius prefix is o(exp(a)) on the logarithmic arithmetic scale. -/
theorem moebiusLogPrefix_exp_ratio_tendsto_zero :
    Tendsto (fun a : ℝ ↦ moebiusLogPrefix a / Real.exp a) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨tau, htau, herror⟩ := exists_moebiusCutoffGaussian_error_le (by linarith : 0 < eps / 2)
  have hc := moebiusCutoffGaussianMass_pos htau
  have herr : (∫ v : ℝ, moebiusCutoffGaussian tau v * |Real.exp v - 1|) /
      moebiusCutoffGaussianMass tau ≤ eps / 2 := (div_le_iff₀ hc).mpr herror
  have hz : Tendsto (fun a : ℝ ↦ Real.exp (-a) +
      |gaussianMoebiusCumulative a tau / Real.exp a| / moebiusCutoffGaussianMass tau) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).add
      ((gaussianMoebiusCumulative_exp_ratio_tendsto_zero htau).abs.div_const
        (moebiusCutoffGaussianMass tau))
  obtain ⟨A, hA⟩ := Metric.tendsto_atTop.mp hz (eps / 2) (by linarith)
  refine ⟨A, fun a ha ↦ ?_⟩
  have hb := hA a ha
  rw [Real.dist_eq, sub_zero] at hb ⊢
  have ht := le_abs_self (Real.exp (-a) +
    |gaussianMoebiusCumulative a tau / Real.exp a| / moebiusCutoffGaussianMass tau)
  have hn := abs_moebiusLogPrefix_exp_ratio_le htau a
  linarith

/-- On the original positive real cutoff scale, the ordinary finite Möbius sum is o(X). -/
theorem moebiusFinitePrefix_floor_div_tendsto_zero :
    Tendsto (fun X : ℝ ↦ moebiusFinitePrefix ⌊X⌋₊ / X) atTop (𝓝 0) := by
  have h := moebiusLogPrefix_exp_ratio_tendsto_zero.comp Real.tendsto_log_atTop
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  simp [moebiusLogPrefix, Real.exp_log hX]

/-- The literal finite signed Möbius prefixes have unconditional sublinear cancellation at integer cutoffs. -/
theorem moebiusFinitePrefix_div_tendsto_zero :
    Tendsto (fun M : ℕ ↦ moebiusFinitePrefix M / (M : ℝ)) atTop (𝓝 0) := by
  have h := moebiusFinitePrefix_floor_div_tendsto_zero.comp tendsto_natCast_atTop_atTop
  change Tendsto (fun M : ℕ ↦ moebiusFinitePrefix ⌊(M : ℝ)⌋₊ / (M : ℝ)) atTop (𝓝 0) at h
  simpa using h

/-- Every prescribed linear coefficient has one finite remainder valid at all actual integer cutoffs. -/
theorem exists_moebiusFinitePrefix_linear_remainder {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, |moebiusFinitePrefix M| ≤ eps * M + C := by
  obtain ⟨A, hA⟩ := Metric.tendsto_atTop.mp moebiusFinitePrefix_div_tendsto_zero eps heps
  let B := max A 1
  refine ⟨B, by positivity, fun M ↦ ?_⟩
  by_cases hM : B ≤ M
  · have h := hA M ((le_max_left _ _).trans hM)
    have hpos : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) ((le_max_right _ _).trans hM)
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hpos, div_lt_iff₀ hpos] at h
    have hB : (0 : ℝ) ≤ B := by positivity
    linarith
  · have h := abs_moebiusFinitePrefix_le M
    have hMB : (M : ℝ) ≤ B := by exact_mod_cast (le_of_not_ge hM)
    have hp : (0 : ℝ) ≤ eps * M := by positivity
    linarith

end

end RiemannGaussian
