import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem windowHyp_of_rpow_eventually (K η : ℝ) (hK : 0 ≤ K) (hη : 0 < η) :
    ∃ Y₁ : ℝ, ∀ Y : ℝ, Y₁ ≤ Y → 1 ≤ Y ∧ K * Real.log Y ≤ Y ^ η := by
  have h2 : 0 < η / 2 := by positivity
  have h1 := (tendsto_rpow_atTop h2).eventually_ge_atTop (K / (η / 2))
  obtain ⟨Y₁, hY₁⟩ := Filter.eventually_atTop.1 (h1.and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨Y₁, fun Y hY => ?_⟩
  obtain ⟨ha, hb⟩ := hY₁ Y hY
  refine ⟨hb, ?_⟩
  have hY0 : 0 < Y := by linarith
  have hl := Real.log_le_rpow_div hY0.le h2
  have hp : 0 ≤ Y ^ (η / 2) := by positivity
  have he : Y ^ η = Y ^ (η / 2) * Y ^ (η / 2) := by
    rw [← Real.rpow_add hY0]; congr 1; ring
  calc K * Real.log Y ≤ K * (Y ^ (η / 2) / (η / 2)) := mul_le_mul_of_nonneg_left hl hK
    _ = K / (η / 2) * Y ^ (η / 2) := by ring
    _ ≤ Y ^ (η / 2) * Y ^ (η / 2) := mul_le_mul_of_nonneg_right ha hp
    _ = Y ^ η := he.symm

theorem windowHyp_of_rpow (F : CharFamily) {θ δ C : ℝ} (hδ : 0 < δ)
    (h : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), Gm F y ≤ C * y ^ θ) :
    WindowHyp F θ δ := by
  intro η hη Y₀
  obtain ⟨Y₁, hY₁⟩ := windowHyp_of_rpow_eventually (|C| * δ) η (by positivity) hη
  obtain ⟨Y, hY, hb⟩ := h (max Y₀ Y₁)
  obtain ⟨h1, hK⟩ := hY₁ Y (le_trans (le_max_right _ _) hY)
  have hY0 : 0 < Y := by linarith
  have hle : Y ≤ Y ^ (1 + δ) := by
    calc Y = Y ^ (1 : ℝ) := (Real.rpow_one Y).symm
      _ ≤ Y ^ (1 + δ) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have heq : Set.EqOn (fun y : ℝ => |C| * y ^ θ * y ^ (-θ - 1)) (fun y : ℝ => |C| * y⁻¹)
      (Set.Icc Y (Y ^ (1 + δ))) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hY0 hy.1
    simp only
    rw [mul_assoc, ← Real.rpow_add hy0, show θ + (-θ - 1) = -1 by ring, Real.rpow_neg_one]
  refine ⟨Y, le_trans (le_max_left _ _) hY, fun y => |C| * y ^ θ, ?_, ?_, ?_⟩
  · refine (integrableOn_congr_fun heq measurableSet_Icc).2 ?_
    refine ContinuousOn.integrableOn_Icc ?_
    exact continuousOn_const.mul (continuousOn_id.inv₀ fun y hy => (lt_of_lt_of_le hY0 hy.1).ne')
  · intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hY0 hy.1
    have hp : 0 ≤ y ^ θ := by positivity
    exact ⟨by positivity, (hb y hy).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hp)⟩
  · rw [setIntegral_congr_fun measurableSet_Icc heq, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle, intervalIntegral.integral_const_mul,
      integral_inv_of_pos hY0 (lt_of_lt_of_le hY0 hle),
      Real.log_div (lt_of_lt_of_le hY0 hle).ne' hY0.ne', Real.log_rpow hY0]
    calc |C| * ((1 + δ) * Real.log Y - Real.log Y) = |C| * δ * Real.log Y := by ring
      _ ≤ Y ^ η := hK

end Deduction

end
