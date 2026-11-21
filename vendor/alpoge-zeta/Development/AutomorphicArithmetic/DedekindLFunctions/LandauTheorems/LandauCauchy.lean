import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem landau_cauchy {Φ : ℂ → ℂ} {z : ℂ} {r r' : ℝ} (hd : DifferentiableOn ℂ Φ (Metric.ball z r))
    (h0 : 0 < r') (h1 : r' < r) :
    ∃ M : ℝ, ∀ k : ℕ, ‖iteratedDeriv k Φ z / (k.factorial : ℂ)‖ ≤ M / r' ^ k := by
  set R : NNReal := ⟨r', h0.le⟩ with hRdef
  have hR : (R : ℝ) = r' := rfl
  refine ⟨(2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi, ‖Φ (circleMap z r' θ)‖, fun k => ?_⟩
  have hsub : Metric.closedBall z (R : ℝ) ⊆ Metric.ball z r := by
    rw [hR]; exact Metric.closedBall_subset_ball h1
  have hRpos : (0 : NNReal) < R := by
    show (0 : ℝ) < (R : ℝ); rw [hR]; exact h0
  have hp := (hd.mono hsub).hasFPowerSeriesOnBall hRpos
  have key := hp.factorial_smul (1 : ℂ) k
  have hderiv : iteratedDeriv k Φ z / (k.factorial : ℂ) = cauchyPowerSeries Φ z (R : ℝ) k (fun _ => 1) := by
    rw [iteratedDeriv_eq_iteratedFDeriv, ← key, nsmul_eq_mul]
    have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp
  rw [hderiv]
  calc ‖cauchyPowerSeries Φ z (R : ℝ) k (fun _ => 1)‖
      ≤ ‖cauchyPowerSeries Φ z (R : ℝ) k‖ * ∏ _i : Fin k, ‖(1 : ℂ)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖cauchyPowerSeries Φ z (R : ℝ) k‖ := by simp
    _ ≤ ((2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi, ‖Φ (circleMap z (R : ℝ) θ)‖) * |(R : ℝ)|⁻¹ ^ k :=
        norm_cauchyPowerSeries_le _ _ _ _
    _ = _ := by
        rw [hR, abs_of_pos h0, inv_pow, div_eq_mul_inv]

end Deduction

end
