import RiemannGaussian.EtaMoebiusArithmeticCells
import RiemannGaussian.EtaMoebiusContinuumBudget

/-!
# The complete arithmetic square sum equals the actual continuum residual

Each original integer-log cell contributes exactly the square of its
signed divisor residual coefficient. The original cells form a disjoint
measurable partition of the entire positive time axis, and the actual
residual is integrable there. The resulting infinite arithmetic square sum
therefore includes every exterior cell and equals the complete residual,
rather than a finite-window surrogate.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The actual weighted square integral on each original logarithmic cell is exactly one square of its complete signed arithmetic residual coefficient. -/
theorem integral_pairedEtaMoebiusContinuumResidual_sq_cell (M : ℕ) (w : ℕ → ℝ) (n : ℕ) :
    (∫ t : ℝ in pairedEtaLogCell n, Real.exp (-t) *
      ‖pairedEtaProjectionHead t - pairedEtaMoebiusContinuumCombination M w t‖ ^ 2) =
      pairedEtaMoebiusArithmeticCellResidual M w (n + 1) ^ 2 := by
  calc
    _ = ∫ t : ℝ in pairedEtaLogCell n,
        Real.exp t * pairedEtaMoebiusArithmeticCellResidual M w (n + 1) ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      have hc : t ∈ Ioc (Real.log (n + 1 : ℕ)) (Real.log ((n + 1 : ℕ) + 1 : ℝ)) := by
        simpa only [pairedEtaLogCell, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using ht
      dsimp only
      rw [pairedEtaMoebiusContinuumResidual_eq_arithmetic_cell M w (Nat.succ_pos n) hc,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
      calc
        _ = (Real.exp (-t) * Real.exp t) * Real.exp t *
            pairedEtaMoebiusArithmeticCellResidual M w (n + 1) ^ 2 := by ring
        _ = _ := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ = (∫ t : ℝ in pairedEtaLogCell n, Real.exp t) *
        pairedEtaMoebiusArithmeticCellResidual M w (n + 1) ^ 2 := by rw [integral_mul_const]
    _ = _ := by
      rw [pairedEtaLogCell, ← intervalIntegral.integral_of_le
        (Real.log_le_log (by positivity : (0 : ℝ) < n + 1) (by linarith : (n : ℝ) + 1 ≤ n + 2)),
        integral_exp, Real.exp_log (by positivity : (0 : ℝ) < n + 2),
        Real.exp_log (by positivity : (0 : ℝ) < n + 1)]
      ring

private theorem arithmetic_cells_cover : (⋃ n : ℕ, pairedEtaLogCell n) = Ioi (0 : ℝ) := by
  simpa only [pairedEtaLogCell] using iUnion_logSuccInterval_eq_Ioi_zero

/-- The signed divisor residual squares have a genuine infinite sum equal to the complete original continuum residual energy, including every cell beyond the arithmetic cutoff. -/
theorem hasSum_pairedEtaMoebiusArithmeticCellResidual_sq (M : ℕ) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    HasSum (fun n : ℕ ↦ pairedEtaMoebiusArithmeticCellResidual M w (n + 1) ^ 2)
      (pairedEtaMoebiusContinuumResidualEnergy M w) := by
  have hi : IntegrableOn (fun t : ℝ ↦ Real.exp (-t) *
      ‖pairedEtaProjectionHead t - pairedEtaMoebiusContinuumCombination M w t‖ ^ 2)
      (⋃ n : ℕ, pairedEtaLogCell n) := by
    rw [arithmetic_cells_cover]
    exact integrableOn_pairedEtaMoebiusContinuumResidualEnergy M hw
  have h := hasSum_integral_iUnion (s := pairedEtaLogCell) (fun _ : ℕ ↦ measurableSet_Ioc)
    pairwise_disjoint_pairedEtaLogCell hi
  simpa only [integral_pairedEtaMoebiusContinuumResidual_sq_cell, arithmetic_cells_cover,
    pairedEtaMoebiusContinuumResidualEnergy] using h

/-- The complete arithmetic residual sequence is square summable for each fixed finite arithmetic cutoff, with actual integrability rather than a totalized infinite sum as justification. -/
theorem summable_pairedEtaMoebiusArithmeticCellResidual_sq (M : ℕ) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    Summable (fun n : ℕ ↦ pairedEtaMoebiusArithmeticCellResidual M w (n + 1) ^ 2) :=
  (hasSum_pairedEtaMoebiusArithmeticCellResidual_sq M hw).summable

/-- The actual full critical target residual is exactly the infinite square sum of the explicit signed divisor errors. -/
theorem pairedEtaMoebiusContinuumResidualEnergy_eq_arithmetic_sum (M : ℕ) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    pairedEtaMoebiusContinuumResidualEnergy M w =
      ∑' n : ℕ, pairedEtaMoebiusArithmeticCellResidual M w (n + 1) ^ 2 :=
  (hasSum_pairedEtaMoebiusArithmeticCellResidual_sq M hw).tsum_eq.symm

/-- The unchanged canonical deficit is bounded by the complete signed arithmetic square sum plus the already proved vanishing allowance. -/
theorem pairedEtaDyadicTranslateDeficit_le_moebius_arithmetic_sum {k : ℕ} (hk : 7 ≤ k) :
    pairedEtaDyadicTranslateDeficit k ≤
      (∑' n : ℕ, pairedEtaMoebiusArithmeticCellResidual (k + 1)
        (pairedEtaMoebiusTrialLogWeight (k + 1)) (n + 1) ^ 2) +
      pairedEtaDyadicMoebiusRefinedAllowance k := by
  have h := pairedEtaDyadicTranslateDeficit_le_moebius_continuum hk
  unfold pairedEtaDyadicMoebiusContinuumResidual at h
  rwa [pairedEtaMoebiusContinuumResidualEnergy_eq_arithmetic_sum (k + 1)
    (fun _ hn ↦ abs_pairedEtaMoebiusTrialLogWeight_le hn)] at h

/-- Every original actual zero displacement is bounded by the entire signed divisor square sum with the existing vanishing allowance; no arithmetic-decay premise is assumed. -/
theorem pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_moebius_arithmetic_sum
    (rho : NontrivialZetaZero) {k : ℕ} (hk : 7 ≤ k) :
    pairedEtaCurrentHorizontalDisplacement rho * pairedEtaProjectionHeadZeroWeight rho ≤
      (∑' n : ℕ, pairedEtaMoebiusArithmeticCellResidual (k + 1)
        (pairedEtaMoebiusTrialLogWeight (k + 1)) (n + 1) ^ 2) +
      pairedEtaDyadicMoebiusRefinedAllowance k :=
  (pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_dyadicDeficit rho k).trans
    (pairedEtaDyadicTranslateDeficit_le_moebius_arithmetic_sum hk)

end

end RiemannGaussian
