import RiemannGaussian.EtaMoebiusBeurlingCells
import RiemannGaussian.EtaDyadicDifferenceEnergy

/-!
# Full norm comparison with the original balanced floor cells

The actual eta residual is the dyadic difference of the exact discrete
Hardy transform of its original balanced arithmetic cells. The Hardy
transform preserves their full weighted norm, while the dyadic difference
has universal upper and lower bounds. Hence the eta colour representation
does not remove the norm-decay obligation for the same coefficient family.
-/

open Filter MeasureTheory
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The full reciprocal-cell-weighted energy of the original balanced fractional-part coefficients. -/
def pairedEtaMoebiusBeurlingCellEnergy (M : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, pairedEtaMoebiusBeurlingCell M w (n + 1) ^ 2 / ((n + 1 : ℝ) * (n + 2 : ℝ))

private theorem beurling_zero (M : ℕ) (w : ℕ → ℝ) : pairedEtaMoebiusBeurlingCell M w 0 = 0 := by
  simp [pairedEtaMoebiusBeurlingCell]

private theorem harmonic_zero (M : ℕ) (w : ℕ → ℝ) : pairedEtaMoebiusBeurlingHarmonicPrefix M w 0 = 0 := by
  simp [pairedEtaMoebiusBeurlingHarmonicPrefix, etaUnpairedArithmeticHarmonicPrefix]

/-- The exact Hardy transform and the original unpaired harmonic primitive differ only by their literal zeroth transformed cell. -/
theorem etaDiscreteHardyTransform_beurling_eq_harmonic {M : ℕ} {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) (L : ℕ) :
    etaDiscreteHardyTransform (pairedEtaMoebiusBeurlingCell M w) L =
      etaDiscreteHardyTransform (pairedEtaMoebiusBeurlingCell M w) 0 + pairedEtaMoebiusBeurlingHarmonicPrefix M w L := by
  induction L with
  | zero => rw [harmonic_zero, add_zero]
  | succ L ih =>
    have hq := etaDiscreteHardyTransform_succ_sub (abs_pairedEtaMoebiusBeurlingCell_le hw) L
    have hh := pairedEtaMoebiusBeurlingHarmonicPrefix_succ_sub M L w
    linarith

/-- At every cell, the unchanged eta residual is precisely the signed dyadic difference of the Hardy transform of the original balanced fractional-part cells. -/
theorem pairedEtaMoebiusArithmeticCellResidual_eq_hardy_dyadic {M : ℕ} {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) (L : ℕ) :
    pairedEtaMoebiusArithmeticCellResidual M w L =
      etaDyadicCellDifference (etaDiscreteHardyTransform (pairedEtaMoebiusBeurlingCell M w)) L := by
  rw [pairedEtaMoebiusArithmeticCellResidual_eq_beurling_dyadic,
    etaDyadicCellDifference, etaDiscreteHardyTransform_beurling_eq_harmonic hw L,
    etaDiscreteHardyTransform_beurling_eq_harmonic hw (L / 2)]
  ring

/-- The unchanged full continuum energy equals the genuine square sum of the signed dyadic Hardy difference, including the empty-cell cancellation. -/
theorem pairedEtaMoebiusContinuumResidualEnergy_eq_hardy_dyadic_sum {M : ℕ} {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    pairedEtaMoebiusContinuumResidualEnergy M w =
      ∑' L : ℕ, etaDyadicCellDifference (etaDiscreteHardyTransform (pairedEtaMoebiusBeurlingCell M w)) L ^ 2 := by
  rw [pairedEtaMoebiusContinuumResidualEnergy_eq_arithmetic_sum M hw]
  simp_rw [pairedEtaMoebiusArithmeticCellResidual_eq_hardy_dyadic hw]
  have hs := summable_etaDyadicCellDifference_sq
    (summable_etaDiscreteHardyTransform_sq (abs_pairedEtaMoebiusBeurlingCell_le hw))
  have he := hs.sum_add_tsum_nat_add 1
  simpa only [Finset.sum_range_one, etaDyadicCellDifference, Nat.zero_div, sub_self,
    zero_pow (by decide : 2 ≠ 0), zero_add] using he

/-- The complete eta residual energy and the full balanced floor-cell energy are comparable in both directions by fixed positive constants independent of the arithmetic cutoff and original bounded weights. -/
theorem pairedEtaMoebiusContinuumResidualEnergy_beurling_bounds {M : ℕ} {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    pairedEtaMoebiusBeurlingCellEnergy M w / 6 ≤ pairedEtaMoebiusContinuumResidualEnergy M w ∧
      pairedEtaMoebiusContinuumResidualEnergy M w ≤ 6 * pairedEtaMoebiusBeurlingCellEnergy M w := by
  have h := etaDyadicCellDifferenceEnergy_bounds
    (summable_etaDiscreteHardyTransform_sq (abs_pairedEtaMoebiusBeurlingCell_le hw))
  rw [tsum_etaDiscreteHardyTransform_sq_eq (abs_pairedEtaMoebiusBeurlingCell_le hw) (beurling_zero M w),
    ← pairedEtaMoebiusContinuumResidualEnergy_eq_hardy_dyadic_sum hw] at h
  exact h

/-- For the exact logarithmic family, decay of the actual full eta residual is equivalent to decay of its balanced floor-cell norm; neither direction supplies the missing arithmetic decay. -/
theorem pairedEtaMoebiusContinuumResidualEnergy_tendsto_zero_iff_beurling :
    Tendsto (fun M : ℕ ↦ pairedEtaMoebiusContinuumResidualEnergy M (pairedEtaMoebiusTrialLogWeight M)) atTop (𝓝 0) ↔
      Tendsto (fun M : ℕ ↦ pairedEtaMoebiusBeurlingCellEnergy M (pairedEtaMoebiusTrialLogWeight M)) atTop (𝓝 0) := by
  constructor
  · intro he
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ tsum_nonneg (fun _ ↦ by positivity))) _
      (by simpa only [mul_zero] using he.const_mul (6 : ℝ))
    exact Eventually.of_forall (fun M ↦ by
      change pairedEtaMoebiusBeurlingCellEnergy M (pairedEtaMoebiusTrialLogWeight M) ≤
        6 * pairedEtaMoebiusContinuumResidualEnergy M (pairedEtaMoebiusTrialLogWeight M)
      have h := (pairedEtaMoebiusContinuumResidualEnergy_beurling_bounds
        (fun _ hn ↦ abs_pairedEtaMoebiusTrialLogWeight_le hn : ∀ n ∈ Finset.Icc 1 M, |pairedEtaMoebiusTrialLogWeight M n| ≤ 1)).1
      linarith)
  · intro hb
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ integral_nonneg (fun _ ↦ by positivity))) _
      (by simpa only [mul_zero] using hb.const_mul (6 : ℝ))
    exact Eventually.of_forall (fun M ↦ (pairedEtaMoebiusContinuumResidualEnergy_beurling_bounds
      (fun _ hn ↦ abs_pairedEtaMoebiusTrialLogWeight_le hn : ∀ n ∈ Finset.Icc 1 M, |pairedEtaMoebiusTrialLogWeight M n| ≤ 1)).2)

end

end RiemannGaussian
