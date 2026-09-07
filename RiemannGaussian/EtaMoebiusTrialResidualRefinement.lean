import RiemannGaussian.EtaMoebiusTrialRefinement
import RiemannGaussian.EtaTranslateResidualStability

/-!
# Stability of the complete target residual under Möbius grid refinement

The full residual energies of the actual coarse and fine arithmetic
candidates differ by at most `16/M + 64*sqrt(2*M^11/d)` when `M≥1`
and the coarse grid is sufficiently fine. Every original target, signed
coefficient, and infinite tail is included. This compares approximations;
it does not assert that either residual tends to zero.
-/

open Complex

namespace RiemannGaussian

noncomputable section

/-- The original compact-target residual energy of the actual Möbius combination on a physical grid. -/
def pairedEtaMoebiusTrialGridResidualEnergy (d M : ℕ) (w : ℕ → ℝ) : ℝ :=
  pairedEtaTranslatedResidualEnergy (fun j : Fin d ↦ pairedEtaMoebiusTrialGridPoint d (j.1 + 1))
    (fun j ↦ (pairedEtaMoebiusTrialCoefficient d M w j : ℂ))

/-- Exact signed regrouping preserves the full original coarse-grid target residual. -/
theorem pairedEtaMoebiusTrialRefinedCoarseGrid_residualEnergy_eq {q : ℕ} (hq : 0 < q)
    (d M : ℕ) (w : ℕ → ℝ) :
    pairedEtaTranslatedResidualEnergy (pairedEtaMoebiusTrialRefinedCoarseGrid d q)
      (pairedEtaMoebiusTrialRefinedCoefficient d M q w) = pairedEtaMoebiusTrialGridResidualEnergy d M w := by
  unfold pairedEtaTranslatedResidualEnergy pairedEtaMoebiusTrialGridResidualEnergy pairedEtaTranslatedResidual
  simp_rw [pairedEtaMoebiusTrialRefinedCoarseGrid_eq hq]
  rfl

/-- The original fine-grid target residual retains the entire integral after reindexing. -/
theorem pairedEtaMoebiusTrialRefinedFineGrid_residualEnergy_eq {d M q : ℕ}
    (hMd : M ≤ d) (hq : 0 < q) (w : ℕ → ℝ) :
    pairedEtaTranslatedResidualEnergy (pairedEtaMoebiusTrialRefinedFineGrid d q)
      (pairedEtaMoebiusTrialRefinedCoefficient d M q w) = pairedEtaMoebiusTrialGridResidualEnergy (d * q) M w := by
  unfold pairedEtaTranslatedResidualEnergy pairedEtaMoebiusTrialGridResidualEnergy pairedEtaTranslatedResidual
  simp_rw [pairedEtaMoebiusTrialRefinedFineGrid_eq hMd hq]
  rfl

/-- A tunable comparison of the two complete actual residual energies, with the entire coefficient norm and grid error controlled. -/
theorem abs_pairedEtaMoebiusTrialGridResidualEnergy_sub_le {d M q : ℕ}
    (hMd : M ≤ d) (hq : 0 < q) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) {e : ℝ} (he : 0 < e) :
    |pairedEtaMoebiusTrialGridResidualEnergy d M w - pairedEtaMoebiusTrialGridResidualEnergy (d * q) M w| ≤
      e * (2 + 2 * (M : ℝ)) ^ 2 + (1 + 1 / e) * pairedEtaMoebiusTrialRefinementError d M q w := by
  have h := abs_pairedEtaTranslatedResidualEnergy_sub_le_grid_error
    (pairedEtaMoebiusTrialRefinedCoarseGrid d q) (pairedEtaMoebiusTrialRefinedFineGrid d q)
    (pairedEtaMoebiusTrialRefinedCoefficient d M q w) he
  rw [pairedEtaMoebiusTrialRefinedCoarseGrid_residualEnergy_eq hq,
    pairedEtaMoebiusTrialRefinedFineGrid_residualEnergy_eq hMd hq,
    ← pairedEtaMoebiusTrialRefinementError_eq hMd hq] at h
  apply h.trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ he.le
  apply pow_le_pow_left₀ (by positivity) _ 2
  exact add_le_add le_rfl (pairedEtaMoebiusTrialRefinedCoefficient_sum_norm_le hMd hq hw)

/-- The whole actual residual-energy difference has an explicit arithmetic and mesh bound, uniformly over the refinement factor. -/
theorem abs_pairedEtaMoebiusTrialGridResidualEnergy_sub_le_explicit {d M q : ℕ}
    (hd : 0 < d) (hM : 1 ≤ M) (hMd : M ≤ d) (hq : 0 < q) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) (hsmall : 2 * (M : ℝ) / d ≤ 1 / 8) :
    |pairedEtaMoebiusTrialGridResidualEnergy d M w - pairedEtaMoebiusTrialGridResidualEnergy (d * q) M w| ≤
      16 / (M : ℝ) + 64 * Real.sqrt (2 * (M : ℝ) ^ 11 / d) := by
  have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  have he : 0 < 1 / (M : ℝ) ^ 3 := by positivity
  have hfirst : (1 / (M : ℝ) ^ 3) * (2 + 2 * (M : ℝ)) ^ 2 ≤ 16 / (M : ℝ) := by
    calc
      _ ≤ (1 / (M : ℝ) ^ 3) * (4 * (M : ℝ)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ he.le
        exact pow_le_pow_left₀ (by positivity) (by linarith : 2 + 2 * (M : ℝ) ≤ 4 * M) 2
      _ = _ := by field_simp; norm_num
  have hpow : (1 : ℝ) ≤ (M : ℝ) ^ 3 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hMreal 3
  have hsecond : (1 + 1 / (1 / (M : ℝ) ^ 3)) * pairedEtaMoebiusTrialRefinementError d M q w ≤
      64 * Real.sqrt (2 * (M : ℝ) ^ 11 / d) := by
    simp only [one_div_one_div]
    calc
      _ ≤ (2 * (M : ℝ) ^ 3) * (32 * (M : ℝ) ^ 2 * Real.sqrt (2 * (M : ℝ) / d)) :=
        mul_le_mul (by linarith) (pairedEtaMoebiusTrialRefinementError_le hd hMd hq hw hsmall)
          (pairedEtaMoebiusTrialRefinementError_nonneg d M q w) (by positivity)
      _ = 64 * ((M : ℝ) ^ 5 * Real.sqrt (2 * (M : ℝ) / d)) := by ring
      _ = 64 * Real.sqrt (((M : ℝ) ^ 5) ^ 2 * (2 * (M : ℝ) / d)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (M : ℝ) ^ 5)]
      _ = _ := by congr 1; congr 1; ring
  exact (abs_pairedEtaMoebiusTrialGridResidualEnergy_sub_le hMd hq hw he).trans (add_le_add hfirst hsecond)

end

end RiemannGaussian
