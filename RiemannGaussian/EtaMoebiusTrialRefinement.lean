import RiemannGaussian.EtaMoebiusTrialGridGeometry

/-!
# Complete square-error control under arbitrary Möbius grid refinement

Exact block identities identify the original coarse and fine combinations
with two grids carrying the same signed coefficients. Their full critical
square distance is bounded independently of the refinement factor. The
arithmetic cutoff and all coefficient weights remain unchanged during
refinement; no approximation claim for the target is assumed.
-/

open Complex MeasureTheory Set

namespace RiemannGaussian

noncomputable section

/-- The actual Möbius combination on a uniform physical grid of arbitrary dimension. -/
def pairedEtaMoebiusTrialGridCombination (d M : ℕ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  pairedEtaTranslatedCombination (fun j : Fin d ↦ pairedEtaMoebiusTrialGridPoint d (j.1 + 1))
    (fun j ↦ (pairedEtaMoebiusTrialCoefficient d M w j : ℂ)) t

/-- The full signed refined coefficient vector, indexed in complete coarse-grid blocks. -/
def pairedEtaMoebiusTrialRefinedCoefficient (d M q : ℕ) (w : ℕ → ℝ) (i : Fin (d * q)) : ℂ :=
  pairedEtaMoebiusTrialEdgeCoefficient (d * q) M w (i.1 + q)

/-- Each fine coefficient keeps its own original nonnegative physical logarithm. -/
def pairedEtaMoebiusTrialRefinedFineGrid (d q : ℕ) (i : Fin (d * q)) : ℝ :=
  pairedEtaMoebiusTrialGridPoint (d * q) (i.1 + q)

/-- The same fine coefficients are assigned to their exact original coarse-grid endpoint. -/
def pairedEtaMoebiusTrialRefinedCoarseGrid (d q : ℕ) (i : Fin (d * q)) : ℝ :=
  pairedEtaMoebiusTrialGridPoint d (i.1 / q + 1)

/-- All reindexed fine terms give precisely the actual original fine-grid combination. -/
theorem pairedEtaMoebiusTrialRefinedFineGrid_eq {d M q : ℕ}
    (hMd : M ≤ d) (hq : 0 < q) (w : ℕ → ℝ) (t : ℝ) :
    pairedEtaTranslatedCombination (pairedEtaMoebiusTrialRefinedFineGrid d q)
      (pairedEtaMoebiusTrialRefinedCoefficient d M q w) t =
        pairedEtaMoebiusTrialGridCombination (d * q) M w t := by
  have h := sum_pairedEtaMoebiusTrialEdgeCoefficient_shift hMd hq w
    (fun m c ↦ (c : ℂ) * (pairedEtaTranslatedColour (pairedEtaMoebiusTrialGridPoint (d * q) m) t : ℂ))
    (by intro m; simp)
  change (∑ i : Fin (d * q), (pairedEtaMoebiusTrialEdgeCoefficient (d * q) M w (i.1 + q) : ℂ) *
    (pairedEtaTranslatedColour (pairedEtaMoebiusTrialGridPoint (d * q) (i.1 + q)) t : ℂ)) = _
  rw [h]
  simp only [pairedEtaMoebiusTrialEdgeCoefficient_eq, pairedEtaMoebiusTrialGridCombination,
    pairedEtaTranslatedCombination]

/-- The exact signed block sums recover the whole original coarse-grid combination. -/
theorem pairedEtaMoebiusTrialRefinedCoarseGrid_eq {q : ℕ} (hq : 0 < q)
    (d M : ℕ) (w : ℕ → ℝ) (t : ℝ) :
    pairedEtaTranslatedCombination (pairedEtaMoebiusTrialRefinedCoarseGrid d q)
      (pairedEtaMoebiusTrialRefinedCoefficient d M q w) t =
        pairedEtaMoebiusTrialGridCombination d M w t := by
  have h := sum_pairedEtaMoebiusTrialEdgeCoefficient_mul_block hq d M w
    (fun j ↦ (pairedEtaTranslatedColour (pairedEtaMoebiusTrialGridPoint d (j + 1)) t : ℂ))
  change (∑ i : Fin (d * q), (pairedEtaMoebiusTrialEdgeCoefficient (d * q) M w (i.1 + q) : ℂ) *
    (pairedEtaTranslatedColour (pairedEtaMoebiusTrialGridPoint d (i.1 / q + 1)) t : ℂ)) = _
  rw [h]
  simp only [pairedEtaMoebiusTrialEdgeCoefficient_eq, pairedEtaMoebiusTrialGridCombination,
    pairedEtaTranslatedCombination]

/-- The entire reindexed coefficient norm sum retains the original dimension-independent arithmetic bound. -/
theorem pairedEtaMoebiusTrialRefinedCoefficient_sum_norm_le {d M q : ℕ}
    (hMd : M ≤ d) (hq : 0 < q) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    (∑ i, ‖pairedEtaMoebiusTrialRefinedCoefficient d M q w i‖) ≤ 2 * M := by
  simp only [pairedEtaMoebiusTrialRefinedCoefficient, Complex.norm_real, Real.norm_eq_abs]
  rw [sum_pairedEtaMoebiusTrialEdgeCoefficient_shift hMd hq w (fun _ c ↦ |c|) (by intro m; simp)]
  simp only [pairedEtaMoebiusTrialEdgeCoefficient_eq]
  exact pairedEtaMoebiusTrialCoefficient_sum_abs_le (d * q) M hw

/-- Every active reindexed coefficient has the same refinement-independent logarithmic displacement bound. -/
theorem pairedEtaMoebiusTrialRefinedGrid_distance {d M q : ℕ}
    (hd : 0 < d) (hq : 0 < q) {w : ℕ → ℝ} (i : Fin (d * q))
    (hc : pairedEtaMoebiusTrialRefinedCoefficient d M q w i ≠ 0) :
    |pairedEtaMoebiusTrialRefinedCoarseGrid d q i - pairedEtaMoebiusTrialRefinedFineGrid d q i| ≤
      2 * (M : ℝ) / d := by
  have hj : i.1 / q < d := (Nat.div_lt_iff_lt_mul hq).mpr i.isLt
  have hl : i.1 % q < q := Nat.mod_lt _ hq
  have harg : q * (i.1 / q + 1) + i.1 % q = i.1 + q := by
    have h := Nat.mod_add_div i.1 q
    nlinarith
  have hcreal : pairedEtaMoebiusTrialEdgeCoefficient (d * q) M w (q * (i.1 / q + 1) + i.1 % q) ≠ 0 := by
    rw [harg]
    intro hz
    exact hc (by simp [pairedEtaMoebiusTrialRefinedCoefficient, hz])
  have h := pairedEtaMoebiusTrialGridPoint_block_distance hd hq hj hl hcreal
  simpa only [pairedEtaMoebiusTrialRefinedCoarseGrid, pairedEtaMoebiusTrialRefinedFineGrid, harg] using h

/-- The full original coarse-to-fine critical square error, with the arithmetic coefficients fixed. -/
def pairedEtaMoebiusTrialRefinementError (d M q : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, Real.exp (-t) *
    ‖pairedEtaMoebiusTrialGridCombination d M w t - pairedEtaMoebiusTrialGridCombination (d * q) M w t‖ ^ 2

/-- Exact regrouping identifies the actual full refinement error with the same-coefficient grid-distance integral. -/
theorem pairedEtaMoebiusTrialRefinementError_eq {d M q : ℕ}
    (hMd : M ≤ d) (hq : 0 < q) (w : ℕ → ℝ) :
    pairedEtaMoebiusTrialRefinementError d M q w =
      pairedEtaTranslateGridError (pairedEtaMoebiusTrialRefinedCoarseGrid d q)
        (pairedEtaMoebiusTrialRefinedFineGrid d q) (pairedEtaMoebiusTrialRefinedCoefficient d M q w) := by
  unfold pairedEtaMoebiusTrialRefinementError pairedEtaTranslateGridError
  simp_rw [pairedEtaMoebiusTrialRefinedCoarseGrid_eq hq,
    pairedEtaMoebiusTrialRefinedFineGrid_eq hMd hq]

/-- The actual full refinement-error kernel is integrable, with the coarse and fine combinations identified exactly. -/
theorem integrableOn_pairedEtaMoebiusTrialRefinementError {d M q : ℕ}
    (hMd : M ≤ d) (hq : 0 < q) (w : ℕ → ℝ) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t) *
      ‖pairedEtaMoebiusTrialGridCombination d M w t -
        pairedEtaMoebiusTrialGridCombination (d * q) M w t‖ ^ 2) (Ioi 0) := by
  have h := integrableOn_pairedEtaTranslateGridError
    (pairedEtaMoebiusTrialRefinedCoarseGrid d q) (pairedEtaMoebiusTrialRefinedFineGrid d q)
    (pairedEtaMoebiusTrialRefinedCoefficient d M q w)
  simpa only [pairedEtaMoebiusTrialRefinedCoarseGrid_eq hq,
    pairedEtaMoebiusTrialRefinedFineGrid_eq hMd hq] using h

/-- The complete refinement error is nonnegative on the unchanged actual carrier. -/
theorem pairedEtaMoebiusTrialRefinementError_nonneg (d M q : ℕ) (w : ℕ → ℝ) :
    0 ≤ pairedEtaMoebiusTrialRefinementError d M q w := integral_nonneg (fun _ ↦ by positivity)

/-- Every refinement has the same full critical-square error budget, with the entire infinite time range included. -/
theorem pairedEtaMoebiusTrialRefinementError_le {d M q : ℕ}
    (hd : 0 < d) (hMd : M ≤ d) (hq : 0 < q) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) (hsmall : 2 * (M : ℝ) / d ≤ 1 / 8) :
    pairedEtaMoebiusTrialRefinementError d M q w ≤
      32 * (M : ℝ) ^ 2 * Real.sqrt (2 * (M : ℝ) / d) := by
  rw [pairedEtaMoebiusTrialRefinementError_eq hMd hq]
  have h := pairedEtaTranslateGridError_le_sqrt
    (fun i ↦ pairedEtaMoebiusTrialGridPoint_nonneg d (i.1 / q + 1))
    (fun i ↦ pairedEtaMoebiusTrialGridPoint_nonneg (d * q) (i.1 + q))
    (pairedEtaMoebiusTrialRefinedCoefficient d M q w) hsmall
    (pairedEtaMoebiusTrialRefinedGrid_distance hd hq)
  apply h.trans
  calc
    _ ≤ 8 * Real.sqrt (2 * (M : ℝ) / d) * (2 * (M : ℝ)) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))
        (pairedEtaMoebiusTrialRefinedCoefficient_sum_norm_le hMd hq hw) 2
    _ = _ := by ring

end

end RiemannGaussian
