import RiemannGaussian.EtaMoebiusContinuumCombination
import RiemannGaussian.EtaMoebiusTrialResidualRefinement
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Full critical square transport to the exact arithmetic continuum carrier

A genuine integrable dominator controls the entire positive time axis at
each fixed arithmetic cutoff. Thus the original grid square integrals
converge to those of the identified signed continuum carrier. Passing the
existing refinement estimate through this limit gives a quantitative
full-grid-to-continuum error; no compact-window truncation is substituted.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The actual complete critical square distance between a finite physical grid and its identified signed arithmetic continuum carrier. -/
def pairedEtaMoebiusContinuumGridError (d M : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, Real.exp (-t) *
    ‖pairedEtaMoebiusTrialGridCombination d M w t - pairedEtaMoebiusContinuumCombination M w t‖ ^ 2

/-- The complete target residual of the exact signed continuum arithmetic, on the entire original positive time axis. -/
def pairedEtaMoebiusContinuumResidualEnergy (M : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, Real.exp (-t) *
    ‖pairedEtaProjectionHead t - pairedEtaMoebiusContinuumCombination M w t‖ ^ 2

private theorem integrableOn_exp_neg : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi 0) := by
  simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) (0 : ℝ)

/-- The identified continuum carrier has a genuinely integrable full target residual, with all analytic hypotheses discharged. -/
theorem integrableOn_pairedEtaMoebiusContinuumResidualEnergy (M : ℕ) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t) *
      ‖pairedEtaProjectionHead t - pairedEtaMoebiusContinuumCombination M w t‖ ^ 2) (Ioi 0) := by
  apply integrableOn_exp_neg.mul_bdd
    ((measurable_pairedEtaProjectionHead.sub (measurable_pairedEtaMoebiusContinuumCombination M w)).norm.pow_const 2).aestronglyMeasurable
  exact Eventually.of_forall fun t ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans
      (add_le_add (norm_pairedEtaProjectionHead_le t) (norm_pairedEtaMoebiusContinuumCombination_le M hw t))) 2

/-- The full original-grid-to-continuum critical square error is genuinely integrable. -/
theorem integrableOn_pairedEtaMoebiusContinuumGridError (d M : ℕ) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t) *
      ‖pairedEtaMoebiusTrialGridCombination d M w t - pairedEtaMoebiusContinuumCombination M w t‖ ^ 2) (Ioi 0) := by
  apply integrableOn_exp_neg.mul_bdd
    (((measurable_pairedEtaMoebiusTrialGridCombination d M w).sub
      (measurable_pairedEtaMoebiusContinuumCombination M w)).norm.pow_const 2).aestronglyMeasurable
  exact Eventually.of_forall fun t ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans
      (add_le_add (norm_pairedEtaMoebiusTrialGridCombination_le d M hw t)
        (norm_pairedEtaMoebiusContinuumCombination_le M hw t))) 2

/-- At fixed arithmetic data, every diverging grid schedule transports the full critical square against a bounded measurable target to the exact continuum carrier, using domination on the entire positive axis. -/
theorem pairedEtaMoebiusGridSquareIntegral_tendsto_continuum (M : ℕ) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) {f : ℝ → ℂ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ t, ‖f t‖ ≤ B) {D : ℕ → ℕ} (hD : Tendsto D atTop atTop) :
    Tendsto (fun q ↦ ∫ t : ℝ in Ioi 0, Real.exp (-t) *
      ‖f t - pairedEtaMoebiusTrialGridCombination (D q) M w t‖ ^ 2) atTop
      (𝓝 (∫ t : ℝ in Ioi 0, Real.exp (-t) *
        ‖f t - pairedEtaMoebiusContinuumCombination M w t‖ ^ 2)) := by
  apply tendsto_integral_of_dominated_convergence (fun t : ℝ ↦ Real.exp (-t) * (B + 2 * M) ^ 2)
  · intro q
    exact ((Real.measurable_exp.comp measurable_neg).mul
      ((hf.sub (measurable_pairedEtaMoebiusTrialGridCombination (D q) M w)).norm.pow_const 2)).aestronglyMeasurable
  · exact integrableOn_exp_neg.mul_const _
  · intro q
    exact Eventually.of_forall fun t ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans
        (add_le_add (hB t) (norm_pairedEtaMoebiusTrialGridCombination_le (D q) M hw t))) 2
  · exact Eventually.of_forall fun t ↦ tendsto_const_nhds.mul
      ((tendsto_const_nhds.sub ((pairedEtaMoebiusTrialGridCombination_tendsto_continuum M w t).comp hD)).norm.pow 2)

/-- The unchanged full target residual of the original grids converges to the actual continuum target residual at fixed arithmetic cutoff. -/
theorem pairedEtaMoebiusTrialGridResidualEnergy_tendsto_continuum (M : ℕ) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) {D : ℕ → ℕ} (hD : Tendsto D atTop atTop) :
    Tendsto (fun q ↦ pairedEtaMoebiusTrialGridResidualEnergy (D q) M w) atTop
      (𝓝 (pairedEtaMoebiusContinuumResidualEnergy M w)) :=
  pairedEtaMoebiusGridSquareIntegral_tendsto_continuum M hw
    measurable_pairedEtaProjectionHead norm_pairedEtaProjectionHead_le hD

/-- The complete refinement-error integrals converge to the genuine full grid-to-continuum error, rather than just to a finite-window limit. -/
theorem pairedEtaMoebiusTrialRefinementError_tendsto_continuum {d : ℕ} (hd : 0 < d)
    (M : ℕ) {w : ℕ → ℝ} (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    Tendsto (fun q ↦ pairedEtaMoebiusTrialRefinementError d M (q + 1) w) atTop
      (𝓝 (pairedEtaMoebiusContinuumGridError d M w)) :=
  pairedEtaMoebiusGridSquareIntegral_tendsto_continuum M hw
    (measurable_pairedEtaMoebiusTrialGridCombination d M w)
    (norm_pairedEtaMoebiusTrialGridCombination_le d M hw)
    ((tendsto_add_atTop_nat 1).const_mul_atTop' hd)

/-- The entire original-grid-to-continuum critical square error has the same explicit arithmetic rate as finite refinement, with all infinite-time contributions included. -/
theorem pairedEtaMoebiusContinuumGridError_le {d M : ℕ} (hd : 0 < d) (hMd : M ≤ d)
    {w : ℕ → ℝ} (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) (hsmall : 2 * (M : ℝ) / d ≤ 1 / 8) :
    pairedEtaMoebiusContinuumGridError d M w ≤ 32 * (M : ℝ) ^ 2 * Real.sqrt (2 * (M : ℝ) / d) :=
  le_of_tendsto (pairedEtaMoebiusTrialRefinementError_tendsto_continuum hd M hw)
    (Eventually.of_forall fun q ↦ pairedEtaMoebiusTrialRefinementError_le hd hMd (Nat.succ_pos q) hw hsmall)

end

end RiemannGaussian
