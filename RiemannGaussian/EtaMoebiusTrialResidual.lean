import RiemannGaussian.EtaMoebiusTrialPenalty

/-!
# Complete residual accounting for the exact logarithmic Möbius trials

The actual infinite residual tail tends to zero on the specified dyadic
schedule. The original canonical deficit is at most the trial's finite
residual plus `(k+1)^2/2^k`. All coefficient, cutoff, and tail hypotheses
are discharged for this family. Decay of the growing finite residual,
and hence of the canonical deficit, is not proved.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The actual finite continuous residual for the exact Möbius trial coefficients and original eta cutoff. -/
def pairedEtaDyadicMoebiusTrialResidualCutoff (k : ℕ) : ℝ :=
  pairedEtaTranslatedResidualEnergyCutoff (pairedEtaDyadicTranslate k)
    (fun j ↦ (pairedEtaDyadicMoebiusTrialCoefficient k j : ℂ))
    (Real.log (2 * pairedEtaDyadicTranslateCutoff k + 1 : ℝ))

/-- The entire original infinite residual tail, not just its coefficient allowance. -/
def pairedEtaDyadicMoebiusTrialResidualTail (k : ℕ) : ℝ :=
  ∫ t : ℝ in Ioi (Real.log (2 * pairedEtaDyadicTranslateCutoff k + 1 : ℝ)),
    Real.exp (-t) * ‖pairedEtaTranslatedResidual (pairedEtaDyadicTranslate k)
      (fun j ↦ (pairedEtaDyadicMoebiusTrialCoefficient k j : ℂ)) t‖ ^ 2

/-- Every prescribed original eta cutoff contains the complete compact target. -/
theorem pairedEtaDyadicTranslate_logCutoff_ge_log_two (k : ℕ) :
    Real.log 2 ≤ Real.log (2 * pairedEtaDyadicTranslateCutoff k + 1 : ℝ) := by
  apply Real.log_le_log (by norm_num)
  have h : (1 : ℝ) ≤ pairedEtaDyadicTranslateCutoff k := by
    exact_mod_cast pairedEtaDyadicTranslateCutoff_one_le k
  linarith

/-- The full exact trial objective is its actual finite residual plus the unchanged diagonal coefficient penalty. -/
theorem pairedEtaDyadicMoebiusTrial_objective_eq_cutoff_add_penalty (k : ℕ) :
    pairedEtaTranslateRidgeObjective (pairedEtaDyadicTranslateCutoff k) (pairedEtaDyadicTranslate k)
      (pairedEtaDyadicMoebiusTrialCoefficient k) =
        pairedEtaDyadicMoebiusTrialResidualCutoff k + pairedEtaDyadicMoebiusTrialPenalty k := by
  let N := pairedEtaDyadicTranslateCutoff k
  let a := pairedEtaDyadicTranslate k
  let c := pairedEtaDyadicMoebiusTrialCoefficient k
  change pairedEtaTranslateRidgeObjective N a c =
    pairedEtaTranslatedResidualEnergyCutoff a (fun j ↦ (c j : ℂ)) (Real.log (2 * N + 1 : ℝ)) +
      pairedEtaTranslateRegularization (pairedEtaDyadicTranslateDimension k) N * ∑ j, c j ^ 2
  rw [pairedEtaTranslatedResidualEnergyCutoff_eq_finiteForm (pairedEtaDyadicTranslate_nonneg k)
    (fun j ↦ (c j : ℂ)) (pairedEtaDyadicTranslate_logCutoff_ge_log_two k) le_rfl]
  have hB := pairedEtaTranslatedFiniteResidualBudget_eq_realMatrix N a c
  unfold pairedEtaTranslatedFiniteResidualBudget at hB
  simp only [Complex.norm_real, Real.norm_eq_abs] at hB
  rw [pairedEtaTranslateRidgeObjective, pairedEtaRegularizedTranslateGram_energy]
  linarith

/-- The original exact canonical family is bounded by the actual balanced Möbius trial, with the whole regularization cost retained. -/
theorem pairedEtaDyadicTranslateDeficit_le_moebius_cutoff_add_penalty (k : ℕ) :
    pairedEtaDyadicTranslateDeficit k ≤
      pairedEtaDyadicMoebiusTrialResidualCutoff k + pairedEtaDyadicMoebiusTrialPenalty k := by
  have h := pairedEtaCanonicalTranslateBudget_le_trial (pairedEtaDyadicTranslateCutoff k)
    (pairedEtaDyadicTranslate_nonneg k) (pairedEtaDyadicMoebiusTrialCoefficient k)
  rw [pairedEtaDyadicMoebiusTrial_objective_eq_cutoff_add_penalty] at h
  exact h

/-- The canonical deficit has an explicit arithmetic residual bound with a proved vanishing coefficient allowance. -/
theorem pairedEtaDyadicTranslateDeficit_le_moebius_cutoff_add_allowance (k : ℕ) :
    pairedEtaDyadicTranslateDeficit k ≤
      pairedEtaDyadicMoebiusTrialResidualCutoff k + pairedEtaDyadicMoebiusTrialAllowance k :=
  (pairedEtaDyadicTranslateDeficit_le_moebius_cutoff_add_penalty k).trans
    (add_le_add le_rfl (pairedEtaDyadicMoebiusTrialPenalty_le k))

/-- The actual complete omitted residual tail is nonnegative at every stage. -/
theorem pairedEtaDyadicMoebiusTrialResidualTail_nonneg (k : ℕ) :
    0 ≤ pairedEtaDyadicMoebiusTrialResidualTail k :=
  integral_nonneg (fun _ ↦ by positivity)

/-- The proved diagonal coefficient cost controls the entire actual infinite residual tail. -/
theorem pairedEtaDyadicMoebiusTrialResidualTail_le_penalty (k : ℕ) :
    pairedEtaDyadicMoebiusTrialResidualTail k ≤ pairedEtaDyadicMoebiusTrialPenalty k := by
  have h := integral_Ioi_pairedEtaTranslatedResidual_weighted_sq_le (pairedEtaDyadicTranslate k)
    (fun j ↦ (pairedEtaDyadicMoebiusTrialCoefficient k j : ℂ)) (pairedEtaDyadicTranslate_logCutoff_ge_log_two k)
  rw [Real.exp_neg, Real.exp_log (by positivity :
    0 < (2 * pairedEtaDyadicTranslateCutoff k + 1 : ℝ))] at h
  have h' : pairedEtaDyadicMoebiusTrialResidualTail k ≤
      (∑ j, |pairedEtaDyadicMoebiusTrialCoefficient k j|) ^ 2 /
        (2 * pairedEtaDyadicTranslateCutoff k + 1 : ℝ) := by
    simpa only [pairedEtaDyadicMoebiusTrialResidualTail, Complex.norm_real, Real.norm_eq_abs,
      div_eq_mul_inv, mul_comm] using h
  exact h'.trans (pairedEtaTranslate_tail_le_regularization (pairedEtaDyadicTranslateCutoff k)
    (pairedEtaDyadicMoebiusTrialCoefficient k))

/-- The actual infinite tail of the exact balanced logarithmic Möbius trial tends to zero; all coefficient and scale estimates are discharged. -/
theorem pairedEtaDyadicMoebiusTrialResidualTail_tendsto_zero :
    Tendsto pairedEtaDyadicMoebiusTrialResidualTail atTop (𝓝 0) :=
  squeeze_zero pairedEtaDyadicMoebiusTrialResidualTail_nonneg pairedEtaDyadicMoebiusTrialResidualTail_le_penalty
    pairedEtaDyadicMoebiusTrialPenalty_tendsto_zero

/-- The original full continuous trial energy retains its exact finite-cutoff plus infinite-tail decomposition. -/
theorem pairedEtaDyadicMoebiusTrialResidualEnergy_eq_cutoff_add_tail (k : ℕ) :
    pairedEtaTranslatedResidualEnergy (pairedEtaDyadicTranslate k)
      (fun j ↦ (pairedEtaDyadicMoebiusTrialCoefficient k j : ℂ)) =
        pairedEtaDyadicMoebiusTrialResidualCutoff k + pairedEtaDyadicMoebiusTrialResidualTail k :=
  pairedEtaTranslatedResidualEnergy_eq_cutoff_add_tail _ _
    ((Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans (pairedEtaDyadicTranslate_logCutoff_ge_log_two k))

/-- The whole continuous trial residual is controlled by its finite part and the same explicit vanishing allowance. -/
theorem pairedEtaDyadicMoebiusTrialResidualEnergy_le_cutoff_add_allowance (k : ℕ) :
    pairedEtaTranslatedResidualEnergy (pairedEtaDyadicTranslate k)
      (fun j ↦ (pairedEtaDyadicMoebiusTrialCoefficient k j : ℂ)) ≤
        pairedEtaDyadicMoebiusTrialResidualCutoff k + pairedEtaDyadicMoebiusTrialAllowance k := by
  rw [pairedEtaDyadicMoebiusTrialResidualEnergy_eq_cutoff_add_tail]
  exact add_le_add le_rfl ((pairedEtaDyadicMoebiusTrialResidualTail_le_penalty k).trans
    (pairedEtaDyadicMoebiusTrialPenalty_le k))

/-- Both reflected actual zero coordinates inherit the arithmetic trial bound, while the finite residual remains explicit. -/
theorem pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_moebius_cutoff_add_allowance
    (rho : NontrivialZetaZero) (k : ℕ) :
    pairedEtaCurrentHorizontalDisplacement rho * pairedEtaProjectionHeadZeroWeight rho ≤
      pairedEtaDyadicMoebiusTrialResidualCutoff k + pairedEtaDyadicMoebiusTrialAllowance k :=
  (pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_dyadicDeficit rho k).trans
    (pairedEtaDyadicTranslateDeficit_le_moebius_cutoff_add_allowance k)

end

end RiemannGaussian
