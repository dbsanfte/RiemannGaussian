import RiemannGaussian.EtaMoebiusTrialResidualRefinement
import RiemannGaussian.EtaMoebiusTrialRefinementLimit
import RiemannGaussian.EtaMoebiusTrialResidual

/-!
# Canonical eta deficit bounds from arbitrarily refined arithmetic candidates

All grid-refinement and coefficient allowances tend to zero along the
original dyadic schedule. The canonical deficit is bounded by the complete
residual of every finer physical grid carrying the same arithmetic cutoff
and weights, plus one explicit vanishing allowance. The remaining target
is decay of that actual arithmetic residual, not a numerical grid limit.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The whole target residual of a finer physical grid with the original stage's arithmetic cutoff and exact logarithmic weights. -/
def pairedEtaDyadicMoebiusRefinedResidual (k q : ℕ) : ℝ :=
  pairedEtaMoebiusTrialGridResidualEnergy (pairedEtaDyadicTranslateDimension k * (q + 1)) (k + 1)
    (pairedEtaMoebiusTrialLogWeight (k + 1))

/-- The complete residual-energy change allowance, uniform over every positive integer refinement factor. -/
def pairedEtaDyadicMoebiusGridResidualAllowance (k : ℕ) : ℝ :=
  16 / (k + 1 : ℝ) + 64 * Real.sqrt (2 * (k + 1 : ℝ) ^ 11 / (2 : ℝ) ^ k)

/-- The combined grid and coefficient allowance used in the unchanged canonical-deficit comparison. -/
def pairedEtaDyadicMoebiusRefinedAllowance (k : ℕ) : ℝ :=
  pairedEtaDyadicMoebiusGridResidualAllowance k + pairedEtaDyadicMoebiusTrialAllowance k

/-- The generic physical-grid energy is exactly the original full dyadic Möbius residual. -/
theorem pairedEtaMoebiusTrialGridResidualEnergy_eq_dyadic (k : ℕ) :
    pairedEtaMoebiusTrialGridResidualEnergy (pairedEtaDyadicTranslateDimension k) (k + 1)
      (pairedEtaMoebiusTrialLogWeight (k + 1)) =
        pairedEtaTranslatedResidualEnergy (pairedEtaDyadicTranslate k)
          (fun j ↦ (pairedEtaDyadicMoebiusTrialCoefficient k j : ℂ)) := by
  change (∫ t : ℝ in Ioi 0, Real.exp (-t) *
    ‖pairedEtaProjectionHead t - pairedEtaMoebiusTrialGridCombination
      (pairedEtaDyadicTranslateDimension k) (k + 1) (pairedEtaMoebiusTrialLogWeight (k + 1)) t‖ ^ 2) = _
  simp_rw [pairedEtaMoebiusTrialGridCombination_eq_dyadic]
  rfl

/-- Every finer arithmetic grid has almost the same full target residual, with an explicit allowance and stage threshold. -/
theorem abs_pairedEtaDyadicMoebiusResidual_sub_refined_le {k : ℕ} (hk : 7 ≤ k) (q : ℕ) :
    |pairedEtaTranslatedResidualEnergy (pairedEtaDyadicTranslate k)
      (fun j ↦ (pairedEtaDyadicMoebiusTrialCoefficient k j : ℂ)) -
        pairedEtaDyadicMoebiusRefinedResidual k q| ≤ pairedEtaDyadicMoebiusGridResidualAllowance k := by
  have h := abs_pairedEtaMoebiusTrialGridResidualEnergy_sub_le_explicit
    (pairedEtaDyadicTranslateDimension_pos k) (by omega : 1 ≤ k + 1)
    (pairedEtaDyadicMoebiusTrial_cutoff_le_dimension k) (Nat.succ_pos q)
    (fun _ hn ↦ abs_pairedEtaMoebiusTrialLogWeight_le hn)
    (by simpa only [Nat.cast_add, Nat.cast_one] using pairedEtaDyadicMoebiusTrialGrid_small hk)
  rw [pairedEtaMoebiusTrialGridResidualEnergy_eq_dyadic] at h
  simpa only [pairedEtaDyadicMoebiusRefinedResidual, pairedEtaDyadicMoebiusGridResidualAllowance,
    pairedEtaDyadicTranslateDimension, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] using h

/-- The entire full-residual refinement allowance tends to zero along the original growing arithmetic family. -/
theorem pairedEtaDyadicMoebiusGridResidualAllowance_tendsto_zero :
    Tendsto pairedEtaDyadicMoebiusGridResidualAllowance atTop (𝓝 0) := by
  have hnat : Tendsto (fun k : ℕ ↦ (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp (hnat.comp (tendsto_add_atTop_nat 1))
  have hp := ((tendsto_pow_const_div_const_pow_of_one_lt 11 (by norm_num : (1 : ℝ) < 2)).comp
    (tendsto_add_atTop_nat 1)).const_mul (4 : ℝ)
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, mul_zero] at hp
  have hpoly : Tendsto (fun k : ℕ ↦ 2 * (k + 1 : ℝ) ^ 11 / (2 : ℝ) ^ k) atTop (𝓝 0) := by
    convert hp using 1
    ext k
    rw [pow_succ]
    ring
  have hroot := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hpoly
  have h := (hinv.const_mul (16 : ℝ)).add (hroot.const_mul (64 : ℝ))
  change Tendsto (fun k : ℕ ↦ 16 / (k + 1 : ℝ) +
    64 * Real.sqrt (2 * (k + 1 : ℝ) ^ 11 / (2 : ℝ) ^ k)) atTop (𝓝 0)
  simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, div_eq_mul_inv,
    mul_zero, Real.sqrt_zero, zero_add] using h

/-- Every refinement schedule preserves the asymptotic full residual energy of the original arithmetic candidate. -/
theorem pairedEtaDyadicMoebiusResidual_sub_refined_tendsto_zero (q : ℕ → ℕ) :
    Tendsto (fun k ↦ |pairedEtaTranslatedResidualEnergy (pairedEtaDyadicTranslate k)
      (fun j ↦ (pairedEtaDyadicMoebiusTrialCoefficient k j : ℂ)) -
        pairedEtaDyadicMoebiusRefinedResidual k (q k)|) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _)
    _ pairedEtaDyadicMoebiusGridResidualAllowance_tendsto_zero
  filter_upwards [eventually_ge_atTop 7] with k hk
  exact abs_pairedEtaDyadicMoebiusResidual_sub_refined_le hk (q k)

/-- Both the full grid-refinement cost and the original coefficient allowance vanish together. -/
theorem pairedEtaDyadicMoebiusRefinedAllowance_tendsto_zero :
    Tendsto pairedEtaDyadicMoebiusRefinedAllowance atTop (𝓝 0) := by
  change Tendsto (fun k ↦ pairedEtaDyadicMoebiusGridResidualAllowance k + pairedEtaDyadicMoebiusTrialAllowance k)
    atTop (𝓝 0)
  simpa only [add_zero] using
    pairedEtaDyadicMoebiusGridResidualAllowance_tendsto_zero.add pairedEtaDyadicMoebiusTrialAllowance_tendsto_zero

/-- The unchanged canonical deficit is controlled by every finer actual arithmetic residual with all added costs explicit and vanishing. -/
theorem pairedEtaDyadicTranslateDeficit_le_refined_moebius {k : ℕ} (hk : 7 ≤ k) (q : ℕ) :
    pairedEtaDyadicTranslateDeficit k ≤
      pairedEtaDyadicMoebiusRefinedResidual k q + pairedEtaDyadicMoebiusRefinedAllowance k := by
  have hcut : pairedEtaDyadicMoebiusTrialResidualCutoff k ≤
      pairedEtaTranslatedResidualEnergy (pairedEtaDyadicTranslate k)
        (fun j ↦ (pairedEtaDyadicMoebiusTrialCoefficient k j : ℂ)) := by
    rw [pairedEtaDyadicMoebiusTrialResidualEnergy_eq_cutoff_add_tail]
    linarith [pairedEtaDyadicMoebiusTrialResidualTail_nonneg k]
  have hfull := (abs_le.mp (abs_pairedEtaDyadicMoebiusResidual_sub_refined_le hk q)).2
  have hD := pairedEtaDyadicTranslateDeficit_le_moebius_cutoff_add_allowance k
  unfold pairedEtaDyadicMoebiusRefinedAllowance
  linarith

/-- Every actual zero coordinate inherits the full refined arithmetic residual bound and the same proved vanishing allowance. -/
theorem pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_refined_moebius
    (rho : NontrivialZetaZero) {k : ℕ} (hk : 7 ≤ k) (q : ℕ) :
    pairedEtaCurrentHorizontalDisplacement rho * pairedEtaProjectionHeadZeroWeight rho ≤
      pairedEtaDyadicMoebiusRefinedResidual k q + pairedEtaDyadicMoebiusRefinedAllowance k :=
  (pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_dyadicDeficit rho k).trans
    (pairedEtaDyadicTranslateDeficit_le_refined_moebius hk q)

end

end RiemannGaussian
