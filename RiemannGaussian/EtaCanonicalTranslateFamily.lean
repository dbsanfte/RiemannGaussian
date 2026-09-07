import RiemannGaussian.EtaCanonicalTranslateBound
import RiemannGaussian.EtaFourTranslateBound

/-!
# A completely specified growing family of eta coefficients

At stage `k` the physical scales are `(j+1)/2^k`, including scale one,
and the original eta cutoff is `4*(2^k)^2`. The actual regularized Gram
inverse defines every coefficient exactly. The complete residual, actual
zero displacement, and both original current branches have bounds in the
same explicit resolvent deficit. Its convergence to zero is not proved.
-/

open Complex Matrix
open scoped Matrix

namespace RiemannGaussian

noncomputable section

/-- The number of original translates at the dyadic search stage. -/
def pairedEtaDyadicTranslateDimension (k : ℕ) : ℕ := 2 ^ k

/-- The original eta arithmetic cutoff chosen for the entire coefficient family. -/
def pairedEtaDyadicTranslateCutoff (k : ℕ) : ℕ := 4 * pairedEtaDyadicTranslateDimension k ^ 2

/-- The nested uniform physical scale grid, expressed as the original nonnegative logarithmic translates. -/
def pairedEtaDyadicTranslate (k : ℕ) (j : Fin (pairedEtaDyadicTranslateDimension k)) : ℝ :=
  -Real.log ((j.1 + 1 : ℝ) / (pairedEtaDyadicTranslateDimension k : ℝ))

/-- Every dyadic family is nonempty. -/
theorem pairedEtaDyadicTranslateDimension_pos (k : ℕ) : 0 < pairedEtaDyadicTranslateDimension k := by
  unfold pairedEtaDyadicTranslateDimension
  positivity

/-- Every dyadic stage includes the compact target in its actual eta arithmetic cutoff. -/
theorem pairedEtaDyadicTranslateCutoff_one_le (k : ℕ) : 1 ≤ pairedEtaDyadicTranslateCutoff k := by
  have hd := pairedEtaDyadicTranslateDimension_pos k
  unfold pairedEtaDyadicTranslateCutoff
  have : 0 < 4 * pairedEtaDyadicTranslateDimension k ^ 2 := by positivity
  omega

/-- Every scale in the exact dyadic family satisfies the full positive-time translate hypothesis. -/
theorem pairedEtaDyadicTranslate_nonneg (k : ℕ) (j : Fin (pairedEtaDyadicTranslateDimension k)) :
    0 ≤ pairedEtaDyadicTranslate k j := by
  have hd : 0 < (pairedEtaDyadicTranslateDimension k : ℝ) := by
    exact_mod_cast pairedEtaDyadicTranslateDimension_pos k
  have hj : (j.1 + 1 : ℝ) ≤ pairedEtaDyadicTranslateDimension k := by
    exact_mod_cast Nat.succ_le_of_lt j.isLt
  apply neg_nonneg.mpr
  apply Real.log_nonpos (by positivity)
  exact (div_le_one hd).mpr hj

/-- Every coefficient in the growing family is defined by the same exact regularized Gram inverse. -/
def pairedEtaDyadicTranslateCoefficient (k : ℕ) : Fin (pairedEtaDyadicTranslateDimension k) → ℝ :=
  pairedEtaCanonicalTranslateCoefficient (pairedEtaDyadicTranslateCutoff k) (pairedEtaDyadicTranslate k)

/-- The exact resolvent deficit whose decay is the next mathematical target for this family. -/
def pairedEtaDyadicTranslateDeficit (k : ℕ) : ℝ :=
  pairedEtaCanonicalTranslateBudget (pairedEtaDyadicTranslateCutoff k) (pairedEtaDyadicTranslate k)

/-- Every stage has a complete residual allowance between zero and one. -/
theorem pairedEtaDyadicTranslateDeficit_bounds (k : ℕ) :
    0 ≤ pairedEtaDyadicTranslateDeficit k ∧ pairedEtaDyadicTranslateDeficit k ≤ 1 :=
  ⟨pairedEtaCanonicalTranslateBudget_nonneg (pairedEtaDyadicTranslateCutoff_one_le k) (pairedEtaDyadicTranslate_nonneg k),
    pairedEtaCanonicalTranslateBudget_le_one _ (pairedEtaDyadicTranslate_nonneg k)⟩

/-- The entire continuous residual of the specified mathematical coefficient family is bounded at every stage, with the full coefficient tail included. -/
theorem pairedEtaDyadicTranslate_residualEnergy_le (k : ℕ) :
    pairedEtaTranslatedResidualEnergy (pairedEtaDyadicTranslate k)
      (fun j ↦ (pairedEtaDyadicTranslateCoefficient k j : ℂ)) ≤ pairedEtaDyadicTranslateDeficit k :=
  pairedEtaCanonicalTranslate_residualEnergy_le (pairedEtaDyadicTranslateCutoff_one_le k) (pairedEtaDyadicTranslate_nonneg k)

/-- The four-point dyadic grid is exactly the grid of the rational coefficient check. -/
theorem pairedEtaDyadicTranslate_two_eq_four :
    pairedEtaDyadicTranslate 2 = pairedEtaFourProjectionTranslate := by
  change (fun j : Fin 4 ↦ -Real.log ((j.1 + 1 : ℝ) / 4)) = pairedEtaFourProjectionTranslate
  funext j
  fin_cases j <;> norm_num [pairedEtaFourProjectionTranslate, pairedEtaRationalTranslate, pairedEtaFourProjectionScale]

/-- The exact growing family has a proved deficit below one quarter at its four-point stage, by comparison with the explicit signed trial coefficients. -/
theorem pairedEtaDyadicTranslateDeficit_two_lt_one_quarter : pairedEtaDyadicTranslateDeficit 2 < 1 / 4 := by
  change pairedEtaCanonicalTranslateBudget 64 (pairedEtaDyadicTranslate 2) < 1 / 4
  rw [pairedEtaDyadicTranslate_two_eq_four]
  change pairedEtaCanonicalTranslateBudget (d := 4) 64 pairedEtaFourProjectionTranslate < 1 / 4
  have htrial := pairedEtaCanonicalTranslateBudget_le_trial 64 pairedEtaFourProjectionTranslate_nonneg
    (fun j ↦ (pairedEtaFourProjectionCoefficient j : ℝ))
  have heq : pairedEtaTranslateRidgeObjective 64 pairedEtaFourProjectionTranslate
      (fun j ↦ (pairedEtaFourProjectionCoefficient j : ℝ)) =
      pairedEtaTranslatedFiniteResidualBudget 64 pairedEtaFourProjectionTranslate
        pairedEtaFourProjectionComplexCoefficient + 5 / 258 := by
    change pairedEtaTranslateRidgeObjective 64 pairedEtaFourProjectionTranslate
      (fun j ↦ (pairedEtaFourProjectionCoefficient j : ℝ)) =
      pairedEtaTranslatedFiniteResidualBudget 64 pairedEtaFourProjectionTranslate
        (fun j ↦ ((pairedEtaFourProjectionCoefficient j : ℝ) : ℂ)) + 5 / 258
    rw [pairedEtaTranslatedFiniteResidualBudget_eq_realMatrix, pairedEtaTranslateRidgeObjective,
      pairedEtaRegularizedTranslateGram_energy]
    norm_num [pairedEtaTranslateRegularization, Fin.sum_univ_succ, pairedEtaFourProjectionCoefficient]
    ring
  rw [heq] at htrial
  linarith [pairedEtaFourProjection_finiteBudget_lt_one_fifth]

/-- The same exact family bounds both reflected actual zero coordinates. -/
theorem pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_dyadicDeficit (rho : NontrivialZetaZero) (k : ℕ) :
    pairedEtaCurrentHorizontalDisplacement rho * pairedEtaProjectionHeadZeroWeight rho ≤
      pairedEtaDyadicTranslateDeficit k :=
  pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_canonicalBudget rho
    (pairedEtaDyadicTranslateCutoff_one_le k) (pairedEtaDyadicTranslate_nonneg k)

/-- The coefficient law gives an explicit current exponent while preserving all preceding phase and prime bounds. -/
def etaDyadicTranslateCurrentExponent (rho : NontrivialZetaZero) (k : ℕ) : ℝ :=
  min (etaFinitePhaseCurrentExponent (analyticZetaZeroMultiplicity rho) (pairedEtaDyadicTranslateCutoff k) rho.1.im)
    (pairedEtaDyadicTranslateDeficit k / pairedEtaProjectionHeadZeroWeight rho)

/-- Every exponent supplied by the exact dyadic family is nonnegative and below one. -/
theorem etaDyadicTranslateCurrentExponent_bounds (rho : NontrivialZetaZero) (k : ℕ) :
    0 ≤ etaDyadicTranslateCurrentExponent rho k ∧ etaDyadicTranslateCurrentExponent rho k < 1 := by
  have hold := etaFinitePhaseCurrentExponent_bounds rho (pairedEtaDyadicTranslateCutoff k)
  exact ⟨le_min hold.1 (div_nonneg (pairedEtaDyadicTranslateDeficit_bounds k).1 (pairedEtaProjectionHeadZeroWeight_pos rho).le),
    (min_le_left _ _).trans_lt hold.2⟩

/-- The actual horizontal displacement is bounded by the exact dyadic-family exponent. -/
theorem pairedEtaCurrentHorizontalDisplacement_le_dyadicTranslate (rho : NontrivialZetaZero) (k : ℕ) :
    pairedEtaCurrentHorizontalDisplacement rho ≤ etaDyadicTranslateCurrentExponent rho k :=
  le_min (pairedEtaCurrentHorizontalDisplacement_le_finitePhase rho (pairedEtaDyadicTranslateCutoff k))
    ((le_div_iff₀ (pairedEtaProjectionHeadZeroWeight_pos rho)).mpr
      (pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_dyadicDeficit rho k))

/-- The exact growing coefficient family bounds both multiplicity branches of the original weighted current at every physical cutoff. -/
theorem pairedEtaLeadingCurrent_firstMoment_le_dyadicTranslate (rho : NontrivialZetaZero) (k K : ℕ) :
    (∑ n ∈ Finset.range K, (2 * n + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho n|) ≤
      pairedEtaCurrentReturnGrowthConstant rho * (K + 1 : ℝ) ^ etaDyadicTranslateCurrentExponent rho k :=
  (pairedEtaLeadingCurrent_firstMoment_le_growthConstant rho K).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      (by linarith [Nat.cast_nonneg (α := ℝ) K]) (pairedEtaCurrentHorizontalDisplacement_le_dyadicTranslate rho k))
      (pairedEtaCurrentReturnGrowthConstant_nonneg rho))

/-- The unchanged linear-width Gaussian return has the same exponent from the exact coefficient law. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_le_dyadicTranslate (rho : NontrivialZetaZero) (k K : ℕ) :
    (∑ n ∈ Finset.range K, (2 * n + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho n‖) ≤
      pairedEtaCurrentReturnGrowthConstant rho * (K + 1 : ℝ) ^ etaDyadicTranslateCurrentExponent rho k :=
  (pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_growth_le rho K).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      (by linarith [Nat.cast_nonneg (α := ℝ) K]) (pairedEtaCurrentHorizontalDisplacement_le_dyadicTranslate rho k))
      (pairedEtaCurrentReturnGrowthConstant_nonneg rho))

/-- The full signed inverse energy inherits the exact family exponent and its existing summable transport budget. -/
theorem pairedEtaCurrentFullInverseEnergy_firstMoment_le_dyadicTranslate (rho : NontrivialZetaZero) (k K : ℕ) :
    (∑ n ∈ Finset.range K, (2 * n + 1 : ℝ) * |pairedEtaCurrentFullInverseEnergy rho n|) ≤
      (pairedEtaCurrentReturnGrowthConstant rho + ∑' n : ℕ, pairedEtaCurrentZeroEnergyErrorEnvelope rho n) *
        (K + 1 : ℝ) ^ etaDyadicTranslateCurrentExponent rho k := by
  have hstab := (abs_le.mp (pairedEtaLeadingCurrent_fullInverseEnergy_firstMoment_stability rho K)).1
  have hcurrent := pairedEtaLeadingCurrent_firstMoment_le_dyadicTranslate rho k K
  have hB : 0 ≤ ∑' n : ℕ, pairedEtaCurrentZeroEnergyErrorEnvelope rho n :=
    tsum_nonneg (pairedEtaCurrentZeroEnergyErrorEnvelope_nonneg rho)
  have hpow : 1 ≤ (K + 1 : ℝ) ^ etaDyadicTranslateCurrentExponent rho k :=
    Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) K]) (etaDyadicTranslateCurrentExponent_bounds rho k).1
  nlinarith [mul_le_mul_of_nonneg_left hpow hB]

end

end RiemannGaussian
