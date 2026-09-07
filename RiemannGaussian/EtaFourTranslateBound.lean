import RiemannGaussian.EtaFourTranslateProjection

/-!
# A proved four-coefficient bound for the complete eta residual and current

The four explicit rational scales and signed coefficients have a complete
continuous residual energy below `1/5`. This includes every finite Gram
cross term and the whole infinite tail. The same rational constant bounds
actual zero displacement after the existing positive target normalization,
and gives an explicit power bound for both original current branches.
No vanishing coefficient family or new numerical zero strip is asserted.
-/

open Complex Set

namespace RiemannGaussian

noncomputable section

/-- The four original nonnegative logarithmic translates. -/
def pairedEtaFourProjectionTranslate (j : Fin 4) : ℝ :=
  pairedEtaRationalTranslate (pairedEtaFourProjectionScale j)

/-- The same four rational coefficients on the original complex carrier. -/
def pairedEtaFourProjectionComplexCoefficient (j : Fin 4) : ℂ :=
  (pairedEtaFourProjectionCoefficient j : ℂ)

/-- Every one of the selected translates satisfies the full positive-time support requirement. -/
theorem pairedEtaFourProjectionTranslate_nonneg (j : Fin 4) :
    0 ≤ pairedEtaFourProjectionTranslate j :=
  pairedEtaRationalTranslate_nonneg (pairedEtaFourProjectionScale_bounds j).1
    (pairedEtaFourProjectionScale_bounds j).2

/-- The four signed target pairings retain exactly one half of the logarithm of six. -/
theorem pairedEtaFourProjection_target_pairing :
    (∑ j : Fin 4, (pairedEtaFourProjectionCoefficient j : ℝ) *
      max 0 (Real.log (2 * (pairedEtaFourProjectionScale j : ℝ)))) =
        (Real.log 2 + Real.log 3) / 2 := by
  have hhalf : Real.log (1 / 2 : ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  have hthree : 0 ≤ Real.log (3 / 2 : ℝ) := Real.log_nonneg (by norm_num)
  have htwo : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  norm_num [Fin.sum_univ_succ, pairedEtaFourProjectionCoefficient, pairedEtaFourProjectionScale]
  rw [max_eq_left hhalf, max_eq_right hthree, max_eq_right htwo,
    Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- The original full finite Gram-plus-tail budget is strictly below one fifth for the explicit four coefficients. -/
theorem pairedEtaFourProjection_finiteBudget_lt_one_fifth :
    pairedEtaTranslatedFiniteResidualBudget 64 pairedEtaFourProjectionTranslate
      pairedEtaFourProjectionComplexCoefficient < 1 / 5 := by
  unfold pairedEtaFourProjectionTranslate pairedEtaFourProjectionComplexCoefficient
  rw [pairedEtaTranslatedFiniteResidualBudget_eq_rational pairedEtaFourProjectionScale
      pairedEtaFourProjectionCoefficient (fun j ↦ (pairedEtaFourProjectionScale_bounds j).1),
    pairedEtaFourProjection_target_pairing]
  have hq : (pairedEtaRationalQuadraticBudget 64 pairedEtaFourProjectionScale
      pairedEtaFourProjectionCoefficient : ℝ) < 99 / 100 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr pairedEtaFourProjection_rationalQuadraticBudget_lt
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

/-- The complete continuous residual, including its infinite tail, is strictly below one fifth. -/
theorem pairedEtaFourProjection_residualEnergy_lt_one_fifth :
    pairedEtaTranslatedResidualEnergy pairedEtaFourProjectionTranslate
      pairedEtaFourProjectionComplexCoefficient < 1 / 5 :=
  (pairedEtaTranslatedResidualEnergy_le_finiteBudget (by norm_num : 1 ≤ (64 : ℕ))
    pairedEtaFourProjectionTranslate_nonneg pairedEtaFourProjectionComplexCoefficient).trans_lt
    pairedEtaFourProjection_finiteBudget_lt_one_fifth

/-- Four explicit coefficients give a strict absolute-coordinate constraint on every actual zero and its partner. -/
theorem pairedEtaCurrentHorizontalDisplacement_mul_headWeight_lt_one_fifth (rho : NontrivialZetaZero) :
    pairedEtaCurrentHorizontalDisplacement rho * pairedEtaProjectionHeadZeroWeight rho < 1 / 5 :=
  (pairedEtaCurrentHorizontalDisplacement_mul_headWeight_le_finiteBudget rho
    (by norm_num : 1 ≤ (64 : ℕ)) pairedEtaFourProjectionTranslate_nonneg
    pairedEtaFourProjectionComplexCoefficient).trans_lt pairedEtaFourProjection_finiteBudget_lt_one_fifth

/-- Dividing by the proved positive target weight preserves the explicit four-coefficient displacement bound. -/
theorem pairedEtaCurrentHorizontalDisplacement_lt_fourProjection (rho : NontrivialZetaZero) :
    pairedEtaCurrentHorizontalDisplacement rho < 1 / (5 * pairedEtaProjectionHeadZeroWeight rho) := by
  have h := (lt_div_iff₀ (pairedEtaProjectionHeadZeroWeight_pos rho)).mpr
    (pairedEtaCurrentHorizontalDisplacement_mul_headWeight_lt_one_fifth rho)
  simpa only [div_div] using h

/-- The explicit four-coefficient exponent preserves the earlier finite phase and prime margins. -/
def etaFourProjectionCurrentExponent (rho : NontrivialZetaZero) : ℝ :=
  min (etaFinitePhaseCurrentExponent (analyticZetaZeroMultiplicity rho) 64 rho.1.im)
    (1 / (5 * pairedEtaProjectionHeadZeroWeight rho))

/-- The new explicit exponent is nonnegative and below one at every actual zero. -/
theorem etaFourProjectionCurrentExponent_bounds (rho : NontrivialZetaZero) :
    0 ≤ etaFourProjectionCurrentExponent rho ∧ etaFourProjectionCurrentExponent rho < 1 := by
  have hold := etaFinitePhaseCurrentExponent_bounds rho 64
  have hw := pairedEtaProjectionHeadZeroWeight_pos rho
  exact ⟨le_min hold.1 (by positivity), (min_le_left _ _).trans_lt hold.2⟩

/-- The original displacement is controlled by the explicit four-coefficient exponent. -/
theorem pairedEtaCurrentHorizontalDisplacement_le_fourProjection (rho : NontrivialZetaZero) :
    pairedEtaCurrentHorizontalDisplacement rho ≤ etaFourProjectionCurrentExponent rho :=
  le_min (pairedEtaCurrentHorizontalDisplacement_le_finitePhase rho 64)
    (pairedEtaCurrentHorizontalDisplacement_lt_fourProjection rho).le

/-- The four explicit coefficients bound the odd-weighted absolute current in both original multiplicity branches at every cutoff. -/
theorem pairedEtaLeadingCurrent_firstMoment_le_fourProjection (rho : NontrivialZetaZero) (K : ℕ) :
    (∑ n ∈ Finset.range K, (2 * n + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho n|) ≤
      pairedEtaCurrentReturnGrowthConstant rho * (K + 1 : ℝ) ^ etaFourProjectionCurrentExponent rho :=
  (pairedEtaLeadingCurrent_firstMoment_le_growthConstant rho K).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      (by linarith [Nat.cast_nonneg (α := ℝ) K])
      (pairedEtaCurrentHorizontalDisplacement_le_fourProjection rho))
      (pairedEtaCurrentReturnGrowthConstant_nonneg rho))

/-- The actual linear-width Gaussian return inherits the explicit four-coefficient exponent and its unchanged constant. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_le_fourProjection (rho : NontrivialZetaZero) (K : ℕ) :
    (∑ n ∈ Finset.range K, (2 * n + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho n‖) ≤
      pairedEtaCurrentReturnGrowthConstant rho * (K + 1 : ℝ) ^ etaFourProjectionCurrentExponent rho :=
  (pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_growth_le rho K).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      (by linarith [Nat.cast_nonneg (α := ℝ) K])
      (pairedEtaCurrentHorizontalDisplacement_le_fourProjection rho))
      (pairedEtaCurrentReturnGrowthConstant_nonneg rho))

/-- The full signed inverse energy retains its proved summable error budget with the same explicit current exponent. -/
theorem pairedEtaCurrentFullInverseEnergy_firstMoment_le_fourProjection (rho : NontrivialZetaZero) (K : ℕ) :
    (∑ n ∈ Finset.range K, (2 * n + 1 : ℝ) * |pairedEtaCurrentFullInverseEnergy rho n|) ≤
      (pairedEtaCurrentReturnGrowthConstant rho + ∑' n : ℕ, pairedEtaCurrentZeroEnergyErrorEnvelope rho n) *
        (K + 1 : ℝ) ^ etaFourProjectionCurrentExponent rho := by
  have hstab := (abs_le.mp (pairedEtaLeadingCurrent_fullInverseEnergy_firstMoment_stability rho K)).1
  have hcurrent := pairedEtaLeadingCurrent_firstMoment_le_fourProjection rho K
  have hB : 0 ≤ ∑' n : ℕ, pairedEtaCurrentZeroEnergyErrorEnvelope rho n :=
    tsum_nonneg (pairedEtaCurrentZeroEnergyErrorEnvelope_nonneg rho)
  have hpow : 1 ≤ (K + 1 : ℝ) ^ etaFourProjectionCurrentExponent rho :=
    Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) K]) (etaFourProjectionCurrentExponent_bounds rho).1
  nlinarith [mul_le_mul_of_nonneg_left hpow hB]

end

end RiemannGaussian
