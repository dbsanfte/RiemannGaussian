import RiemannGaussian.EtaFinitePhaseMargin
import RiemannGaussian.EtaCurrentQuadraticPrimeBound

/-!
# Finite phase arithmetic bounds the original current's cutoff exponent

The projection zero margin controls the horizontal displacement itself.
Its finite paired eta prefix and complete analytic tail produce an exponent
valid at every current cutoff, for both multiplicity branches and the full
inverse energy. Taking the minimum preserves every preceding prime margin.
No zero exponent or cutoff-independent weighted bound is assumed or proved.
-/

open Complex Set

namespace RiemannGaussian

noncomputable section

/-- The finite phase exponent, combined with all previously proved multiplicity-sensitive prime margins. -/
def etaFinitePhaseCurrentExponent (m N : ℕ) (y : ℝ) : ℝ :=
  min (1 - 2 * etaQuadraticPrimeProductZeroMargin m y)
    ((1 - etaFinitePhaseNormLower N y) / (1 + etaFinitePhaseNormLower N y))

/-- The finite phase budget is an actual exponent between zero and one at every nontrivial zero. -/
theorem etaFinitePhaseCurrentExponent_bounds (rho : NontrivialZetaZero) (N : ℕ) :
    0 ≤ etaFinitePhaseCurrentExponent (analyticZetaZeroMultiplicity rho) N rho.1.im ∧
      etaFinitePhaseCurrentExponent (analyticZetaZeroMultiplicity rho) N rho.1.im < 1 := by
  have hold := etaQuadraticPrimeProduct_return_exponent_bounds rho
  have hq := etaFinitePhaseNormLower_nonneg N rho.1.im
  have hq1 := etaFinitePhaseNormLower_le_one N rho.1.im
  unfold etaFinitePhaseCurrentExponent
  exact ⟨le_min (by linarith [hold.1]) (by positivity), (min_le_left _ _).trans_lt hold.2⟩

/-- Adding finite phase arithmetic never increases the preceding allowed cutoff power. -/
theorem etaFinitePhaseCurrentExponent_le_quadraticPrime (m N : ℕ) (y : ℝ) :
    etaFinitePhaseCurrentExponent m N y ≤ 1 - 2 * etaQuadraticPrimeProductZeroMargin m y :=
  min_le_left _ _

/-- This single-projection exponent budget stays at least `1/11` at every finite cutoff; this is a limitation of the upper bound, not a lower bound on any zero's displacement. -/
theorem one_eleventh_le_etaFinitePhaseCurrentExponent (rho : NontrivialZetaZero) (N : ℕ) :
    1 / 11 ≤ etaFinitePhaseCurrentExponent (analyticZetaZeroMultiplicity rho) N rho.1.im := by
  have hold := (etaQuadraticPrimeProduct_return_exponent_bounds rho).1
  have hq := etaFinitePhaseNormLower_nonneg N rho.1.im
  have hq1 := (etaFinitePhaseNormLower_le_norm N rho.1.im).trans
    (norm_pairedEtaPhaseBoundaryValue_le_five_sixths rho.1.im)
  unfold etaFinitePhaseCurrentExponent
  apply le_min (by linarith)
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- The actual zero's displacement is controlled by the finite arithmetic phase exponent, uniformly in the current cutoff. -/
theorem pairedEtaCurrentHorizontalDisplacement_le_finitePhase (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCurrentHorizontalDisplacement rho ≤
      etaFinitePhaseCurrentExponent (analyticZetaZeroMultiplicity rho) N rho.1.im := by
  have hz := nontrivialZetaZero_mem_etaFinitePhase_strip rho N
  have hp : pairedEtaCurrentHorizontalDisplacement rho ≤ 1 - 2 * etaFinitePhaseZeroMargin N rho.1.im := by
    unfold pairedEtaCurrentHorizontalDisplacement
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2]
  have hq := etaFinitePhaseNormLower_nonneg N rho.1.im
  have he : 1 - 2 * etaFinitePhaseZeroMargin N rho.1.im =
      (1 - etaFinitePhaseNormLower N rho.1.im) / (1 + etaFinitePhaseNormLower N rho.1.im) := by
    unfold etaFinitePhaseZeroMargin
    field_simp [show 1 + etaFinitePhaseNormLower N rho.1.im ≠ 0 by positivity]
    ring
  rw [he] at hp
  exact le_min (pairedEtaCurrentHorizontalDisplacement_le_quadraticPrime rho) hp

/-- The original real current has the common growth constant in both the critical and off-critical cases. -/
theorem pairedEtaLeadingCurrent_firstMoment_le_growthConstant (rho : NontrivialZetaZero) (K : ℕ) :
    (∑ n ∈ Finset.range K, (2 * n + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho n|) ≤
      pairedEtaCurrentReturnGrowthConstant rho * (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho := by
  by_cases hrho : rho.1.re = 1 / 2
  · simp only [pairedEtaLeadingCurrent_eq_zero_of_re_eq_half rho hrho, abs_zero, mul_zero, Finset.sum_const_zero]
    exact mul_nonneg (pairedEtaCurrentReturnGrowthConstant_nonneg rho) (by positivity)
  · have hc : pairedEtaCurrentGrowthAmplitude rho / pairedEtaCurrentHorizontalDisplacement rho ≤
        pairedEtaCurrentReturnGrowthConstant rho := by
      unfold pairedEtaCurrentReturnGrowthConstant
      rw [if_neg hrho]
      linarith [pairedEtaCurrentLinearHeatWeightedErrorBound_nonneg rho]
    exact (pairedEtaLeadingCurrent_firstMoment_growth_le_of_re_ne_half rho hrho K).trans
      (mul_le_mul_of_nonneg_right hc (by positivity))

/-- Every finite original eta prefix gives a proved all-cutoff power bound for both branches of the unchanged weighted current. -/
theorem pairedEtaLeadingCurrent_firstMoment_le_finitePhase (rho : NontrivialZetaZero) (N K : ℕ) :
    (∑ n ∈ Finset.range K, (2 * n + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho n|) ≤
      pairedEtaCurrentReturnGrowthConstant rho *
        (K + 1 : ℝ) ^ etaFinitePhaseCurrentExponent (analyticZetaZeroMultiplicity rho) N rho.1.im :=
  (pairedEtaLeadingCurrent_firstMoment_le_growthConstant rho K).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      (by linarith [Nat.cast_nonneg (α := ℝ) K]) (pairedEtaCurrentHorizontalDisplacement_le_finitePhase rho N))
      (pairedEtaCurrentReturnGrowthConstant_nonneg rho))

/-- The literal linear-width Gaussian return inherits the finite phase exponent with its original common constant. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_le_finitePhase (rho : NontrivialZetaZero) (N K : ℕ) :
    (∑ n ∈ Finset.range K, (2 * n + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho n‖) ≤
      pairedEtaCurrentReturnGrowthConstant rho *
        (K + 1 : ℝ) ^ etaFinitePhaseCurrentExponent (analyticZetaZeroMultiplicity rho) N rho.1.im :=
  (pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_growth_le rho K).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      (by linarith [Nat.cast_nonneg (α := ℝ) K]) (pairedEtaCurrentHorizontalDisplacement_le_finitePhase rho N))
      (pairedEtaCurrentReturnGrowthConstant_nonneg rho))

/-- The complete signed inverse energy obeys the same finite arithmetic power, retaining its summable transport error budget. -/
theorem pairedEtaCurrentFullInverseEnergy_firstMoment_le_finitePhase (rho : NontrivialZetaZero) (N K : ℕ) :
    (∑ n ∈ Finset.range K, (2 * n + 1 : ℝ) * |pairedEtaCurrentFullInverseEnergy rho n|) ≤
      (pairedEtaCurrentReturnGrowthConstant rho + ∑' n : ℕ, pairedEtaCurrentZeroEnergyErrorEnvelope rho n) *
        (K + 1 : ℝ) ^ etaFinitePhaseCurrentExponent (analyticZetaZeroMultiplicity rho) N rho.1.im := by
  have hstab := (abs_le.mp (pairedEtaLeadingCurrent_fullInverseEnergy_firstMoment_stability rho K)).1
  have hcurrent := pairedEtaLeadingCurrent_firstMoment_le_finitePhase rho N K
  have hB : 0 ≤ ∑' n : ℕ, pairedEtaCurrentZeroEnergyErrorEnvelope rho n :=
    tsum_nonneg (pairedEtaCurrentZeroEnergyErrorEnvelope_nonneg rho)
  have hpow : 1 ≤ (K + 1 : ℝ) ^ etaFinitePhaseCurrentExponent (analyticZetaZeroMultiplicity rho) N rho.1.im :=
    Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) K]) (etaFinitePhaseCurrentExponent_bounds rho N).1
  nlinarith [mul_le_mul_of_nonneg_left hpow hB]

end

end RiemannGaussian
