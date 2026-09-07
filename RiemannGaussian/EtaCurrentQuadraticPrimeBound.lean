import RiemannGaussian.ZetaSignedQuadraticComparison
import RiemannGaussian.EtaCurrentFullInverseEnergy

/-!
# A stronger arithmetic exponent for the original current and full inverse energy

The new quadratic prime margin is combined with every previously checked
zero margin. Its literal zero-strip theorem reduces the original current's
allowed horizontal growth exponent, including at simple zeros. The full
inverse energy retains its proved finite transport budget. The exponent
remains positive; the cutoff-independent weighted goal is still open.
-/

open Complex Set
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The strongest of the new quadratic prime margin and all previous actual-zero margins. -/
def etaQuadraticPrimeProductZeroMargin (m : ℕ) (y : ℝ) : ℝ :=
  max (etaSignedPrimeProductZeroMargin m y) (zetaSignedQuadraticZeroMargin m y)

/-- Every actual zero satisfies the combined strip with its full multiplicity. -/
theorem nontrivialZetaZero_mem_etaQuadraticPrimeProduct_strip (rho : NontrivialZetaZero) :
    rho.1.re ∈ Icc (etaQuadraticPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im)
      (1 - etaQuadraticPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im) := by
  have hold := nontrivialZetaZero_mem_etaSignedPrimeProduct_strip rho
  have hnew := nontrivialZetaZero_mem_signedQuadratic_strip rho
  constructor
  · exact max_le hold.1 hnew.1
  · have h : etaQuadraticPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im ≤ 1 - rho.1.re :=
      max_le (by linarith [hold.2]) (by linarith [hnew.2])
    linarith

/-- The new exponent retains an explicit positive lower bound and is strictly below one. -/
theorem etaQuadraticPrimeProduct_return_exponent_bounds (rho : NontrivialZetaZero) :
    7 / 8 ≤ 1 - 2 * etaQuadraticPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im ∧
      1 - 2 * etaQuadraticPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im < 1 := by
  have hold := etaSignedPrimeProduct_return_exponent_bounds rho
  have hsmall : etaQuadraticPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im ≤ 1 / 16 :=
    max_le (by linarith [hold.1]) ((zetaSignedQuadraticZeroMargin_le_one_div _ _).trans (by norm_num))
  have hpos : 0 < etaQuadraticPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im :=
    (zetaSignedQuadraticZeroMargin_pos _ (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)).trans_le (le_max_right _ _)
  constructor <;> linarith

/-- At every actual simple zero the new arithmetic margin strictly dominates the complete previous bound. -/
theorem etaSignedPrimeProductZeroMargin_lt_quadratic_of_simple (rho : NontrivialZetaZero)
    (hm : analyticZetaZeroMultiplicity rho = 1) :
    etaSignedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im <
      etaQuadraticPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im := by
  rw [etaSignedPrimeProductZeroMargin_eq_signed_of_simple rho hm]
  have h := thirtyOne_mul_signedLogZeroMargin_lt_quadratic (analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)
  have hp := zetaSignedLogZeroMargin_pos (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)
  exact (show zetaSignedLogZeroMargin rho.1.im <
    zetaSignedQuadraticZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im by linarith).trans_le (le_max_right _ _)

/-- The original current's permitted exponent strictly improves at every actual simple zero. -/
theorem etaQuadraticPrimeProduct_return_exponent_lt_of_simple (rho : NontrivialZetaZero)
    (hm : analyticZetaZeroMultiplicity rho = 1) :
    1 - 2 * etaQuadraticPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im <
      1 - 2 * etaSignedPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im := by
  linarith [etaSignedPrimeProductZeroMargin_lt_quadratic_of_simple rho hm]

/-- The proved arithmetic zero strip constrains the horizontal displacement controlling both original branches. -/
theorem pairedEtaCurrentHorizontalDisplacement_le_quadraticPrime (rho : NontrivialZetaZero) :
    pairedEtaCurrentHorizontalDisplacement rho ≤
      1 - 2 * etaQuadraticPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im := by
  have hz := nontrivialZetaZero_mem_etaQuadraticPrimeProduct_strip rho
  unfold pairedEtaCurrentHorizontalDisplacement
  rw [abs_le]
  constructor <;> linarith [hz.1, hz.2]

/-- Both original current branches satisfy the improved all-cutoff arithmetic power bound. -/
theorem pairedEtaLeadingCurrent_firstMoment_le_quadraticPrime (rho : NontrivialZetaZero) (K : ℕ) :
    (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N|) ≤
      pairedEtaCurrentReturnGrowthConstant rho *
        (K + 1 : ℝ) ^ (1 - 2 * etaQuadraticPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im) := by
  have hC := pairedEtaCurrentReturnGrowthConstant_nonneg rho
  by_cases hrho : rho.1.re = 1 / 2
  · simp only [pairedEtaLeadingCurrent_eq_zero_of_re_eq_half rho hrho, abs_zero, mul_zero, Finset.sum_const_zero]
    positivity
  · have hc : pairedEtaCurrentGrowthAmplitude rho / pairedEtaCurrentHorizontalDisplacement rho ≤
        pairedEtaCurrentReturnGrowthConstant rho := by
      unfold pairedEtaCurrentReturnGrowthConstant
      rw [if_neg hrho]
      linarith [pairedEtaCurrentLinearHeatWeightedErrorBound_nonneg rho]
    calc
      _ ≤ (pairedEtaCurrentGrowthAmplitude rho / pairedEtaCurrentHorizontalDisplacement rho) *
          (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho :=
        pairedEtaLeadingCurrent_firstMoment_growth_le_of_re_ne_half rho hrho K
      _ ≤ pairedEtaCurrentReturnGrowthConstant rho * (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) K])
          (pairedEtaCurrentHorizontalDisplacement_le_quadraticPrime rho)) hC

/-- The actual linear-width Gaussian return inherits the smaller exponent with its original finite constant. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_le_quadraticPrime (rho : NontrivialZetaZero) (K : ℕ) :
    (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N‖) ≤
      pairedEtaCurrentReturnGrowthConstant rho *
        (K + 1 : ℝ) ^ (1 - 2 * etaQuadraticPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im) :=
  (pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_growth_le rho K).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) K])
      (pairedEtaCurrentHorizontalDisplacement_le_quadraticPrime rho)) (pairedEtaCurrentReturnGrowthConstant_nonneg rho))

/-- The complete signed inverse energy has the improved exponent and keeps its genuinely finite transport budget. -/
theorem pairedEtaCurrentFullInverseEnergy_firstMoment_le_quadraticPrime (rho : NontrivialZetaZero) (K : ℕ) :
    (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * |pairedEtaCurrentFullInverseEnergy rho N|) ≤
      (pairedEtaCurrentReturnGrowthConstant rho + ∑' N : ℕ, pairedEtaCurrentZeroEnergyErrorEnvelope rho N) *
        (K + 1 : ℝ) ^ (1 - 2 * etaQuadraticPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im) := by
  have hstab := (abs_le.mp (pairedEtaLeadingCurrent_fullInverseEnergy_firstMoment_stability rho K)).1
  have hcurrent := pairedEtaLeadingCurrent_firstMoment_le_quadraticPrime rho K
  have hB : 0 ≤ ∑' N : ℕ, pairedEtaCurrentZeroEnergyErrorEnvelope rho N :=
    tsum_nonneg (pairedEtaCurrentZeroEnergyErrorEnvelope_nonneg rho)
  have hpow : 1 ≤ (K + 1 : ℝ) ^
      (1 - 2 * etaQuadraticPrimeProductZeroMargin (analyticZetaZeroMultiplicity rho) rho.1.im) :=
    Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) K])
      (by linarith [(etaQuadraticPrimeProduct_return_exponent_bounds rho).1])
  nlinarith [mul_le_mul_of_nonneg_left hpow hB]

end

end RiemannGaussian
