import RiemannGaussian.EtaLeadingFluxSignedInversePartialSum

/-!
# Summable normalization of the signed reflected inverse energy

The actual odd weight times the logarithmic step differs from two by at
most `4/(N+1)`. Multiplying this error by the complete reflected energy
gives a genuinely summable envelope at every actual zero. Consequently
the signed inverse sum is four times the unweighted reflected-energy sum
plus a convergent signed correction. Only this correction is bounded by
separate channel norms; the main signed difference is kept unchanged.
-/

open Complex Filter Topology
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- A quantitative rate for the literal odd-weight/logarithmic-step
factor, valid at every cutoff including zero. -/
theorem pairedEtaCurrent_abs_odd_weight_mul_shift_sub_two_le (N : ℕ) :
    |(2 * N + 1 : ℝ) * pairedEtaLogTailShiftIncrement (N + 1) - 2| ≤ 4 / (N + 1 : ℝ) := by
  rw [abs_of_nonpos (sub_nonpos.mpr (pairedEtaCurrent_odd_weight_mul_shift_le_two N))]
  have hl := mul_le_mul_of_nonneg_left (pairedEtaCurrent_shiftIncrement_lower N)
    (by positivity : (0 : ℝ) ≤ 2 * N + 1)
  have hrat : 2 - (2 * N + 1 : ℝ) * (2 / (2 * N + 5 : ℝ)) = 8 / (2 * N + 5 : ℝ) := by
    field_simp
    ring
  have hle : 8 / (2 * N + 5 : ℝ) ≤ 4 / (N + 1 : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith
  linarith

/-- The full reflected zeroth-energy bracket, with the true positive
coefficients and both actual finite completed moments retained. -/
def pairedEtaCurrentReflectedEnergy (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  (pairedEtaCurrentZeroEnergyCoefficient (NontrivialZetaZero.conjugatePartner rho)).re *
      ‖pairedEtaFiniteCompletedMoment (NontrivialZetaZero.conjugatePartner rho) (N + 2) 0‖ ^ 2 -
    (pairedEtaCurrentZeroEnergyCoefficient rho).re * ‖pairedEtaFiniteCompletedMoment rho (N + 2) 0‖ ^ 2

/-- Exact full inversion expresses the normalized bracket through both
complete inverse regions, at their original physical cutoff and center. -/
theorem pairedEtaCurrentReflectedEnergy_eq_fullInverseRegions (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCurrentReflectedEnergy rho N =
      (pairedEtaCurrentZeroEnergyCoefficient (NontrivialZetaZero.conjugatePartner rho)).re *
          ‖pairedEtaCompletedMomentInverseRegion (NontrivialZetaZero.conjugatePartner rho) 0
            (pairedEtaLogTailCutoff (N + 2)) (2 * (N + 2))
            (pairedEtaInverseHyperbolicRegion (2 * (N + 2)))‖ ^ 2 -
        (pairedEtaCurrentZeroEnergyCoefficient rho).re *
          ‖pairedEtaCompletedMomentInverseRegion rho 0 (pairedEtaLogTailCutoff (N + 2)) (2 * (N + 2))
            (pairedEtaInverseHyperbolicRegion (2 * (N + 2)))‖ ^ 2 := by
  simp only [pairedEtaCurrentReflectedEnergy, pairedEtaFiniteCompletedMoment_eq_fullInverseRegion]

/-- The full inverse energy is exactly twice the logarithmic step times
the normalized signed bracket. -/
theorem pairedEtaCurrentFullInverseEnergy_eq_reflectedEnergy (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCurrentFullInverseEnergy rho N =
      2 * pairedEtaLogTailShiftIncrement (N + 1) * pairedEtaCurrentReflectedEnergy rho N := by
  rw [pairedEtaCurrentFullInverseEnergy_eq_zeroEnergy, pairedEtaCurrentZeroEnergy_eq_signed_norms]
  rfl

/-- The cumulative normalized reflected energies retain their signs. -/
def pairedEtaNormalizedReflectedEnergyPartialSum (rho : NontrivialZetaZero) (K : ℕ) : ℝ :=
  ∑ N ∈ Finset.range K, pairedEtaCurrentReflectedEnergy rho N

/-- The pointwise signed normalization error, before its absolute estimate. -/
theorem pairedEtaCurrentFullInverseEnergy_weighted_sub_four_reflected
    (rho : NontrivialZetaZero) (N : ℕ) :
    (2 * N + 1 : ℝ) * pairedEtaCurrentFullInverseEnergy rho N -
      4 * pairedEtaCurrentReflectedEnergy rho N =
        2 * ((2 * N + 1 : ℝ) * pairedEtaLogTailShiftIncrement (N + 1) - 2) *
          pairedEtaCurrentReflectedEnergy rho N := by
  rw [pairedEtaCurrentFullInverseEnergy_eq_reflectedEnergy]
  ring

private theorem zero_energy_norm_sq_le_decay (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaFiniteCompletedMoment rho (N + 2) 0‖ ^ 2 ≤
      pairedEtaCurrentMomentConstant rho ^ 2 * pairedEtaCurrentMomentDecay rho N := by
  have hn := norm_pairedEtaFiniteCompletedMoment_lower_le rho (analyticZetaZeroMultiplicity_positive rho) N
  have hD := pairedEtaCurrentMomentDecay_bounds rho N
  have hC := pairedEtaCurrentMomentConstant_nonneg rho
  calc
    _ ≤ (pairedEtaCurrentMomentConstant rho * pairedEtaCurrentMomentDecay rho N) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC hD.1)).mpr hn
    _ ≤ _ := by
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      nlinarith

/-- An explicit envelope for only the normalization error. The main
reflected energy has not been replaced by this separate-channel bound. -/
def pairedEtaCurrentStepNormalizationErrorEnvelope (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  8 * ((pairedEtaCurrentZeroEnergyCoefficient (NontrivialZetaZero.conjugatePartner rho)).re *
      pairedEtaCurrentMomentConstant (NontrivialZetaZero.conjugatePartner rho) ^ 2 *
      pairedEtaCurrentMomentDecay (NontrivialZetaZero.conjugatePartner rho) N / (N + 1 : ℝ) +
    (pairedEtaCurrentZeroEnergyCoefficient rho).re * pairedEtaCurrentMomentConstant rho ^ 2 *
      pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ))

/-- The normalization envelope is nonnegative at every actual cutoff. -/
theorem pairedEtaCurrentStepNormalizationErrorEnvelope_nonneg (rho : NontrivialZetaZero) (N : ℕ) :
    0 ≤ pairedEtaCurrentStepNormalizationErrorEnvelope rho N := by
  have hp := (pairedEtaCurrentZeroEnergyCoefficient_re_pos (NontrivialZetaZero.conjugatePartner rho)).le
  have hq := (pairedEtaCurrentZeroEnergyCoefficient_re_pos rho).le
  have hDp := (pairedEtaCurrentMomentDecay_bounds (NontrivialZetaZero.conjugatePartner rho) N).1
  have hDq := (pairedEtaCurrentMomentDecay_bounds rho N).1
  unfold pairedEtaCurrentStepNormalizationErrorEnvelope
  positivity

/-- The extra inverse-cutoff factor makes the entire normalization
envelope summable throughout the open critical strip. -/
theorem summable_pairedEtaCurrentStepNormalizationErrorEnvelope (rho : NontrivialZetaZero) :
    Summable (pairedEtaCurrentStepNormalizationErrorEnvelope rho) := by
  have hs (z : NontrivialZetaZero) : Summable (fun N : ℕ ↦ pairedEtaCurrentMomentDecay z N / (N + 1 : ℝ)) := by
    simpa only [pow_zero, one_mul] using summable_pairedEtaCurrent_logPower_mul_decay_div z 0
  change Summable (fun N ↦ pairedEtaCurrentStepNormalizationErrorEnvelope rho N)
  simpa only [pairedEtaCurrentStepNormalizationErrorEnvelope, mul_div_assoc] using
    (((hs (NontrivialZetaZero.conjugatePartner rho)).mul_left
      ((pairedEtaCurrentZeroEnergyCoefficient (NontrivialZetaZero.conjugatePartner rho)).re *
        pairedEtaCurrentMomentConstant (NontrivialZetaZero.conjugatePartner rho) ^ 2)).add
      ((hs rho).mul_left
        ((pairedEtaCurrentZeroEnergyCoefficient rho).re * pairedEtaCurrentMomentConstant rho ^ 2))).mul_left 8

/-- Replacing the odd-weight/log-step factor by two costs a proved
summable amount in the complete original signed inverse energy. -/
theorem pairedEtaCurrentFullInverseEnergy_weighted_normalization_error_le
    (rho : NontrivialZetaZero) (N : ℕ) :
    |(2 * N + 1 : ℝ) * pairedEtaCurrentFullInverseEnergy rho N -
      4 * pairedEtaCurrentReflectedEnergy rho N| ≤ pairedEtaCurrentStepNormalizationErrorEnvelope rho N := by
  let P := NontrivialZetaZero.conjugatePartner rho
  have hp := (pairedEtaCurrentZeroEnergyCoefficient_re_pos P).le
  have hq := (pairedEtaCurrentZeroEnergyCoefficient_re_pos rho).le
  have hBp := mul_le_mul_of_nonneg_left (zero_energy_norm_sq_le_decay P N) hp
  have hBq := mul_le_mul_of_nonneg_left (zero_energy_norm_sq_le_decay rho N) hq
  have hB : |pairedEtaCurrentReflectedEnergy rho N| ≤
      (pairedEtaCurrentZeroEnergyCoefficient P).re * pairedEtaCurrentMomentConstant P ^ 2 *
        pairedEtaCurrentMomentDecay P N +
      (pairedEtaCurrentZeroEnergyCoefficient rho).re * pairedEtaCurrentMomentConstant rho ^ 2 *
        pairedEtaCurrentMomentDecay rho N := by
    have htriangle := norm_sub_le
      ((pairedEtaCurrentZeroEnergyCoefficient P).re * ‖pairedEtaFiniteCompletedMoment P (N + 2) 0‖ ^ 2)
      ((pairedEtaCurrentZeroEnergyCoefficient rho).re * ‖pairedEtaFiniteCompletedMoment rho (N + 2) 0‖ ^ 2)
    simp only [Real.norm_eq_abs] at htriangle
    apply htriangle.trans
    rw [abs_of_nonneg (mul_nonneg hp (sq_nonneg _)), abs_of_nonneg (mul_nonneg hq (sq_nonneg _))]
    simpa only [mul_assoc] using add_le_add hBp hBq
  rw [pairedEtaCurrentFullInverseEnergy_weighted_sub_four_reflected, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := mul_le_mul
    (mul_le_mul_of_nonneg_left (pairedEtaCurrent_abs_odd_weight_mul_shift_sub_two_le N) (by norm_num : (0 : ℝ) ≤ 2))
    hB (abs_nonneg _) (by positivity)
  exact h.trans_eq (by dsimp [pairedEtaCurrentStepNormalizationErrorEnvelope, P]; ring)

/-- Absolute summability is proved for the normalization error itself. -/
theorem summable_pairedEtaCurrentFullInverseEnergy_normalization_error (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦ |(2 * N + 1 : ℝ) * pairedEtaCurrentFullInverseEnergy rho N -
      4 * pairedEtaCurrentReflectedEnergy rho N|) :=
  (summable_pairedEtaCurrentStepNormalizationErrorEnvelope rho).of_nonneg_of_le
    (fun _ ↦ abs_nonneg _) (pairedEtaCurrentFullInverseEnergy_weighted_normalization_error_le rho)

/-- A single finite explicit budget normalizes every signed partial sum. -/
theorem pairedEtaFullInverseEnergySignedPartialSum_normalized_error_le
    (rho : NontrivialZetaZero) (K : ℕ) :
    |pairedEtaFullInverseEnergySignedPartialSum rho K - 4 * pairedEtaNormalizedReflectedEnergyPartialSum rho K| ≤
      ∑' N : ℕ, pairedEtaCurrentStepNormalizationErrorEnvelope rho N := by
  unfold pairedEtaFullInverseEnergySignedPartialSum pairedEtaNormalizedReflectedEnergyPartialSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ N ∈ Finset.range K, |(2 * N + 1 : ℝ) * pairedEtaCurrentFullInverseEnergy rho N -
        4 * pairedEtaCurrentReflectedEnergy rho N| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ N ∈ Finset.range K, pairedEtaCurrentStepNormalizationErrorEnvelope rho N :=
      Finset.sum_le_sum (fun N _ ↦ pairedEtaCurrentFullInverseEnergy_weighted_normalization_error_le rho N)
    _ ≤ _ := (summable_pairedEtaCurrentStepNormalizationErrorEnvelope rho).sum_le_tsum _
      (fun N _ ↦ pairedEtaCurrentStepNormalizationErrorEnvelope_nonneg rho N)

/-- The signed normalization correction converges to its actual series,
so the exact representation accompanies the uniform absolute budget. -/
theorem pairedEtaFullInverseEnergySignedPartialSum_sub_normalized_tendsto (rho : NontrivialZetaZero) :
    Tendsto (fun K : ℕ ↦ pairedEtaFullInverseEnergySignedPartialSum rho K -
      4 * pairedEtaNormalizedReflectedEnergyPartialSum rho K) atTop
        (𝓝 (∑' N : ℕ, ((2 * N + 1 : ℝ) * pairedEtaCurrentFullInverseEnergy rho N -
          4 * pairedEtaCurrentReflectedEnergy rho N))) := by
  have hs : Summable (fun N : ℕ ↦ (2 * N + 1 : ℝ) * pairedEtaCurrentFullInverseEnergy rho N -
      4 * pairedEtaCurrentReflectedEnergy rho N) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using summable_pairedEtaCurrentFullInverseEnergy_normalization_error rho
  simpa only [pairedEtaFullInverseEnergySignedPartialSum, pairedEtaNormalizedReflectedEnergyPartialSum,
    Finset.mul_sum, ← Finset.sum_sub_distrib] using hs.hasSum.tendsto_sum_nat

/-- The actual signed current is four times the normalized reflected sum
up to the two complete, proved finite transport budgets. -/
theorem pairedEtaLeadingFluxSignedPartialSum_normalized_error_le
    (rho : NontrivialZetaZero) (K : ℕ) :
    |pairedEtaLeadingFluxSignedPartialSum rho K - 4 * pairedEtaNormalizedReflectedEnergyPartialSum rho K| ≤
      (∑' N : ℕ, pairedEtaCurrentZeroEnergyErrorEnvelope rho N) +
        ∑' N : ℕ, pairedEtaCurrentStepNormalizationErrorEnvelope rho N := by
  exact (abs_sub_le _ (pairedEtaFullInverseEnergySignedPartialSum rho K) _).trans
    (add_le_add (pairedEtaLeadingFluxSignedPartialSum_fullInverse_error_le rho K)
      (pairedEtaFullInverseEnergySignedPartialSum_normalized_error_le rho K))

/-- The normalized complete energy sum retains the off-critical lower
power, with all early cutoffs and both transport errors explicitly paid. -/
theorem pairedEtaNormalizedReflectedEnergyPartialSum_lower_with_offset
    (rho : NontrivialZetaZero) (hrho : rho.1.re ≠ 1 / 2) : ∃ N₀ : ℕ, ∀ K : ℕ,
      pairedEtaCurrentReturnGrowthLowerCoefficient rho * (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho -
        (pairedEtaLeadingFluxSignedGrowthOffset rho N₀ +
          (∑' N : ℕ, pairedEtaCurrentZeroEnergyErrorEnvelope rho N) +
            ∑' N : ℕ, pairedEtaCurrentStepNormalizationErrorEnvelope rho N) ≤
        4 * (pairedEtaLeadingFluxSide rho * pairedEtaNormalizedReflectedEnergyPartialSum rho K) := by
  obtain ⟨N₀, hN₀⟩ := pairedEtaLeadingFluxSignedPartialSum_lower_with_offset rho hrho
  refine ⟨N₀, fun K ↦ ?_⟩
  have h := (pairedEtaLeadingFluxSide_mul_le_abs rho
    (pairedEtaLeadingFluxSignedPartialSum rho K - 4 * pairedEtaNormalizedReflectedEnergyPartialSum rho K)).trans
      (pairedEtaLeadingFluxSignedPartialSum_normalized_error_le rho K)
  nlinarith [hN₀ K, h]

/-- Removing the odd-weight/log-step factor preserves a positive eighth
of the original lower coefficient. The remaining arithmetic target is a
relative vanishing upper factor for this unweighted signed energy sum. -/
theorem pairedEtaNormalizedReflectedEnergyPartialSum_power_lower_eventually
    (rho : NontrivialZetaZero) (hrho : rho.1.re ≠ 1 / 2) : ∀ᶠ K : ℕ in atTop,
      (pairedEtaCurrentReturnGrowthLowerCoefficient rho / 8) *
        (K + 1 : ℝ) ^ pairedEtaCurrentHorizontalDisplacement rho ≤
          pairedEtaLeadingFluxSide rho * pairedEtaNormalizedReflectedEnergyPartialSum rho K := by
  obtain ⟨N₀, hN₀⟩ := pairedEtaNormalizedReflectedEnergyPartialSum_lower_with_offset rho hrho
  have hc := pairedEtaCurrentReturnGrowthLowerCoefficient_pos rho hrho
  have hx : Tendsto (fun K : ℕ ↦ (K + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have ht := ((tendsto_rpow_atTop (pairedEtaCurrentHorizontalDisplacement_pos rho hrho)).comp hx).const_mul_atTop
    (by positivity : 0 < pairedEtaCurrentReturnGrowthLowerCoefficient rho / 2)
  filter_upwards [ht.eventually_ge_atTop (pairedEtaLeadingFluxSignedGrowthOffset rho N₀ +
    (∑' N : ℕ, pairedEtaCurrentZeroEnergyErrorEnvelope rho N) +
      ∑' N : ℕ, pairedEtaCurrentStepNormalizationErrorEnvelope rho N)] with K hK
  dsimp only [Function.comp_apply] at hK
  nlinarith [hN₀ K]

end

end RiemannGaussian
