import RiemannGaussian.EtaCurrentZeroMomentReduction
import RiemannGaussian.EtaCurrentEulerEstimate

/-!
# Summable transport of both original current branches to full zeroth energies

The actual head and adjacent-moment products are retained as complex
channels. Their zeroth-energy replacements have one common form, with
the actual multiplicity and complex coefficients explicit. The original
signed current has a proved summable odd-weighted error from this form;
the weighted sum of the signed energies themselves is still unbounded by
the results here.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- One actual completed current channel, before reflection and the real-part map. -/
def pairedEtaCurrentChannelProduct (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  if analyticZetaZeroMultiplicity rho = 1 then
    pairedEtaHeadCompletedMoment rho N 0 * starRingEnd ℂ (pairedEtaFiniteCompletedMoment rho (N + 2) 0)
  else (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1) : ℝ) *
    (pairedEtaFiniteCompletedMoment rho (N + 2) (analyticZetaZeroMultiplicity rho - 2) *
      starRingEnd ℂ (pairedEtaFiniteCompletedMoment rho (N + 2) (analyticZetaZeroMultiplicity rho - 1)))

/-- The unchanged original current is the signed pair of its two actual complex channels. -/
theorem pairedEtaLeadingCurrent_eq_channelProducts (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N =
      2 * (pairedEtaCurrentChannelProduct (NontrivialZetaZero.conjugatePartner rho) N -
        starRingEnd ℂ (pairedEtaCurrentChannelProduct rho N)).re := by
  by_cases hm : analyticZetaZeroMultiplicity rho = 1
  · rw [pairedEtaLeadingCurrent_eq_headCompletedMomentPair rho hm]
    simp only [pairedEtaCurrentChannelProduct, analyticZetaZeroMultiplicity_conjugatePartner,
      hm, if_true, pairedEtaHeadCompletedMomentPair, etaSignedCompletedPair, map_mul,
      starRingEnd_apply, star_star]
  · have hm2 : 2 ≤ analyticZetaZeroMultiplicity rho := by
      have := analyticZetaZeroMultiplicity_positive rho
      omega
    rw [pairedEtaLeadingCurrent_eq_completedMomentPair rho hm2]
    simp only [pairedEtaCurrentChannelProduct, analyticZetaZeroMultiplicity_conjugatePartner,
      if_neg hm, pairedEtaFiniteCompletedMomentPair, etaSignedCompletedPair, map_mul,
      Complex.conj_ofReal, starRingEnd_self_apply, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring

/-- The complex coefficient of the full zeroth energy, selected by the actual multiplicity. -/
def pairedEtaCurrentZeroEnergyCoefficient (rho : NontrivialZetaZero) : ℂ :=
  if analyticZetaZeroMultiplicity rho = 1 then rho.1
  else ((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℂ) *
    (pairedEtaMomentParityCoefficient rho (analyticZetaZeroMultiplicity rho - 2) *
      starRingEnd ℂ (pairedEtaMomentParityCoefficient rho (analyticZetaZeroMultiplicity rho - 1)))

/-- Both actual multiplicity branches have strictly positive real zeroth-energy coefficients. -/
theorem pairedEtaCurrentZeroEnergyCoefficient_re_pos (rho : NontrivialZetaZero) :
    0 < (pairedEtaCurrentZeroEnergyCoefficient rho).re := by
  have ha (k : ℕ) : pairedEtaMomentParityCoefficient rho k =
      (2 * rho.1) * pairedEtaCurrentEulerMomentValue rho k := by
    rw [pairedEtaMomentParityCoefficient_eq, pairedEtaCurrentEulerMomentValue, pow_succ]
    field_simp [NontrivialZetaZero.coe_ne_zero rho]
  have hpair (k : ℕ) :
      pairedEtaMomentParityCoefficient rho k * starRingEnd ℂ (pairedEtaMomentParityCoefficient rho (k + 1)) =
        (Complex.normSq (2 * rho.1) : ℂ) *
          (pairedEtaCurrentEulerMomentValue rho k * starRingEnd ℂ (pairedEtaCurrentEulerMomentValue rho (k + 1))) := by
    rw [ha k, ha (k + 1), map_mul, ← Complex.mul_conj]
    ring
  have hpos (k : ℕ) : 0 <
      (pairedEtaMomentParityCoefficient rho k * starRingEnd ℂ (pairedEtaMomentParityCoefficient rho (k + 1))).re := by
    rw [hpair]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos (Complex.normSq_pos.mpr
      (mul_ne_zero (by norm_num) (NontrivialZetaZero.coe_ne_zero rho)))
      (pairedEtaCurrentEuler_adjacent_coefficient_pos rho k)
  unfold pairedEtaCurrentZeroEnergyCoefficient
  split
  · exact NontrivialZetaZero.zero_lt_re rho
  · rename_i hm
    have hm2 : 2 ≤ analyticZetaZeroMultiplicity rho := by
      have := analyticZetaZeroMultiplicity_positive rho
      omega
    rw [show analyticZetaZeroMultiplicity rho - 1 = analyticZetaZeroMultiplicity rho - 2 + 1 by omega]
    simpa only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] using
      mul_pos (by positivity : (0 : ℝ) < ((analyticZetaZeroMultiplicity rho - 2 + 1 : ℕ) : ℝ))
        (hpos (analyticZetaZeroMultiplicity rho - 2))

/-- The complete zeroth-moment channel keeps its complex coefficient and original cutoff increment. -/
def pairedEtaCurrentZeroEnergyChannel (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  (pairedEtaLogTailShiftIncrement (N + 1) : ℂ) * pairedEtaCurrentZeroEnergyCoefficient rho *
    (‖pairedEtaFiniteCompletedMoment rho (N + 2) 0‖ : ℂ) ^ 2

/-- The signed zeroth-energy expression is derived from the original current, with both colours retained. -/
def pairedEtaCurrentZeroEnergy (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  2 * (pairedEtaCurrentZeroEnergyChannel (NontrivialZetaZero.conjugatePartner rho) N -
    starRingEnd ℂ (pairedEtaCurrentZeroEnergyChannel rho N)).re

/-- Taking the real part leaves the signed full energies and the real parts of their complex coefficients. -/
theorem pairedEtaCurrentZeroEnergy_eq_signed_norms (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCurrentZeroEnergy rho N = 2 * pairedEtaLogTailShiftIncrement (N + 1) *
      ((pairedEtaCurrentZeroEnergyCoefficient (NontrivialZetaZero.conjugatePartner rho)).re *
          ‖pairedEtaFiniteCompletedMoment (NontrivialZetaZero.conjugatePartner rho) (N + 2) 0‖ ^ 2 -
        (pairedEtaCurrentZeroEnergyCoefficient rho).re * ‖pairedEtaFiniteCompletedMoment rho (N + 2) 0‖ ^ 2) := by
  simp only [pairedEtaCurrentZeroEnergy, pairedEtaCurrentZeroEnergyChannel, Complex.sub_re,
    Complex.conj_re, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
  ring

/-- At a simple zero the exact channel defect contains the original head transport error. -/
theorem pairedEtaCurrentChannelProduct_sub_zeroEnergy_simple (rho : NontrivialZetaZero)
    (hm : analyticZetaZeroMultiplicity rho = 1) (N : ℕ) :
    pairedEtaCurrentChannelProduct rho N - pairedEtaCurrentZeroEnergyChannel rho N =
      (pairedEtaHeadCompletedMoment rho N 0 - (pairedEtaLogTailShiftIncrement (N + 1) : ℂ) * rho.1 *
        pairedEtaFiniteCompletedMoment rho (N + 2) 0) *
          starRingEnd ℂ (pairedEtaFiniteCompletedMoment rho (N + 2) 0) := by
  simp only [pairedEtaCurrentChannelProduct, pairedEtaCurrentZeroEnergyChannel,
    pairedEtaCurrentZeroEnergyCoefficient, if_pos hm, ← Complex.mul_conj']
  ring

/-- At a repeated zero the full complex product error retains its original multiplicity and step. -/
theorem pairedEtaCurrentChannelProduct_sub_zeroEnergy_multiple (rho : NontrivialZetaZero)
    (hm : 2 ≤ analyticZetaZeroMultiplicity rho) (N : ℕ) :
    pairedEtaCurrentChannelProduct rho N - pairedEtaCurrentZeroEnergyChannel rho N =
      (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1) : ℝ) *
        (pairedEtaFiniteCompletedMoment rho (N + 2) (analyticZetaZeroMultiplicity rho - 2) *
            starRingEnd ℂ (pairedEtaFiniteCompletedMoment rho (N + 2) (analyticZetaZeroMultiplicity rho - 1)) -
          pairedEtaMomentParityCoefficient rho (analyticZetaZeroMultiplicity rho - 2) *
            starRingEnd ℂ (pairedEtaMomentParityCoefficient rho (analyticZetaZeroMultiplicity rho - 1)) *
              (‖pairedEtaFiniteCompletedMoment rho (N + 2) 0‖ : ℂ) ^ 2) := by
  have hm1 : analyticZetaZeroMultiplicity rho ≠ 1 := by omega
  simp only [pairedEtaCurrentChannelProduct, pairedEtaCurrentZeroEnergyChannel,
    pairedEtaCurrentZeroEnergyCoefficient, if_neg hm1, Complex.ofReal_mul, Complex.ofReal_natCast]
  ring

/-- The actual multiplicity chooses the finite coefficient in one channel's weighted transport error. -/
def pairedEtaCurrentZeroEnergyErrorConstant (rho : NontrivialZetaZero) : ℝ :=
  if analyticZetaZeroMultiplicity rho = 1 then
    pairedEtaCurrentZeroHeadErrorConstant rho * pairedEtaCurrentMomentConstant rho
  else ((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) *
    pairedEtaCurrentZeroPairErrorConstant rho (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1)

/-- Each multiplicity branch gives a nonnegative error coefficient. -/
theorem pairedEtaCurrentZeroEnergyErrorConstant_nonneg (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaCurrentZeroEnergyErrorConstant rho := by
  have hH := pairedEtaCurrentZeroHeadErrorConstant_nonneg rho
  have hQ := pairedEtaCurrentMomentConstant_nonneg rho
  have hP := pairedEtaCurrentZeroPairErrorConstant_nonneg rho
    (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1)
  unfold pairedEtaCurrentZeroEnergyErrorConstant
  split <;> positivity

/-- Both actual complex channels have a summable odd-weighted transport error. -/
theorem pairedEtaCurrentChannelProduct_weighted_zeroEnergy_error_le (rho : NontrivialZetaZero) (N : ℕ) :
    (2 * N + 1 : ℝ) * ‖pairedEtaCurrentChannelProduct rho N - pairedEtaCurrentZeroEnergyChannel rho N‖ ≤
      2 * pairedEtaCurrentZeroEnergyErrorConstant rho * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ) := by
  have hQ := pairedEtaCurrentMomentConstant_nonneg rho
  have hD := (pairedEtaCurrentMomentDecay_bounds rho N).1
  have hw : (0 : ℝ) ≤ 2 * N + 1 := by positivity
  by_cases hm : analyticZetaZeroMultiplicity rho = 1
  · rw [pairedEtaCurrentChannelProduct_sub_zeroEnergy_simple rho hm, norm_mul, norm_conj]
    have hH := pairedEtaCurrentZeroHeadErrorConstant_nonneg rho
    calc
      _ ≤ (2 * N + 1 : ℝ) *
          ((pairedEtaCurrentZeroHeadErrorConstant rho * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ) ^ 2) *
            pairedEtaCurrentMomentConstant rho) :=
        mul_le_mul_of_nonneg_left (mul_le_mul
          (norm_pairedEtaHeadCompletedMoment_sub_shift_mul_zero_le rho N)
          (norm_pairedEtaFiniteCompletedMoment_le rho (analyticZetaZeroMultiplicity_positive rho).le N)
          (norm_nonneg _) (by positivity)) hw
      _ ≤ _ := by
        unfold pairedEtaCurrentZeroEnergyErrorConstant
        rw [if_pos hm]
        have hweight : (2 * N + 1 : ℝ) ≤ 2 * (N + 1 : ℝ) := by linarith
        have h := mul_le_mul_of_nonneg_right hweight
          (show 0 ≤ pairedEtaCurrentZeroHeadErrorConstant rho * pairedEtaCurrentMomentDecay rho N /
            (N + 1 : ℝ) ^ 2 * pairedEtaCurrentMomentConstant rho by positivity)
        apply h.trans_eq
        field_simp
  · have hm2 : 2 ≤ analyticZetaZeroMultiplicity rho := by
      have := analyticZetaZeroMultiplicity_positive rho
      omega
    have hδ := (pairedEtaLogTailShiftIncrement_pos (N + 1)).le
    have hP := pairedEtaCurrentZeroPairErrorConstant_nonneg rho
      (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1)
    rw [pairedEtaCurrentChannelProduct_sub_zeroEnergy_multiple rho hm2, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ (2 * N + 1 : ℝ) *
          ((((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
            (pairedEtaCurrentZeroPairErrorConstant rho (analyticZetaZeroMultiplicity rho - 2)
              (analyticZetaZeroMultiplicity rho - 1) * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (norm_pairedEtaFiniteCompletedMoment_product_sub_zero_le rho (by omega) (by omega) N) (by positivity)) hw
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right (pairedEtaCurrent_odd_weight_mul_shift_le_two N)
          (show 0 ≤ ((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) *
            pairedEtaCurrentZeroPairErrorConstant rho (analyticZetaZeroMultiplicity rho - 2)
              (analyticZetaZeroMultiplicity rho - 1) * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ) by positivity)
        simpa only [pairedEtaCurrentZeroEnergyErrorConstant, if_neg hm, mul_div_assoc,
          mul_assoc, mul_left_comm, mul_comm] using h

/-- The sum of the two proved channel envelopes, including the current's factor two. -/
def pairedEtaCurrentZeroEnergyErrorEnvelope (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  4 * (pairedEtaCurrentZeroEnergyErrorConstant (NontrivialZetaZero.conjugatePartner rho) *
      pairedEtaCurrentMomentDecay (NontrivialZetaZero.conjugatePartner rho) N / (N + 1 : ℝ) +
    pairedEtaCurrentZeroEnergyErrorConstant rho * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ))

/-- The complete signed transport envelope is nonnegative at every physical cutoff. -/
theorem pairedEtaCurrentZeroEnergyErrorEnvelope_nonneg (rho : NontrivialZetaZero) (N : ℕ) :
    0 ≤ pairedEtaCurrentZeroEnergyErrorEnvelope rho N := by
  have hC := pairedEtaCurrentZeroEnergyErrorConstant_nonneg rho
  have hCp := pairedEtaCurrentZeroEnergyErrorConstant_nonneg (NontrivialZetaZero.conjugatePartner rho)
  have hD := (pairedEtaCurrentMomentDecay_bounds rho N).1
  have hDp := (pairedEtaCurrentMomentDecay_bounds (NontrivialZetaZero.conjugatePartner rho) N).1
  unfold pairedEtaCurrentZeroEnergyErrorEnvelope
  positivity

/-- The full error envelope has a finite sum, using the actual positive horizontal coordinates. -/
theorem summable_pairedEtaCurrentZeroEnergyErrorEnvelope (rho : NontrivialZetaZero) :
    Summable (pairedEtaCurrentZeroEnergyErrorEnvelope rho) := by
  have hs (z : NontrivialZetaZero) : Summable (fun N : ℕ ↦ pairedEtaCurrentMomentDecay z N / (N + 1 : ℝ)) := by
    simpa only [pow_zero, one_mul] using summable_pairedEtaCurrent_logPower_mul_decay_div z 0
  change Summable (fun N ↦ pairedEtaCurrentZeroEnergyErrorEnvelope rho N)
  simpa only [pairedEtaCurrentZeroEnergyErrorEnvelope, mul_div_assoc] using
    (((hs (NontrivialZetaZero.conjugatePartner rho)).mul_left
      (pairedEtaCurrentZeroEnergyErrorConstant (NontrivialZetaZero.conjugatePartner rho))).add
      ((hs rho).mul_left (pairedEtaCurrentZeroEnergyErrorConstant rho))).mul_left 4

/-- The original current retains the signed complex channel defects before taking any norm. -/
theorem pairedEtaLeadingCurrent_sub_zeroEnergy (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N - pairedEtaCurrentZeroEnergy rho N =
      2 * ((pairedEtaCurrentChannelProduct (NontrivialZetaZero.conjugatePartner rho) N -
          pairedEtaCurrentZeroEnergyChannel (NontrivialZetaZero.conjugatePartner rho) N) -
        starRingEnd ℂ (pairedEtaCurrentChannelProduct rho N - pairedEtaCurrentZeroEnergyChannel rho N)).re := by
  rw [pairedEtaLeadingCurrent_eq_channelProducts, pairedEtaCurrentZeroEnergy]
  simp only [map_sub, Complex.sub_re]
  ring

/-- The unchanged original current has a summable weighted error from the complete signed zeroth energies. -/
theorem pairedEtaLeadingCurrent_weighted_zeroEnergy_error_le (rho : NontrivialZetaZero) (N : ℕ) :
    (2 * N + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N - pairedEtaCurrentZeroEnergy rho N| ≤
      pairedEtaCurrentZeroEnergyErrorEnvelope rho N := by
  rw [pairedEtaLeadingCurrent_sub_zeroEnergy, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hnorm := (Complex.abs_re_le_norm
    ((pairedEtaCurrentChannelProduct (NontrivialZetaZero.conjugatePartner rho) N -
        pairedEtaCurrentZeroEnergyChannel (NontrivialZetaZero.conjugatePartner rho) N) -
      starRingEnd ℂ (pairedEtaCurrentChannelProduct rho N - pairedEtaCurrentZeroEnergyChannel rho N))).trans
    (norm_sub_le _ _)
  rw [norm_conj] at hnorm
  have h := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 2 * (2 * N + 1 : ℝ) by positivity)
  have hp := pairedEtaCurrentChannelProduct_weighted_zeroEnergy_error_le (NontrivialZetaZero.conjugatePartner rho) N
  have ho := pairedEtaCurrentChannelProduct_weighted_zeroEnergy_error_le rho N
  unfold pairedEtaCurrentZeroEnergyErrorEnvelope
  simp only [mul_div_assoc] at hp ho ⊢
  nlinarith

end

end RiemannGaussian
