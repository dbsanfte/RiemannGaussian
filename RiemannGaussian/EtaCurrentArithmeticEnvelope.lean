import RiemannGaussian.EtaCurrentEulerEstimate

/-!
# Two endpoint decays in the original completed current

Both factors of the actual leading-current pair lie below the zero
multiplicity. Keeping both zero-tail decays improves the bound for the
current itself. The exact signed pairs and Euler identities remain
upstream; this norm envelope is a downstream estimate on those carriers.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Both actual completed zero channels with both lower-moment decays retained. -/
def pairedEtaCurrentDoubleDecayEnvelope (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  pairedEtaCurrentMomentConstant (NontrivialZetaZero.conjugatePartner rho) ^ 2 *
      pairedEtaCurrentMomentDecay (NontrivialZetaZero.conjugatePartner rho) N ^ 2 +
    pairedEtaCurrentMomentConstant rho ^ 2 * pairedEtaCurrentMomentDecay rho N ^ 2

/-- The double-decay current envelope is nonnegative. -/
theorem pairedEtaCurrentDoubleDecayEnvelope_nonneg (rho : NontrivialZetaZero) (N : ℕ) :
    0 ≤ pairedEtaCurrentDoubleDecayEnvelope rho N := by
  unfold pairedEtaCurrentDoubleDecayEnvelope
  positivity

/-- Both lower finite moment factors retain their actual endpoint decay. -/
theorem norm_pairedEtaCurrent_lower_product_le_doubleDecay (rho : NontrivialZetaZero) {k l : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) (hl : l < analyticZetaZeroMultiplicity rho) (N : ℕ) :
    ‖pairedEtaFiniteCompletedMoment rho (N + 2) k‖ * ‖pairedEtaFiniteCompletedMoment rho (N + 2) l‖ ≤
      pairedEtaCurrentMomentConstant rho ^ 2 * pairedEtaCurrentMomentDecay rho N ^ 2 := by
  have hQ := pairedEtaCurrentMomentConstant_nonneg rho
  have hd := (pairedEtaCurrentMomentDecay_bounds rho N).1
  exact (mul_le_mul (norm_pairedEtaFiniteCompletedMoment_lower_le rho hk N)
    (norm_pairedEtaFiniteCompletedMoment_lower_le rho hl N) (norm_nonneg _) (mul_nonneg hQ hd)).trans_eq (by ring)

/-- The norm of the original complex adjacent pair has both endpoint decays. -/
theorem norm_pairedEtaFiniteCompletedMomentPair_le_doubleDecay (rho : NontrivialZetaZero) {k l : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) (hl : l < analyticZetaZeroMultiplicity rho) (N : ℕ) :
    ‖pairedEtaFiniteCompletedMomentPair rho (N + 2) k l‖ ≤ pairedEtaCurrentDoubleDecayEnvelope rho N := by
  exact (norm_etaSignedCompletedPair_le _ _ _ _).trans
    (add_le_add (norm_pairedEtaCurrent_lower_product_le_doubleDecay (NontrivialZetaZero.conjugatePartner rho)
      (by simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using hk)
      (by simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using hl) N)
      (norm_pairedEtaCurrent_lower_product_le_doubleDecay rho hk hl N))

/-- The actual shifted head and lower successor prefix retain two endpoint
decays and the head's original cutoff increment. -/
theorem norm_pairedEtaCurrent_head_product_le_doubleDecay (rho : NontrivialZetaZero) (N k : ℕ) {l : ℕ}
    (hl : l < analyticZetaZeroMultiplicity rho) :
    ‖pairedEtaHeadCompletedMoment rho N k‖ * ‖pairedEtaFiniteCompletedMoment rho (N + 2) l‖ ≤
      pairedEtaLogTailShiftIncrement (N + 1) *
        (pairedEtaCurrentMomentConstant rho ^ 2 * pairedEtaCurrentMomentDecay rho N ^ 2) := by
  have hQ := pairedEtaCurrentMomentConstant_nonneg rho
  have hd := (pairedEtaCurrentMomentDecay_bounds rho N).1
  have hdelta := (pairedEtaLogTailShiftIncrement_pos (N + 1)).le
  exact (mul_le_mul (norm_pairedEtaHeadCompletedMoment_le rho N k)
    (norm_pairedEtaFiniteCompletedMoment_lower_le rho hl N) (norm_nonneg _)
      (mul_nonneg (mul_nonneg hQ hdelta) hd)).trans_eq (by ring)

/-- The norm of the original complex head pair retains both completed decays. -/
theorem norm_pairedEtaHeadCompletedMomentPair_le_doubleDecay (rho : NontrivialZetaZero) (N k : ℕ) {l : ℕ}
    (hl : l < analyticZetaZeroMultiplicity rho) :
    ‖pairedEtaHeadCompletedMomentPair rho N k l‖ ≤
      pairedEtaLogTailShiftIncrement (N + 1) * pairedEtaCurrentDoubleDecayEnvelope rho N := by
  apply (norm_etaSignedCompletedPair_le _ _ _ _).trans
  exact (add_le_add (norm_pairedEtaCurrent_head_product_le_doubleDecay (NontrivialZetaZero.conjugatePartner rho) N k
    (by simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using hl))
    (norm_pairedEtaCurrent_head_product_le_doubleDecay rho N k hl)).trans_eq
      (by unfold pairedEtaCurrentDoubleDecayEnvelope; ring)

/-- The original current itself has a two-channel arithmetic decay bound
in both actual multiplicity branches. -/
theorem abs_pairedEtaLeadingCurrent_le_doubleDecay (rho : NontrivialZetaZero) (N : ℕ) :
    |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N| ≤
      2 * (analyticZetaZeroMultiplicity rho : ℝ) * pairedEtaLogTailShiftIncrement (N + 1) *
        pairedEtaCurrentDoubleDecayEnvelope rho N := by
  have hdelta := (pairedEtaLogTailShiftIncrement_pos (N + 1)).le
  have hE := pairedEtaCurrentDoubleDecayEnvelope_nonneg rho N
  by_cases hm : analyticZetaZeroMultiplicity rho = 1
  · rw [pairedEtaLeadingCurrent_eq_headCompletedMomentPair rho hm, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), hm, Nat.cast_one, mul_one]
    exact (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)).trans
      ((mul_le_mul_of_nonneg_left (norm_pairedEtaHeadCompletedMomentPair_le_doubleDecay rho N 0
        (analyticZetaZeroMultiplicity_positive rho)) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))
  · have hm2 : 2 ≤ analyticZetaZeroMultiplicity rho := by have := analyticZetaZeroMultiplicity_positive rho; omega
    rw [pairedEtaLeadingCurrent_eq_completedMomentPair rho hm2, abs_mul, abs_of_nonneg (by positivity)]
    have hpair := norm_pairedEtaFiniteCompletedMomentPair_le_doubleDecay rho
      (by omega : analyticZetaZeroMultiplicity rho - 2 < analyticZetaZeroMultiplicity rho)
      (by omega : analyticZetaZeroMultiplicity rho - 1 < analyticZetaZeroMultiplicity rho) N
    have hmle : ((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) ≤ (analyticZetaZeroMultiplicity rho : ℝ) :=
      by exact_mod_cast Nat.sub_le (analyticZetaZeroMultiplicity rho) 1
    calc
      _ ≤ 2 * (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
          pairedEtaCurrentDoubleDecayEnvelope rho N :=
        mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hpair) (by positivity)
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right hmle (show 0 ≤ 2 * pairedEtaLogTailShiftIncrement (N + 1) *
          pairedEtaCurrentDoubleDecayEnvelope rho N by positivity)
        nlinarith only [h]

/-- The odd-weighted original current is bounded by the two explicit
completed endpoint power channels, before summing the cutoff. -/
theorem pairedEtaLeadingCurrent_weighted_le_doubleDecay (rho : NontrivialZetaZero) (N : ℕ) :
    (2 * N + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N| ≤
      4 * (analyticZetaZeroMultiplicity rho : ℝ) * pairedEtaCurrentDoubleDecayEnvelope rho N := by
  have hE := pairedEtaCurrentDoubleDecayEnvelope_nonneg rho N
  calc
    _ ≤ (2 * N + 1 : ℝ) * (2 * (analyticZetaZeroMultiplicity rho : ℝ) * pairedEtaLogTailShiftIncrement (N + 1) *
        pairedEtaCurrentDoubleDecayEnvelope rho N) :=
      mul_le_mul_of_nonneg_left (abs_pairedEtaLeadingCurrent_le_doubleDecay rho N) (by positivity)
    _ = ((2 * N + 1 : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
        (2 * (analyticZetaZeroMultiplicity rho : ℝ) * pairedEtaCurrentDoubleDecayEnvelope rho N) := by ring
    _ ≤ 2 * (2 * (analyticZetaZeroMultiplicity rho : ℝ) * pairedEtaCurrentDoubleDecayEnvelope rho N) :=
      mul_le_mul_of_nonneg_right (pairedEtaCurrent_odd_weight_mul_shift_le_two N) (by positivity)
    _ = _ := by ring

/-- At a critical-line zero the two completed channels cancel in the
original real current, including the simple-zero head. -/
theorem pairedEtaLeadingCurrent_eq_zero_of_re_eq_half (rho : NontrivialZetaZero)
    (hrho : rho.1.re = 1 / 2) (N : ℕ) : pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N = 0 := by
  have hp := conjugatePartner_eq_self_of_re_eq_half rho hrho
  have hre (A B : ℂ) : (etaSignedCompletedPair A B A B).re = 0 := by
    simp only [etaSignedCompletedPair, Complex.sub_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  by_cases hm : analyticZetaZeroMultiplicity rho = 1
  · rw [pairedEtaLeadingCurrent_eq_headCompletedMomentPair rho hm]
    simp only [pairedEtaHeadCompletedMomentPair, hp, hre, mul_zero]
  · have hm2 : 2 ≤ analyticZetaZeroMultiplicity rho := by have := analyticZetaZeroMultiplicity_positive rho; omega
    rw [pairedEtaLeadingCurrent_eq_completedMomentPair rho hm2]
    simp only [pairedEtaFiniteCompletedMomentPair, hp, hre, mul_zero]

end

end RiemannGaussian
