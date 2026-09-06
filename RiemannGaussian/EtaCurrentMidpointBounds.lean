import RiemannGaussian.EtaCurrentMomentBounds

/-!
# A zero-equation gain for the original midpoint coefficient

The exact finite arithmetic identities are bounded only after retaining
their signed reflection decomposition upstream. At least one lower-order
zero-tail factor remains in every finite pair. The actual shifted head
also retains one logarithmic increment. Both original multiplicity
branches consequently gain a decaying arithmetic endpoint factor.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The two actual completed endpoint decays controlling the midpoint arithmetic. -/
def pairedEtaCurrentMidpointEnvelope (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  pairedEtaCurrentMomentConstant (NontrivialZetaZero.conjugatePartner rho) ^ 2 *
      pairedEtaCurrentMomentDecay (NontrivialZetaZero.conjugatePartner rho) N +
    pairedEtaCurrentMomentConstant rho ^ 2 * pairedEtaCurrentMomentDecay rho N

/-- The completed midpoint envelope is nonnegative at every cutoff. -/
theorem pairedEtaCurrentMidpointEnvelope_nonneg (rho : NontrivialZetaZero) (N : ℕ) :
    0 ≤ pairedEtaCurrentMidpointEnvelope rho N :=
  add_nonneg (mul_nonneg (sq_nonneg _) (pairedEtaCurrentMomentDecay_bounds _ N).1)
    (mul_nonneg (sq_nonneg _) (pairedEtaCurrentMomentDecay_bounds rho N).1)

/-- Taking a norm of the retained complex signed pair gives its two product envelopes. -/
theorem norm_etaSignedCompletedPair_le (Ap Bp A B : ℂ) :
    ‖etaSignedCompletedPair Ap Bp A B‖ ≤ ‖Ap‖ * ‖Bp‖ + ‖A‖ * ‖B‖ := by
  simpa [etaSignedCompletedPair, norm_mul] using norm_sub_le
    (Ap * starRingEnd ℂ Bp) (starRingEnd ℂ A * B)

private theorem norm_finiteMoment_product_le (rho : NontrivialZetaZero) {k l : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) (hl : l ≤ analyticZetaZeroMultiplicity rho) (N : ℕ) :
    ‖pairedEtaFiniteCompletedMoment rho (N + 2) k‖ * ‖pairedEtaFiniteCompletedMoment rho (N + 2) l‖ ≤
      pairedEtaCurrentMomentConstant rho ^ 2 * pairedEtaCurrentMomentDecay rho N := by
  calc
    _ ≤ (pairedEtaCurrentMomentConstant rho * pairedEtaCurrentMomentDecay rho N) *
        pairedEtaCurrentMomentConstant rho :=
      mul_le_mul (norm_pairedEtaFiniteCompletedMoment_lower_le rho hk N)
        (norm_pairedEtaFiniteCompletedMoment_le rho hl N) (norm_nonneg _)
        (mul_nonneg (pairedEtaCurrentMomentConstant_nonneg rho) (pairedEtaCurrentMomentDecay_bounds rho N).1)
    _ = _ := by ring

/-- Every required finite pair retains one actual lower-order zero-tail decay. -/
theorem norm_pairedEtaFiniteCompletedMomentPair_le (rho : NontrivialZetaZero) {k l : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) (hl : l ≤ analyticZetaZeroMultiplicity rho) (N : ℕ) :
    ‖pairedEtaFiniteCompletedMomentPair rho (N + 2) k l‖ ≤ pairedEtaCurrentMidpointEnvelope rho N := by
  apply (norm_etaSignedCompletedPair_le _ _ _ _).trans
  exact add_le_add (norm_finiteMoment_product_le (NontrivialZetaZero.conjugatePartner rho)
    (by simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using hk)
    (by simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using hl) N)
    (norm_finiteMoment_product_le rho hk hl N)

private theorem norm_headMoment_product_le (rho : NontrivialZetaZero) (N k : ℕ) {l : ℕ}
    (hl : l ≤ analyticZetaZeroMultiplicity rho) :
    ‖pairedEtaHeadCompletedMoment rho N k‖ * ‖pairedEtaFiniteCompletedMoment rho (N + 2) l‖ ≤
      pairedEtaLogTailShiftIncrement (N + 1) *
        (pairedEtaCurrentMomentConstant rho ^ 2 * pairedEtaCurrentMomentDecay rho N) := by
  calc
    _ ≤ (pairedEtaCurrentMomentConstant rho * pairedEtaLogTailShiftIncrement (N + 1) *
        pairedEtaCurrentMomentDecay rho N) * pairedEtaCurrentMomentConstant rho :=
      mul_le_mul (norm_pairedEtaHeadCompletedMoment_le rho N k)
        (norm_pairedEtaFiniteCompletedMoment_le rho hl N) (norm_nonneg _)
        (mul_nonneg (mul_nonneg (pairedEtaCurrentMomentConstant_nonneg rho)
          (pairedEtaLogTailShiftIncrement_pos _).le) (pairedEtaCurrentMomentDecay_bounds rho N).1)
    _ = _ := by ring

/-- The actual head/prefix pair retains one cutoff increment and one endpoint decay. -/
theorem norm_pairedEtaHeadCompletedMomentPair_le (rho : NontrivialZetaZero) (N k : ℕ) {l : ℕ}
    (hl : l ≤ analyticZetaZeroMultiplicity rho) :
    ‖pairedEtaHeadCompletedMomentPair rho N k l‖ ≤
      pairedEtaLogTailShiftIncrement (N + 1) * pairedEtaCurrentMidpointEnvelope rho N := by
  apply (norm_etaSignedCompletedPair_le _ _ _ _).trans
  exact (add_le_add (norm_headMoment_product_le (NontrivialZetaZero.conjugatePartner rho) N k
    (by simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using hl))
    (norm_headMoment_product_le rho N k hl)).trans_eq (by unfold pairedEtaCurrentMidpointEnvelope; ring)

/-- The actual simple-zero midpoint moment gains a decaying arithmetic endpoint factor. -/
theorem abs_pairedEtaLeadingCurrentMidpointMoment_head_le (rho : NontrivialZetaZero)
    (hm : analyticZetaZeroMultiplicity rho = 1) (N : ℕ) :
    |pairedEtaLeadingCurrentMidpointMoment rho N| ≤
      2 * pairedEtaLogTailShiftIncrement (N + 1) * (1 + pairedEtaLogTailCutoff (N + 2)) *
        pairedEtaCurrentMidpointEnvelope rho N := by
  have hd := (pairedEtaLogTailShiftIncrement_pos (N + 1)).le
  have hL := pairedEtaLogTailCutoff_nonneg (N + 2)
  have hL₀ := pairedEtaLogTailCutoff_nonneg (N + 1)
  have hE := pairedEtaCurrentMidpointEnvelope_nonneg rho N
  have hcenter : (pairedEtaLogTailCutoff (N + 1) + pairedEtaLogTailCutoff (N + 2)) / 2 ≤
      pairedEtaLogTailCutoff (N + 2) := by
    have hstep : pairedEtaLogTailCutoff (N + 1) ≤ pairedEtaLogTailCutoff (N + 2) := by
      unfold pairedEtaLogTailCutoff
      apply Real.log_le_log (by positivity)
      exact_mod_cast (show 2 * (N + 1) + 1 ≤ 2 * (N + 2) + 1 by omega)
    linarith
  have h₀ := (Complex.abs_re_le_norm (pairedEtaHeadCompletedMomentPair rho N 0 0)).trans
    (norm_pairedEtaHeadCompletedMomentPair_le rho N 0 (by omega : 0 ≤ analyticZetaZeroMultiplicity rho))
  have h₁ := (Complex.abs_re_le_norm (pairedEtaHeadCompletedMomentPair rho N 1 0)).trans
    (norm_pairedEtaHeadCompletedMomentPair_le rho N 1 (by omega : 0 ≤ analyticZetaZeroMultiplicity rho))
  have h₂ := (Complex.abs_re_le_norm (pairedEtaHeadCompletedMomentPair rho N 0 1)).trans
    (norm_pairedEtaHeadCompletedMomentPair_le rho N 0 (by omega : 1 ≤ analyticZetaZeroMultiplicity rho))
  have hJ : |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N| ≤
      2 * (pairedEtaLogTailShiftIncrement (N + 1) * pairedEtaCurrentMidpointEnvelope rho N) := by
    rw [pairedEtaLeadingCurrent_eq_headCompletedMomentPair rho hm, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left h₀ (by norm_num)
  rw [pairedEtaLeadingCurrentMidpointMoment_eq_head_arithmetic rho hm]
  calc
    _ ≤ |((pairedEtaLogTailCutoff (N + 1) + pairedEtaLogTailCutoff (N + 2)) / 2) *
          pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N| +
        |(pairedEtaHeadCompletedMomentPair rho N 1 0).re| + |(pairedEtaHeadCompletedMomentPair rho N 0 1).re| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = ((pairedEtaLogTailCutoff (N + 1) + pairedEtaLogTailCutoff (N + 2)) / 2) *
          |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N| +
        |(pairedEtaHeadCompletedMomentPair rho N 1 0).re| + |(pairedEtaHeadCompletedMomentPair rho N 0 1).re| := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (pairedEtaLogTailCutoff (N + 1) + pairedEtaLogTailCutoff (N + 2)) / 2)]
    _ ≤ pairedEtaLogTailCutoff (N + 2) *
          (2 * (pairedEtaLogTailShiftIncrement (N + 1) * pairedEtaCurrentMidpointEnvelope rho N)) +
        pairedEtaLogTailShiftIncrement (N + 1) * pairedEtaCurrentMidpointEnvelope rho N +
          pairedEtaLogTailShiftIncrement (N + 1) * pairedEtaCurrentMidpointEnvelope rho N :=
      add_le_add (add_le_add (mul_le_mul hcenter hJ (abs_nonneg _) hL) h₁) h₂
    _ = _ := by ring

/-- The actual repeated-zero midpoint moment gains a decaying arithmetic
endpoint factor while retaining its exact multiplicity and increment. -/
theorem abs_pairedEtaLeadingCurrentMidpointMoment_adjacent_le (rho : NontrivialZetaZero)
    (hm : 2 ≤ analyticZetaZeroMultiplicity rho) (N : ℕ) :
    |pairedEtaLeadingCurrentMidpointMoment rho N| ≤
      2 * ((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1) *
        (1 + pairedEtaLogTailCutoff (N + 2)) * pairedEtaCurrentMidpointEnvelope rho N := by
  have hd := (pairedEtaLogTailShiftIncrement_pos (N + 1)).le
  have hL := pairedEtaLogTailCutoff_nonneg (N + 2)
  have hE := pairedEtaCurrentMidpointEnvelope_nonneg rho N
  have h₀ := (Complex.abs_re_le_norm (pairedEtaFiniteCompletedMomentPair rho (N + 2)
    (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1))).trans
      (norm_pairedEtaFiniteCompletedMomentPair_le rho (by omega) (by omega) N)
  have h₁ := (Complex.abs_re_le_norm (pairedEtaFiniteCompletedMomentPair rho (N + 2)
    (analyticZetaZeroMultiplicity rho - 1) (analyticZetaZeroMultiplicity rho - 1))).trans
      (norm_pairedEtaFiniteCompletedMomentPair_le rho (by omega) (by omega) N)
  have h₂ := (Complex.abs_re_le_norm (pairedEtaFiniteCompletedMomentPair rho (N + 2)
    (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho))).trans
      (norm_pairedEtaFiniteCompletedMomentPair_le rho (by omega) le_rfl N)
  have hJ : |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N| ≤
      2 * (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
        pairedEtaCurrentMidpointEnvelope rho N := by
    rw [pairedEtaLeadingCurrent_eq_completedMomentPair rho hm, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ 2 * (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) *
        pairedEtaLogTailShiftIncrement (N + 1)))]
    exact mul_le_mul_of_nonneg_left h₀ (by positivity)
  rw [pairedEtaLeadingCurrentMidpointMoment_eq_adjacent_arithmetic rho hm]
  calc
    _ ≤ |pairedEtaLogTailCutoff (N + 2) * pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N| +
        |(((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
          ((pairedEtaFiniteCompletedMomentPair rho (N + 2)
              (analyticZetaZeroMultiplicity rho - 1) (analyticZetaZeroMultiplicity rho - 1)).re +
            (pairedEtaFiniteCompletedMomentPair rho (N + 2)
              (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho)).re)| := abs_add_le _ _
    _ ≤ pairedEtaLogTailCutoff (N + 2) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N| +
        (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
          (|(pairedEtaFiniteCompletedMomentPair rho (N + 2)
              (analyticZetaZeroMultiplicity rho - 1) (analyticZetaZeroMultiplicity rho - 1)).re| +
            |(pairedEtaFiniteCompletedMomentPair rho (N + 2)
              (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho)).re|) := by
      rw [abs_mul, abs_of_nonneg hL, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ ((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1))]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity))
    _ ≤ pairedEtaLogTailCutoff (N + 2) *
          (2 * (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
            pairedEtaCurrentMidpointEnvelope rho N) +
        (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
          (pairedEtaCurrentMidpointEnvelope rho N + pairedEtaCurrentMidpointEnvelope rho N) :=
      add_le_add (mul_le_mul_of_nonneg_left hJ hL)
        (mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by positivity))
    _ = _ := by ring

/-- Both actual midpoint coefficients have an explicit arithmetic endpoint
gain over the absolute kernel-mass envelope, at every cutoff and zero. -/
theorem abs_pairedEtaLeadingCurrentMidpointMoment_le_arithmetic (rho : NontrivialZetaZero) (N : ℕ) :
    |pairedEtaLeadingCurrentMidpointMoment rho N| ≤
      2 * (analyticZetaZeroMultiplicity rho : ℝ) * (1 + pairedEtaLogTailCutoff (N + 2)) /
        (N + 1 : ℝ) * pairedEtaCurrentMidpointEnvelope rho N := by
  have hd := (pairedEtaLogTailShiftIncrement_pos (N + 1)).le
  have hL := pairedEtaLogTailCutoff_nonneg (N + 2)
  have hE := pairedEtaCurrentMidpointEnvelope_nonneg rho N
  have hb : |pairedEtaLeadingCurrentMidpointMoment rho N| ≤
      2 * (analyticZetaZeroMultiplicity rho : ℝ) * pairedEtaLogTailShiftIncrement (N + 1) *
        (1 + pairedEtaLogTailCutoff (N + 2)) * pairedEtaCurrentMidpointEnvelope rho N := by
    by_cases hm : analyticZetaZeroMultiplicity rho = 1
    · simpa only [hm, Nat.cast_one, mul_one] using abs_pairedEtaLeadingCurrentMidpointMoment_head_le rho hm N
    · have hm₂ : 2 ≤ analyticZetaZeroMultiplicity rho := by have := analyticZetaZeroMultiplicity_positive rho; omega
      apply (abs_pairedEtaLeadingCurrentMidpointMoment_adjacent_le rho hm₂ N).trans
      gcongr
      exact_mod_cast Nat.sub_le (analyticZetaZeroMultiplicity rho) 1
  apply hb.trans
  calc
    _ ≤ 2 * (analyticZetaZeroMultiplicity rho : ℝ) * (1 / (N + 1 : ℝ)) *
        (1 + pairedEtaLogTailCutoff (N + 2)) * pairedEtaCurrentMidpointEnvelope rho N := by
      gcongr
      exact pairedEtaLogTailShiftIncrement_succ_le N
    _ = _ := by ring

end

end RiemannGaussian
