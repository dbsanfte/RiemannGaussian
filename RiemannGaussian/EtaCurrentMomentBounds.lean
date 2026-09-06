import RiemannGaussian.EtaCurrentMidpointReflection

/-!
# Arithmetic bounds for the finite moments in the midpoint coefficient

The actual zero equation bounds every order below multiplicity by its
centered tail. The exact multiplicity order is bounded using its nonzero
full moment. A single explicit constant controls both cases, while the
negative head retains its cutoff increment and endpoint decay.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- A finite explicit constant for all actual completed moments through
the exact multiplicity, including the nonzero leading moment. -/
def pairedEtaCurrentMomentConstant (rho : NontrivialZetaZero) : ℝ :=
  ‖pairedEtaXiCompletionFactor rho.1 * rho.1‖ + ‖pairedEtaCompletedLeadingMoment rho‖ +
    ‖pairedEtaXiCompletionFactor rho.1 * rho.1‖ *
      ((analyticZetaZeroMultiplicity rho).factorial : ℝ) / rho.1.re ^ (analyticZetaZeroMultiplicity rho + 1)

/-- The actual successor odd-endpoint decay of one completed zero channel. -/
def pairedEtaCurrentMomentDecay (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  (((2 * (N + 1) + 1 : ℕ) : ℝ) ^ (-rho.1.re))

/-- The arithmetic endpoint decay is positive and at most one. -/
theorem pairedEtaCurrentMomentDecay_bounds (rho : NontrivialZetaZero) (N : ℕ) :
    0 ≤ pairedEtaCurrentMomentDecay rho N ∧ pairedEtaCurrentMomentDecay rho N ≤ 1 := by
  constructor
  · exact Real.rpow_nonneg (by positivity) _
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (show 1 ≤ 2 * (N + 1) + 1 by omega))
      (neg_nonpos.mpr (NontrivialZetaZero.zero_lt_re rho).le)

/-- The explicit moment constant is nonnegative. -/
theorem pairedEtaCurrentMomentConstant_nonneg (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaCurrentMomentConstant rho := by
  have hs := NontrivialZetaZero.zero_lt_re rho
  unfold pairedEtaCurrentMomentConstant
  positivity

/-- The moment constant includes the literal completion amplitude. -/
theorem norm_completion_le_pairedEtaCurrentMomentConstant (rho : NontrivialZetaZero) :
    ‖pairedEtaXiCompletionFactor rho.1 * rho.1‖ ≤ pairedEtaCurrentMomentConstant rho := by
  have hs := NontrivialZetaZero.zero_lt_re rho
  unfold pairedEtaCurrentMomentConstant
  have ht : 0 ≤ ‖pairedEtaXiCompletionFactor rho.1 * rho.1‖ *
      ((analyticZetaZeroMultiplicity rho).factorial : ℝ) / rho.1.re ^ (analyticZetaZeroMultiplicity rho + 1) := by positivity
  linarith [norm_nonneg (pairedEtaCompletedLeadingMoment rho)]

/-- The factorial tail constant increases with order inside the actual critical strip. -/
theorem etaMoment_factorial_constant_le (rho : NontrivialZetaZero) {k : ℕ}
    (hk : k ≤ analyticZetaZeroMultiplicity rho) :
    (k.factorial : ℝ) / rho.1.re ^ (k + 1) ≤
      ((analyticZetaZeroMultiplicity rho).factorial : ℝ) / rho.1.re ^ (analyticZetaZeroMultiplicity rho + 1) := by
  have hs := NontrivialZetaZero.zero_lt_re rho
  calc
    _ ≤ ((analyticZetaZeroMultiplicity rho).factorial : ℝ) / rho.1.re ^ (k + 1) :=
      div_le_div_of_nonneg_right (by exact_mod_cast Nat.factorial_le hk) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_of_le_one hs.le (NontrivialZetaZero.re_lt_one rho).le (by omega))

/-- Every factorial tail amplitude through multiplicity is included in the explicit constant. -/
theorem etaMoment_completed_factorial_le (rho : NontrivialZetaZero) {k : ℕ}
    (hk : k ≤ analyticZetaZeroMultiplicity rho) :
    ‖pairedEtaXiCompletionFactor rho.1 * rho.1‖ * ((k.factorial : ℝ) / rho.1.re ^ (k + 1)) ≤
      pairedEtaCurrentMomentConstant rho := by
  apply (mul_le_mul_of_nonneg_left (etaMoment_factorial_constant_le rho hk) (norm_nonneg _)).trans
  unfold pairedEtaCurrentMomentConstant
  rw [mul_div_assoc]
  linarith [norm_nonneg (pairedEtaXiCompletionFactor rho.1 * rho.1), norm_nonneg (pairedEtaCompletedLeadingMoment rho)]

/-- The actual zero equation supplies endpoint decay for every lower finite completed moment. -/
theorem norm_pairedEtaFiniteCompletedMoment_lower_le (rho : NontrivialZetaZero) {k : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) (N : ℕ) :
    ‖pairedEtaFiniteCompletedMoment rho (N + 2) k‖ ≤
      pairedEtaCurrentMomentConstant rho * pairedEtaCurrentMomentDecay rho N := by
  unfold pairedEtaFiniteCompletedMoment
  rw [norm_mul]
  calc
    _ ≤ ‖pairedEtaXiCompletionFactor rho.1 * rho.1‖ *
        (((k.factorial : ℝ) / rho.1.re ^ (k + 1)) * pairedEtaCurrentMomentDecay rho N) :=
      mul_le_mul_of_nonneg_left (norm_pairedEtaLogLaplaceMomentCutoffCenteredPartialSum_le_oddEndpoint_rpow
        rho hk (N + 1)) (norm_nonneg _)
    _ = (‖pairedEtaXiCompletionFactor rho.1 * rho.1‖ * ((k.factorial : ℝ) / rho.1.re ^ (k + 1))) *
        pairedEtaCurrentMomentDecay rho N := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (etaMoment_completed_factorial_le rho hk.le)
      (pairedEtaCurrentMomentDecay_bounds rho N).1

/-- At the exact multiplicity the finite completed moment is uniformly
bounded by its full nonzero moment and the genuine centered-tail bound. -/
theorem norm_pairedEtaFiniteCompletedMoment_top_le (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaFiniteCompletedMoment rho (N + 2) (analyticZetaZeroMultiplicity rho)‖ ≤
      pairedEtaCurrentMomentConstant rho := by
  have hs := NontrivialZetaZero.zero_lt_re rho
  have ht : ‖pairedEtaCompletedMomentTail rho (N + 2) (analyticZetaZeroMultiplicity rho)‖ ≤
      ‖pairedEtaXiCompletionFactor rho.1 * rho.1‖ *
        (((analyticZetaZeroMultiplicity rho).factorial : ℝ) / rho.1.re ^ (analyticZetaZeroMultiplicity rho + 1)) := by
    unfold pairedEtaCompletedMomentTail
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (norm_pairedEtaLogLaplaceMomentCutoffCenteredTail_le (analyticZetaZeroMultiplicity rho) hs (N + 2)).trans
    rw [pairedEtaLogLaplaceMomentCenteredTailUpper_eq_rpow]
    exact mul_le_of_le_one_left (by positivity)
      (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (show 1 ≤ 2 * (N + 2) + 1 by omega))
        (neg_nonpos.mpr hs.le))
  rw [pairedEtaFiniteCompletedMoment_top_eq_sub_tail]
  calc
    _ ≤ ‖pairedEtaCompletedLeadingMoment rho‖ +
        ‖pairedEtaCompletedMomentTail rho (N + 2) (analyticZetaZeroMultiplicity rho)‖ := norm_sub_le _ _
    _ ≤ _ := by
      unfold pairedEtaCurrentMomentConstant
      rw [← mul_div_assoc] at ht
      linarith [norm_nonneg (pairedEtaXiCompletionFactor rho.1 * rho.1)]

/-- Every finite completed moment through multiplicity has the same explicit uniform bound. -/
theorem norm_pairedEtaFiniteCompletedMoment_le (rho : NontrivialZetaZero) {k : ℕ}
    (hk : k ≤ analyticZetaZeroMultiplicity rho) (N : ℕ) :
    ‖pairedEtaFiniteCompletedMoment rho (N + 2) k‖ ≤ pairedEtaCurrentMomentConstant rho := by
  rcases lt_or_eq_of_le hk with hk | hk
  · exact (norm_pairedEtaFiniteCompletedMoment_lower_le rho hk N).trans
      (mul_le_of_le_one_right (pairedEtaCurrentMomentConstant_nonneg rho) (pairedEtaCurrentMomentDecay_bounds rho N).2)
  · rw [hk]
    exact norm_pairedEtaFiniteCompletedMoment_top_le rho N

/-- The actual successor cutoff increment is at most one. -/
theorem pairedEtaLogTailShiftIncrement_succ_le_one (N : ℕ) :
    pairedEtaLogTailShiftIncrement (N + 1) ≤ 1 := by
  apply (pairedEtaLogTailShiftIncrement_succ_le N).trans
  exact (div_le_one (by positivity : (0 : ℝ) < N + 1)).2 (by have := Nat.cast_nonneg (α := ℝ) N; linarith)

/-- Every shifted head order retains one actual increment and one endpoint
decay, with the literal completion amplitude bounded explicitly. -/
theorem norm_pairedEtaHeadCompletedMoment_le (rho : NontrivialZetaZero) (N k : ℕ) :
    ‖pairedEtaHeadCompletedMoment rho N k‖ ≤
      pairedEtaCurrentMomentConstant rho * pairedEtaLogTailShiftIncrement (N + 1) * pairedEtaCurrentMomentDecay rho N := by
  have hd := (pairedEtaLogTailShiftIncrement_pos (N + 1)).le
  have hp : pairedEtaLogTailShiftIncrement (N + 1) ^ (k + 1) ≤ pairedEtaLogTailShiftIncrement (N + 1) := by
    simpa only [pow_one] using pow_le_pow_of_le_one hd (pairedEtaLogTailShiftIncrement_succ_le_one N)
      (show 1 ≤ k + 1 by omega)
  unfold pairedEtaHeadCompletedMoment
  rw [norm_mul, norm_neg]
  calc
    _ ≤ ‖pairedEtaXiCompletionFactor rho.1 * rho.1‖ *
        (pairedEtaCurrentMomentDecay rho N * pairedEtaLogTailShiftIncrement (N + 1) ^ (k + 1)) :=
      mul_le_mul_of_nonneg_left (norm_pairedEtaLogLaplaceMomentCutoffCenteredHead_le k
        (NontrivialZetaZero.zero_lt_re rho) (N + 1)) (norm_nonneg _)
    _ ≤ pairedEtaCurrentMomentConstant rho *
        (pairedEtaCurrentMomentDecay rho N * pairedEtaLogTailShiftIncrement (N + 1)) :=
      mul_le_mul (norm_completion_le_pairedEtaCurrentMomentConstant rho)
        (mul_le_mul_of_nonneg_left hp (pairedEtaCurrentMomentDecay_bounds rho N).1)
        (mul_nonneg (pairedEtaCurrentMomentDecay_bounds rho N).1 (pow_nonneg hd _))
        (pairedEtaCurrentMomentConstant_nonneg rho)
    _ = _ := by ring

end

end RiemannGaussian
