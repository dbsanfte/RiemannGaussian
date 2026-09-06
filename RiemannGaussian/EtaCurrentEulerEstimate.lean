import RiemannGaussian.EtaCurrentEulerArithmetic
import RiemannGaussian.EtaCurrentLinearHeatReconstruction

/-!
# An arithmetic Euler estimate for the original signed current and return

Both actual multiplicity branches differ from explicit completed endpoint
expressions by a summable odd-weighted error. The estimate is on the
unchanged current and, through the checked heat reconstruction, on its
actual linear-width return. The endpoint expression is not asserted to
have a finite first absolute moment.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The explicit Euler expression for the original multiplicity-selected
current. The head is evaluated by `pairedEtaHeadCompletedMoment_zero_eq_endpoints`. -/
def pairedEtaCurrentEulerExpression (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  if analyticZetaZeroMultiplicity rho = 1 then 2 * (pairedEtaCurrentEulerHeadPair rho N).re
  else 2 * (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
    (pairedEtaCurrentEulerMomentPair rho N (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1)).re

/-- At a repeated zero the explicit current term is a signed difference
of two nonoscillatory positive-coefficient endpoint decays, with the
original multiplicity and cutoff increment retained. -/
theorem pairedEtaCurrentEulerExpression_eq_adjacent_endpoints (rho : NontrivialZetaZero)
    (hm : 2 ≤ analyticZetaZeroMultiplicity rho) (N : ℕ) :
    pairedEtaCurrentEulerExpression rho N =
      2 * (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
        (pairedEtaCurrentEulerAdjacentCoefficient (NontrivialZetaZero.conjugatePartner rho)
            (analyticZetaZeroMultiplicity rho - 2) *
              Real.exp (-2 * (NontrivialZetaZero.conjugatePartner rho).1.re * pairedEtaLogTailCutoff (N + 2)) -
          pairedEtaCurrentEulerAdjacentCoefficient rho (analyticZetaZeroMultiplicity rho - 2) *
              Real.exp (-2 * rho.1.re * pairedEtaLogTailCutoff (N + 2))) := by
  rw [pairedEtaCurrentEulerExpression, if_neg (show analyticZetaZeroMultiplicity rho ≠ 1 by omega),
    show analyticZetaZeroMultiplicity rho - 1 = analyticZetaZeroMultiplicity rho - 2 + 1 by omega,
    pairedEtaCurrentEulerMomentPair_adjacent_re]

/-- The explicit summable envelope of the signed arithmetic Euler error,
before its external cutoff increment and odd weight are applied. -/
def pairedEtaCurrentEulerErrorEnvelope (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  if analyticZetaZeroMultiplicity rho = 1 then
    pairedEtaCurrentMomentConstant (NontrivialZetaZero.conjugatePartner rho) *
        pairedEtaCurrentEulerMomentErrorConstant (NontrivialZetaZero.conjugatePartner rho) 0 *
        pairedEtaCurrentMomentDecay (NontrivialZetaZero.conjugatePartner rho) N / (N + 1 : ℝ) +
      pairedEtaCurrentMomentConstant rho * pairedEtaCurrentEulerMomentErrorConstant rho 0 *
        pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ)
  else ((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) *
    (pairedEtaCurrentEulerPairErrorConstant (NontrivialZetaZero.conjugatePartner rho)
        (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1) *
        pairedEtaCurrentMomentDecay (NontrivialZetaZero.conjugatePartner rho) N / (N + 1 : ℝ) +
      pairedEtaCurrentEulerPairErrorConstant rho (analyticZetaZeroMultiplicity rho - 2)
        (analyticZetaZeroMultiplicity rho - 1) * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ))

/-- The signed arithmetic error envelope is nonnegative at every cutoff. -/
theorem pairedEtaCurrentEulerErrorEnvelope_nonneg (rho : NontrivialZetaZero) (N : ℕ) :
    0 ≤ pairedEtaCurrentEulerErrorEnvelope rho N := by
  have hQ := pairedEtaCurrentMomentConstant_nonneg rho
  have hQp := pairedEtaCurrentMomentConstant_nonneg (NontrivialZetaZero.conjugatePartner rho)
  have hD := pairedEtaCurrentEulerMomentErrorConstant_nonneg rho 0
  have hDp := pairedEtaCurrentEulerMomentErrorConstant_nonneg (NontrivialZetaZero.conjugatePartner rho) 0
  have hd := (pairedEtaCurrentMomentDecay_bounds rho N).1
  have hdp := (pairedEtaCurrentMomentDecay_bounds (NontrivialZetaZero.conjugatePartner rho) N).1
  have hC := pairedEtaCurrentEulerPairErrorConstant_nonneg rho
    (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1)
  have hCp := pairedEtaCurrentEulerPairErrorConstant_nonneg (NontrivialZetaZero.conjugatePartner rho)
    (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1)
  unfold pairedEtaCurrentEulerErrorEnvelope
  split <;> positivity

/-- The original signed current has an explicit Euler error with the
actual logarithmic shift retained, in both multiplicity branches. -/
theorem abs_pairedEtaLeadingCurrent_sub_euler_le (rho : NontrivialZetaZero) (N : ℕ) :
    |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N - pairedEtaCurrentEulerExpression rho N| ≤
      2 * pairedEtaLogTailShiftIncrement (N + 1) * pairedEtaCurrentEulerErrorEnvelope rho N := by
  have hd := (pairedEtaLogTailShiftIncrement_pos (N + 1)).le
  by_cases hm : analyticZetaZeroMultiplicity rho = 1
  · rw [pairedEtaCurrentEulerExpression, if_pos hm, pairedEtaLeadingCurrent_eq_headCompletedMomentPair rho hm,
      ← mul_sub, ← Complex.sub_re, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ ≤ 2 * ‖pairedEtaHeadCompletedMomentPair rho N 0 0 - pairedEtaCurrentEulerHeadPair rho N‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left (norm_pairedEtaHeadCompletedMomentPair_sub_euler_le rho N)
          (by norm_num : (0 : ℝ) ≤ 2)
        simpa only [pairedEtaCurrentEulerErrorEnvelope, if_pos hm, mul_assoc] using h
  · have hm2 : 2 ≤ analyticZetaZeroMultiplicity rho := by have := analyticZetaZeroMultiplicity_positive rho; omega
    rw [pairedEtaCurrentEulerExpression, if_neg hm, pairedEtaLeadingCurrent_eq_completedMomentPair rho hm2,
      ← mul_sub, ← Complex.sub_re, abs_mul, abs_of_nonneg (by positivity)]
    calc
      _ ≤ 2 * (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
          ‖pairedEtaFiniteCompletedMomentPair rho (N + 2) (analyticZetaZeroMultiplicity rho - 2)
              (analyticZetaZeroMultiplicity rho - 1) - pairedEtaCurrentEulerMomentPair rho N
                (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1)‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left
          (norm_pairedEtaFiniteCompletedMomentPair_sub_euler_le rho (by omega : analyticZetaZeroMultiplicity rho - 2 < _)
            (by omega : analyticZetaZeroMultiplicity rho - 1 < _) N)
          (by positivity : 0 ≤ 2 * (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)))
        unfold pairedEtaCurrentEulerErrorEnvelope
        rw [if_neg hm]
        exact h.trans_eq (by ring)

/-- The original odd endpoint weight absorbs one actual successor cutoff shift. -/
theorem pairedEtaCurrent_odd_weight_mul_shift_le_two (N : ℕ) :
    (2 * N + 1 : ℝ) * pairedEtaLogTailShiftIncrement (N + 1) ≤ 2 := by
  calc
    _ ≤ (2 * N + 1 : ℝ) * (1 / (N + 1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (pairedEtaLogTailShiftIncrement_succ_le N) (by positivity)
    _ ≤ 2 := by
      rw [mul_one_div]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < N + 1)).2
      linarith

/-- The unchanged current's weighted Euler error has a fully explicit
summable arithmetic majorant at every cutoff. -/
theorem pairedEtaLeadingCurrent_weighted_euler_error_le (rho : NontrivialZetaZero) (N : ℕ) :
    (2 * N + 1 : ℝ) * |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N - pairedEtaCurrentEulerExpression rho N| ≤
      4 * pairedEtaCurrentEulerErrorEnvelope rho N := by
  have hB := pairedEtaCurrentEulerErrorEnvelope_nonneg rho N
  calc
    _ ≤ (2 * N + 1 : ℝ) * (2 * pairedEtaLogTailShiftIncrement (N + 1) * pairedEtaCurrentEulerErrorEnvelope rho N) :=
      mul_le_mul_of_nonneg_left (abs_pairedEtaLeadingCurrent_sub_euler_le rho N) (by positivity)
    _ = ((2 * N + 1 : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) * (2 * pairedEtaCurrentEulerErrorEnvelope rho N) := by ring
    _ ≤ 2 * (2 * pairedEtaCurrentEulerErrorEnvelope rho N) :=
      mul_le_mul_of_nonneg_right (pairedEtaCurrent_odd_weight_mul_shift_le_two N) (by positivity)
    _ = _ := by ring

/-- Both completed Euler error envelopes are genuinely summable for every actual zero. -/
theorem summable_pairedEtaCurrentEulerErrorEnvelope (rho : NontrivialZetaZero) :
    Summable (pairedEtaCurrentEulerErrorEnvelope rho) := by
  have hs (z : NontrivialZetaZero) : Summable (fun N : ℕ ↦ pairedEtaCurrentMomentDecay z N / (N + 1 : ℝ)) := by
    simpa only [pow_zero, one_mul] using summable_pairedEtaCurrent_logPower_mul_decay_div z 0
  change Summable (fun N ↦ pairedEtaCurrentEulerErrorEnvelope rho N)
  by_cases hm : analyticZetaZeroMultiplicity rho = 1
  · simpa only [pairedEtaCurrentEulerErrorEnvelope, if_pos hm, mul_div_assoc] using
      ((hs (NontrivialZetaZero.conjugatePartner rho)).mul_left
        (pairedEtaCurrentMomentConstant (NontrivialZetaZero.conjugatePartner rho) *
          pairedEtaCurrentEulerMomentErrorConstant (NontrivialZetaZero.conjugatePartner rho) 0)).add
      ((hs rho).mul_left (pairedEtaCurrentMomentConstant rho * pairedEtaCurrentEulerMomentErrorConstant rho 0))
  · simpa only [pairedEtaCurrentEulerErrorEnvelope, if_neg hm, mul_div_assoc] using
      (((hs (NontrivialZetaZero.conjugatePartner rho)).mul_left
        (pairedEtaCurrentEulerPairErrorConstant (NontrivialZetaZero.conjugatePartner rho)
          (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1))).add
      ((hs rho).mul_left (pairedEtaCurrentEulerPairErrorConstant rho
        (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1)))).mul_left
          (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ))

/-- The original leading current differs from its elementary Euler expression
by a genuinely summable odd-weighted absolute error. -/
theorem summable_oddEndpoint_mul_abs_pairedEtaLeadingCurrent_euler_error (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦ (2 * N + 1 : ℝ) *
      |pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N - pairedEtaCurrentEulerExpression rho N|) :=
  ((summable_pairedEtaCurrentEulerErrorEnvelope rho).mul_left 4).of_nonneg_of_le
    (fun N ↦ by positivity) (pairedEtaLeadingCurrent_weighted_euler_error_le rho)

/-- The actual linear-width return has a summable error from the same
explicit signed Euler expression, with both arithmetic and heat budgets retained. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_weighted_euler_error_le (rho : NontrivialZetaZero) (N : ℕ) :
    (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N - (pairedEtaCurrentEulerExpression rho N : ℂ)‖ ≤
      pairedEtaCurrentLinearHeatErrorMajorant rho N + 4 * pairedEtaCurrentEulerErrorEnvelope rho N := by
  have ht := norm_sub_le_norm_sub_add_norm_sub (pairedEtaLeadingCurrentLinearHeatReturn rho N)
    (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ) (pairedEtaCurrentEulerExpression rho N : ℂ)
  have h := mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ) ≤ 2 * N + 1)
  rw [mul_add] at h
  simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  exact h.trans (add_le_add (pairedEtaLeadingCurrentLinearHeatReturn_weighted_error_le rho N)
    (pairedEtaLeadingCurrent_weighted_euler_error_le rho N))

/-- The original return's complete weighted Euler error is absolutely summable. -/
theorem summable_oddEndpoint_mul_norm_pairedEtaLeadingCurrentLinearHeatReturn_euler_error (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦ (2 * N + 1 : ℝ) *
      ‖pairedEtaLeadingCurrentLinearHeatReturn rho N - (pairedEtaCurrentEulerExpression rho N : ℂ)‖) :=
  ((summable_pairedEtaCurrentLinearHeatErrorMajorant rho).add
    ((summable_pairedEtaCurrentEulerErrorEnvelope rho).mul_left 4)).of_nonneg_of_le
      (fun N ↦ by positivity) (pairedEtaLeadingCurrentLinearHeatReturn_weighted_euler_error_le rho)

/-- Every finite return error sum lies below the same explicitly defined
finite majorant sum; the endpoint expression itself is left unbounded. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_euler_error_sum_le (rho : NontrivialZetaZero) (K : ℕ) :
    (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) *
      ‖pairedEtaLeadingCurrentLinearHeatReturn rho N - (pairedEtaCurrentEulerExpression rho N : ℂ)‖) ≤
        ∑' N : ℕ, (pairedEtaCurrentLinearHeatErrorMajorant rho N + 4 * pairedEtaCurrentEulerErrorEnvelope rho N) := by
  calc
    _ ≤ ∑ N ∈ Finset.range K, (pairedEtaCurrentLinearHeatErrorMajorant rho N + 4 * pairedEtaCurrentEulerErrorEnvelope rho N) :=
      Finset.sum_le_sum (fun N _ ↦ pairedEtaLeadingCurrentLinearHeatReturn_weighted_euler_error_le rho N)
    _ ≤ _ := ((summable_pairedEtaCurrentLinearHeatErrorMajorant rho).add
      ((summable_pairedEtaCurrentEulerErrorEnvelope rho).mul_left 4)).sum_le_tsum _ (fun N _ ↦
        add_nonneg (pairedEtaCurrentLinearHeatErrorMajorant_nonneg rho N)
          (mul_nonneg (by norm_num) (pairedEtaCurrentEulerErrorEnvelope_nonneg rho N)))

end

end RiemannGaussian
