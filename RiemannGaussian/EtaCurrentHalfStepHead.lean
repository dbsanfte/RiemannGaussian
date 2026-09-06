import RiemannGaussian.EtaCurrentHeadHalfWidth

/-!
# A common-endpoint expression for the original simple-zero head

The actual completed head is compared with half the complete logarithmic
step placed at the successor endpoint. Its exact complex defect retains
the head exponential variation, the support/gap width discrepancy, and
the endpoint translation. The defect gains two inverse-cutoff powers.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Half the actual logarithmic step at the successor completed endpoint. -/
def pairedEtaCurrentHalfStepHead (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  -(pairedEtaXiCompletionFactor rho.1 * rho.1) *
    Complex.exp (-rho.1 * (pairedEtaLogTailCutoff (N + 2) : ℂ)) *
      ((pairedEtaLogTailShiftIncrement (N + 1) / 2 : ℝ) : ℂ)

/-- All three signed complex contributions to the actual head defect
remain explicit before their norm estimate. -/
theorem pairedEtaHeadCompletedMoment_sub_halfStep (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaHeadCompletedMoment rho N 0 - pairedEtaCurrentHalfStepHead rho N =
      -(pairedEtaXiCompletionFactor rho.1 * rho.1) *
        Complex.exp (-rho.1 * (pairedEtaLogTailCutoff (N + 1) : ℂ)) *
          ((pairedEtaShiftedLogHeadLaplaceMoment 0 rho.1 (N + 1) - (pairedEtaShiftedLogHeadWidth (N + 1) : ℂ)) +
            ((pairedEtaShiftedLogHeadWidth (N + 1) - pairedEtaLogTailShiftIncrement (N + 1) / 2 : ℝ) : ℂ) +
              ((pairedEtaLogTailShiftIncrement (N + 1) / 2 : ℝ) : ℂ) *
                (1 - Complex.exp (-rho.1 * (pairedEtaLogTailShiftIncrement (N + 1) : ℂ)))) := by
  unfold pairedEtaHeadCompletedMoment pairedEtaLogLaplaceMomentCutoffCenteredHead pairedEtaCurrentHalfStepHead
  rw [← cexp_neg_mul_cutoff_mul_cexp_neg_mul_shiftIncrement rho.1 (N + 1)]
  push_cast
  ring

/-- The original head's endpoint exponential has exactly its actual
horizontal decay; its global ordinate phase is preserved upstream. -/
theorem norm_pairedEtaCurrent_old_cutoff_exp (rho : NontrivialZetaZero) (N : ℕ) :
    ‖Complex.exp (-rho.1 * (pairedEtaLogTailCutoff (N + 1) : ℂ))‖ = pairedEtaCurrentMomentDecay rho N := by
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  unfold pairedEtaLogTailCutoff pairedEtaCurrentMomentDecay
  rw [Real.rpow_def_of_pos (by positivity)]
  congr 1
  ring

/-- The explicit finite constant for the actual completed head replacement error. -/
def pairedEtaCurrentHalfStepHeadErrorConstant (rho : NontrivialZetaZero) : ℝ :=
  ‖pairedEtaXiCompletionFactor rho.1 * rho.1‖ * (2 * pairedEtaCurrentHeadVariationConstant rho + 1)

/-- The completed head replacement constant is nonnegative. -/
theorem pairedEtaCurrentHalfStepHeadErrorConstant_nonneg (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaCurrentHalfStepHeadErrorConstant rho := by
  have hK := pairedEtaCurrentHeadVariationConstant_nonneg rho
  unfold pairedEtaCurrentHalfStepHeadErrorConstant
  positivity

/-- The sum of the three retained head defects has an explicit quadratic
arithmetic bound at every cutoff. -/
theorem norm_pairedEtaCurrent_head_defects_le (rho : NontrivialZetaZero) (N : ℕ) :
    ‖(pairedEtaShiftedLogHeadLaplaceMoment 0 rho.1 (N + 1) - (pairedEtaShiftedLogHeadWidth (N + 1) : ℂ)) +
      ((pairedEtaShiftedLogHeadWidth (N + 1) - pairedEtaLogTailShiftIncrement (N + 1) / 2 : ℝ) : ℂ) +
        ((pairedEtaLogTailShiftIncrement (N + 1) / 2 : ℝ) : ℂ) *
          (1 - Complex.exp (-rho.1 * (pairedEtaLogTailShiftIncrement (N + 1) : ℂ)))‖ ≤
      (2 * pairedEtaCurrentHeadVariationConstant rho + 1) / (N + 1 : ℝ) ^ 2 := by
  have hK := pairedEtaCurrentHeadVariationConstant_nonneg rho
  have hd := (pairedEtaLogTailShiftIncrement_pos (N + 1)).le
  have hx : 0 < (N + 1 : ℝ) := by positivity
  have hd2 : pairedEtaLogTailShiftIncrement (N + 1) ^ 2 ≤ 1 / (N + 1 : ℝ) ^ 2 := by
    simpa only [div_pow, one_pow] using pow_le_pow_left₀ hd (pairedEtaLogTailShiftIncrement_succ_le N) 2
  have h1 := (norm_pairedEtaShiftedLogHeadLaplaceMoment_zero_sub_width_le rho N).trans
    (mul_le_mul_of_nonneg_left hd2 hK)
  have hw := pairedEtaShiftedLogHeadWidth_sub_half_step_bounds N
  have h2 : ‖((pairedEtaShiftedLogHeadWidth (N + 1) - pairedEtaLogTailShiftIncrement (N + 1) / 2 : ℝ) : ℂ)‖ ≤
      1 / (N + 1 : ℝ) ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw.1]
    apply hw.2.trans
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith [sq_nonneg (N + 1 : ℝ)])
  have h3 : ‖((pairedEtaLogTailShiftIncrement (N + 1) / 2 : ℝ) : ℂ) *
      (1 - Complex.exp (-rho.1 * (pairedEtaLogTailShiftIncrement (N + 1) : ℂ)))‖ ≤
        pairedEtaCurrentHeadVariationConstant rho * (1 / (N + 1 : ℝ) ^ 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_sub_rev]
    calc
      _ ≤ (pairedEtaLogTailShiftIncrement (N + 1) / 2) *
          (pairedEtaCurrentHeadVariationConstant rho * pairedEtaLogTailShiftIncrement (N + 1)) :=
        mul_le_mul_of_nonneg_left (norm_pairedEtaCurrent_head_exp_sub_one_le rho hd
          (pairedEtaLogTailShiftIncrement_succ_le_one N)) (by positivity)
      _ ≤ pairedEtaCurrentHeadVariationConstant rho * pairedEtaLogTailShiftIncrement (N + 1) ^ 2 := by
        nlinarith [mul_nonneg hK (sq_nonneg (pairedEtaLogTailShiftIncrement (N + 1)))]
      _ ≤ _ := mul_le_mul_of_nonneg_left hd2 hK
  calc
    _ ≤ (‖pairedEtaShiftedLogHeadLaplaceMoment 0 rho.1 (N + 1) - (pairedEtaShiftedLogHeadWidth (N + 1) : ℂ)‖ +
        ‖((pairedEtaShiftedLogHeadWidth (N + 1) - pairedEtaLogTailShiftIncrement (N + 1) / 2 : ℝ) : ℂ)‖) +
          ‖((pairedEtaLogTailShiftIncrement (N + 1) / 2 : ℝ) : ℂ) *
            (1 - Complex.exp (-rho.1 * (pairedEtaLogTailShiftIncrement (N + 1) : ℂ)))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (pairedEtaCurrentHeadVariationConstant rho * (1 / (N + 1 : ℝ) ^ 2) + 1 / (N + 1 : ℝ) ^ 2) +
        pairedEtaCurrentHeadVariationConstant rho * (1 / (N + 1 : ℝ) ^ 2) := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

/-- The actual completed simple-zero head differs from its common-endpoint
half-step expression by two inverse-cutoff powers and the true zero decay. -/
theorem norm_pairedEtaHeadCompletedMoment_sub_halfStep_le (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaHeadCompletedMoment rho N 0 - pairedEtaCurrentHalfStepHead rho N‖ ≤
      pairedEtaCurrentHalfStepHeadErrorConstant rho * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ) ^ 2 := by
  rw [pairedEtaHeadCompletedMoment_sub_halfStep, norm_mul, norm_mul, norm_neg, norm_pairedEtaCurrent_old_cutoff_exp]
  exact (mul_le_mul_of_nonneg_left (norm_pairedEtaCurrent_head_defects_le rho N)
    (mul_nonneg (norm_nonneg _) (pairedEtaCurrentMomentDecay_bounds rho N).1)).trans_eq
      (by unfold pairedEtaCurrentHalfStepHeadErrorConstant; ring)

/-- The common-endpoint half-step head is the original Euler zeroth moment
times the actual zero and the full logarithmic shift, as a complex identity. -/
theorem pairedEtaCurrentHalfStepHead_eq_eulerMoment (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCurrentHalfStepHead rho N = (pairedEtaLogTailShiftIncrement (N + 1) : ℂ) * rho.1 *
      pairedEtaCurrentEulerMoment rho N 0 := by
  unfold pairedEtaCurrentHalfStepHead pairedEtaCurrentEulerMoment pairedEtaCurrentEulerMomentValue
  simp only [Nat.factorial_zero, Nat.cast_one, zero_add, pow_one, one_mul]
  push_cast
  field_simp

end

end RiemannGaussian
