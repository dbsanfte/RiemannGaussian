import RiemannGaussian.EtaMoebiusParityRecurrence
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaCompletionReflectionHighOrdinateRigidity

/-!
# Uniform bounds for the complete Möbius parity aggregates

The exact dyadic recurrence controls the entire growing divisor family.
Its complex multiplier has norm strictly below one at every actual zero.
The resulting constants are independent of the physical cutoff; no sum of
individual divisor errors or fixed-divisor limiting argument is used.
These are bounds for the arithmetic aggregates, not for the original
current's weighted absolute return.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- One explicit constant for every cutoff of the complete odd aggregate,
including the initial cutoff and the source of the recurrence. -/
def pairedEtaCompletedMoebiusParityConstant (rho : NontrivialZetaZero) : ℝ :=
  ‖pairedEtaXiCompletionFactor rho.1‖ +
    ‖pairedEtaCompletedMoebiusSource rho‖ / (1 - ‖(2 : ℂ) ^ (-rho.1)‖)

/-- The parity constant is nonnegative. -/
theorem pairedEtaCompletedMoebiusParityConstant_nonneg (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaCompletedMoebiusParityConstant rho := by
  have hden := sub_pos.mpr (norm_two_cpow_neg_lt_one (NontrivialZetaZero.zero_lt_re rho))
  unfold pairedEtaCompletedMoebiusParityConstant
  positivity

/-- The explicit constant contains the actual cutoff-one value. -/
theorem norm_pairedEtaXiCompletionFactor_le_parityConstant (rho : NontrivialZetaZero) :
    ‖pairedEtaXiCompletionFactor rho.1‖ ≤ pairedEtaCompletedMoebiusParityConstant rho := by
  have hden := sub_pos.mpr (norm_two_cpow_neg_lt_one (NontrivialZetaZero.zero_lt_re rho))
  unfold pairedEtaCompletedMoebiusParityConstant
  exact le_add_of_nonneg_right (div_nonneg (norm_nonneg _) hden.le)

/-- The explicit constant is preserved by the norm recurrence. -/
theorem pairedEtaCompletedMoebiusParityConstant_recurrence_le (rho : NontrivialZetaZero) :
    ‖pairedEtaCompletedMoebiusSource rho‖ +
      ‖(2 : ℂ) ^ (-rho.1)‖ * pairedEtaCompletedMoebiusParityConstant rho ≤
        pairedEtaCompletedMoebiusParityConstant rho := by
  have hr := norm_two_cpow_neg_lt_one (NontrivialZetaZero.zero_lt_re rho)
  have hden : 0 < 1 - ‖(2 : ℂ) ^ (-rho.1)‖ := sub_pos.mpr hr
  have hcancel := div_mul_cancel₀ ‖pairedEtaCompletedMoebiusSource rho‖ hden.ne'
  have hX := norm_nonneg (pairedEtaXiCompletionFactor rho.1)
  unfold pairedEtaCompletedMoebiusParityConstant
  nlinarith

/-- The complete odd Möbius aggregate is bounded uniformly over every
physical cutoff, despite the increasing number of divisors. -/
theorem norm_pairedEtaCompletedMoebiusOddAggregate_le (rho : NontrivialZetaZero) (M : ℕ) :
    ‖pairedEtaCompletedMoebiusOddAggregate rho M‖ ≤
      pairedEtaCompletedMoebiusParityConstant rho := by
  induction M using Nat.strong_induction_on with
  | h M ih =>
    by_cases hM : 2 ≤ M
    · rw [pairedEtaCompletedMoebiusOddAggregate_recurrence rho hM]
      calc
        _ ≤ ‖pairedEtaCompletedMoebiusSource rho‖ +
            ‖(2 : ℂ) ^ (-rho.1) * pairedEtaCompletedMoebiusOddAggregate rho (M / 2)‖ :=
          norm_add_le _ _
        _ ≤ ‖pairedEtaCompletedMoebiusSource rho‖ +
            ‖(2 : ℂ) ^ (-rho.1)‖ * pairedEtaCompletedMoebiusParityConstant rho := by
          rw [norm_mul]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (ih (M / 2) (Nat.div_lt_self (by omega) (by omega))) (norm_nonneg _))
        _ ≤ _ := pairedEtaCompletedMoebiusParityConstant_recurrence_le rho
    · interval_cases M
      · simpa only [pairedEtaCompletedMoebiusOddAggregate_zero, norm_zero] using
          pairedEtaCompletedMoebiusParityConstant_nonneg rho
      · simpa only [pairedEtaCompletedMoebiusOddAggregate_one] using
          norm_pairedEtaXiCompletionFactor_le_parityConstant rho

/-- The complete even Möbius aggregate has a uniform bound with the
additional exact dyadic contraction factor. -/
theorem norm_pairedEtaCompletedMoebiusEvenAggregate_le (rho : NontrivialZetaZero) (M : ℕ) :
    ‖pairedEtaCompletedMoebiusEvenAggregate rho M‖ ≤
      ‖(2 : ℂ) ^ (-rho.1)‖ * pairedEtaCompletedMoebiusParityConstant rho := by
  rw [pairedEtaCompletedMoebiusEvenAggregate_eq_half_odd, norm_mul, norm_neg]
  exact mul_le_mul_of_nonneg_left (norm_pairedEtaCompletedMoebiusOddAggregate_le rho (M / 2))
    (norm_nonneg _)

end

end RiemannGaussian
