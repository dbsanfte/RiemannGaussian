import RiemannGaussian.EtaMomentDivisorPhase
import RiemannGaussian.EtaCurrentHalfStepHead
import RiemannGaussian.EtaCurrentEulerPairs

/-!
# Reduction of the actual current factors to the complete zeroth moment

Every order below the actual zero multiplicity is a fixed complex multiple
of the original zeroth moment with an extra inverse-cutoff error. The
simple-zero head has the corresponding extra inverse-square error. Exact
complex defect identities precede the estimates, so the complete inverse
sum can retain its mixed cancellation when inserted into either branch.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The Euler terms have exactly the same complex ratios as the physical moment columns. -/
theorem pairedEtaCurrentEulerMoment_eq_coefficient_mul_zero
    (rho : NontrivialZetaZero) (N k : ℕ) :
    pairedEtaCurrentEulerMoment rho N k =
      pairedEtaMomentParityCoefficient rho k * pairedEtaCurrentEulerMoment rho N 0 := by
  simp only [pairedEtaCurrentEulerMoment, pairedEtaCurrentEulerMomentValue,
    pairedEtaMomentParityCoefficient_eq, Nat.factorial_zero, Nat.cast_one, pow_succ]
  field_simp [NontrivialZetaZero.coe_ne_zero rho]

/-- The actual lower-moment defect keeps both completed Euler errors with their complex coefficient. -/
theorem pairedEtaFiniteCompletedMoment_sub_coefficient_mul_zero
    (rho : NontrivialZetaZero) (N k : ℕ) :
    pairedEtaFiniteCompletedMoment rho (N + 2) k -
        pairedEtaMomentParityCoefficient rho k * pairedEtaFiniteCompletedMoment rho (N + 2) 0 =
      (pairedEtaFiniteCompletedMoment rho (N + 2) k - pairedEtaCurrentEulerMoment rho N k) -
        pairedEtaMomentParityCoefficient rho k *
          (pairedEtaFiniteCompletedMoment rho (N + 2) 0 - pairedEtaCurrentEulerMoment rho N 0) := by
  rw [pairedEtaCurrentEulerMoment_eq_coefficient_mul_zero rho N k]
  ring

/-- The explicit error coefficient for replacing a full moment by its actual zeroth moment. -/
def pairedEtaCurrentZeroMomentErrorConstant (rho : NontrivialZetaZero) (k : ℕ) : ℝ :=
  pairedEtaCurrentEulerMomentErrorConstant rho k +
    ‖pairedEtaMomentParityCoefficient rho k‖ * pairedEtaCurrentEulerMomentErrorConstant rho 0

/-- The moment transport constant is nonnegative. -/
theorem pairedEtaCurrentZeroMomentErrorConstant_nonneg (rho : NontrivialZetaZero) (k : ℕ) :
    0 ≤ pairedEtaCurrentZeroMomentErrorConstant rho k :=
  add_nonneg (pairedEtaCurrentEulerMomentErrorConstant_nonneg rho k)
    (mul_nonneg (norm_nonneg _) (pairedEtaCurrentEulerMomentErrorConstant_nonneg rho 0))

/-- Every actual lower moment reduces to the full zeroth moment with an extra inverse cutoff. -/
theorem norm_pairedEtaFiniteCompletedMoment_sub_coefficient_mul_zero_le
    (rho : NontrivialZetaZero) {k : ℕ} (hk : k < analyticZetaZeroMultiplicity rho) (N : ℕ) :
    ‖pairedEtaFiniteCompletedMoment rho (N + 2) k -
        pairedEtaMomentParityCoefficient rho k * pairedEtaFiniteCompletedMoment rho (N + 2) 0‖ ≤
      pairedEtaCurrentZeroMomentErrorConstant rho k * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ) := by
  rw [pairedEtaFiniteCompletedMoment_sub_coefficient_mul_zero]
  calc
    _ ≤ ‖pairedEtaFiniteCompletedMoment rho (N + 2) k - pairedEtaCurrentEulerMoment rho N k‖ +
        ‖pairedEtaMomentParityCoefficient rho k‖ *
          ‖pairedEtaFiniteCompletedMoment rho (N + 2) 0 - pairedEtaCurrentEulerMoment rho N 0‖ := by
      simpa only [norm_mul] using norm_sub_le
        (pairedEtaFiniteCompletedMoment rho (N + 2) k - pairedEtaCurrentEulerMoment rho N k)
        (pairedEtaMomentParityCoefficient rho k *
          (pairedEtaFiniteCompletedMoment rho (N + 2) 0 - pairedEtaCurrentEulerMoment rho N 0))
    _ ≤ pairedEtaCurrentEulerMomentErrorConstant rho k * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ) +
        ‖pairedEtaMomentParityCoefficient rho k‖ *
          (pairedEtaCurrentEulerMomentErrorConstant rho 0 * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ)) :=
      add_le_add (norm_pairedEtaFiniteCompletedMoment_sub_euler_le rho hk N)
        (mul_le_mul_of_nonneg_left (norm_pairedEtaFiniteCompletedMoment_sub_euler_le rho
          (analyticZetaZeroMultiplicity_positive rho) N) (norm_nonneg _))
    _ = _ := by unfold pairedEtaCurrentZeroMomentErrorConstant; ring

/-- The original head defect keeps its geometric half-step error and the actual zeroth-moment error. -/
theorem pairedEtaHeadCompletedMoment_sub_shift_mul_zero (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaHeadCompletedMoment rho N 0 -
        (pairedEtaLogTailShiftIncrement (N + 1) : ℂ) * rho.1 * pairedEtaFiniteCompletedMoment rho (N + 2) 0 =
      (pairedEtaHeadCompletedMoment rho N 0 - pairedEtaCurrentHalfStepHead rho N) -
        (pairedEtaLogTailShiftIncrement (N + 1) : ℂ) * rho.1 *
          (pairedEtaFiniteCompletedMoment rho (N + 2) 0 - pairedEtaCurrentEulerMoment rho N 0) := by
  rw [pairedEtaCurrentHalfStepHead_eq_eulerMoment]
  ring

/-- The explicit head transport coefficient retains both sources of its error. -/
def pairedEtaCurrentZeroHeadErrorConstant (rho : NontrivialZetaZero) : ℝ :=
  pairedEtaCurrentHalfStepHeadErrorConstant rho + ‖rho.1‖ * pairedEtaCurrentEulerMomentErrorConstant rho 0

/-- The head transport coefficient is nonnegative. -/
theorem pairedEtaCurrentZeroHeadErrorConstant_nonneg (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaCurrentZeroHeadErrorConstant rho :=
  add_nonneg (pairedEtaCurrentHalfStepHeadErrorConstant_nonneg rho)
    (mul_nonneg (norm_nonneg _) (pairedEtaCurrentEulerMomentErrorConstant_nonneg rho 0))

/-- The literal simple-zero head reduces to the actual zeroth moment with an inverse-square error. -/
theorem norm_pairedEtaHeadCompletedMoment_sub_shift_mul_zero_le
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaHeadCompletedMoment rho N 0 -
        (pairedEtaLogTailShiftIncrement (N + 1) : ℂ) * rho.1 * pairedEtaFiniteCompletedMoment rho (N + 2) 0‖ ≤
      pairedEtaCurrentZeroHeadErrorConstant rho * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ) ^ 2 := by
  have hδ := (pairedEtaLogTailShiftIncrement_pos (N + 1)).le
  have hE := pairedEtaCurrentEulerMomentErrorConstant_nonneg rho 0
  have hD := (pairedEtaCurrentMomentDecay_bounds rho N).1
  rw [pairedEtaHeadCompletedMoment_sub_shift_mul_zero]
  calc
    _ ≤ ‖pairedEtaHeadCompletedMoment rho N 0 - pairedEtaCurrentHalfStepHead rho N‖ +
        pairedEtaLogTailShiftIncrement (N + 1) * ‖rho.1‖ *
          ‖pairedEtaFiniteCompletedMoment rho (N + 2) 0 - pairedEtaCurrentEulerMoment rho N 0‖ := by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ] using
        norm_sub_le (pairedEtaHeadCompletedMoment rho N 0 - pairedEtaCurrentHalfStepHead rho N)
          ((pairedEtaLogTailShiftIncrement (N + 1) : ℂ) * rho.1 *
            (pairedEtaFiniteCompletedMoment rho (N + 2) 0 - pairedEtaCurrentEulerMoment rho N 0))
    _ ≤ pairedEtaCurrentHalfStepHeadErrorConstant rho * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ) ^ 2 +
        (1 / (N + 1 : ℝ)) * ‖rho.1‖ *
          (pairedEtaCurrentEulerMomentErrorConstant rho 0 * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ)) :=
      add_le_add (norm_pairedEtaHeadCompletedMoment_sub_halfStep_le rho N)
        (mul_le_mul (mul_le_mul_of_nonneg_right (pairedEtaLogTailShiftIncrement_succ_le N) (norm_nonneg _))
          (norm_pairedEtaFiniteCompletedMoment_sub_euler_le rho (analyticZetaZeroMultiplicity_positive rho) N)
          (norm_nonneg _) (by positivity))
    _ = _ := by unfold pairedEtaCurrentZeroHeadErrorConstant; field_simp

/-- The full complex product transport retains both actual zeroth-moment defects. -/
theorem pairedEtaFiniteCompletedMoment_product_sub_zero
    (rho : NontrivialZetaZero) (N k l : ℕ) :
    let F := pairedEtaFiniteCompletedMoment rho (N + 2)
    let a := pairedEtaMomentParityCoefficient rho
    F k * starRingEnd ℂ (F l) - a k * starRingEnd ℂ (a l) * (‖F 0‖ : ℂ) ^ 2 =
      (F k - a k * F 0) * starRingEnd ℂ (F l) +
        (a k * F 0) * starRingEnd ℂ (F l - a l * F 0) := by
  dsimp only
  rw [← Complex.mul_conj']
  simp only [map_sub, map_mul]
  ring

/-- One explicit constant controls both positions of the full-moment product transport. -/
def pairedEtaCurrentZeroPairErrorConstant (rho : NontrivialZetaZero) (k l : ℕ) : ℝ :=
  pairedEtaCurrentZeroMomentErrorConstant rho k * pairedEtaCurrentMomentConstant rho +
    ‖pairedEtaMomentParityCoefficient rho k‖ * pairedEtaCurrentMomentConstant rho *
      pairedEtaCurrentZeroMomentErrorConstant rho l

/-- Every full product transport coefficient is nonnegative. -/
theorem pairedEtaCurrentZeroPairErrorConstant_nonneg (rho : NontrivialZetaZero) (k l : ℕ) :
    0 ≤ pairedEtaCurrentZeroPairErrorConstant rho k l := by
  have hk := pairedEtaCurrentZeroMomentErrorConstant_nonneg rho k
  have hl := pairedEtaCurrentZeroMomentErrorConstant_nonneg rho l
  have hQ := pairedEtaCurrentMomentConstant_nonneg rho
  unfold pairedEtaCurrentZeroPairErrorConstant
  positivity

/-- Two original lower moments reduce to the full zeroth energy with an extra inverse-cutoff error. -/
theorem norm_pairedEtaFiniteCompletedMoment_product_sub_zero_le
    (rho : NontrivialZetaZero) {k l : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) (hl : l < analyticZetaZeroMultiplicity rho) (N : ℕ) :
    ‖pairedEtaFiniteCompletedMoment rho (N + 2) k * starRingEnd ℂ (pairedEtaFiniteCompletedMoment rho (N + 2) l) -
        pairedEtaMomentParityCoefficient rho k * starRingEnd ℂ (pairedEtaMomentParityCoefficient rho l) *
          (‖pairedEtaFiniteCompletedMoment rho (N + 2) 0‖ : ℂ) ^ 2‖ ≤
      pairedEtaCurrentZeroPairErrorConstant rho k l * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ) := by
  have hQ := pairedEtaCurrentMomentConstant_nonneg rho
  have hkE := pairedEtaCurrentZeroMomentErrorConstant_nonneg rho k
  have hD := (pairedEtaCurrentMomentDecay_bounds rho N).1
  rw [pairedEtaFiniteCompletedMoment_product_sub_zero]
  calc
    _ ≤ ‖pairedEtaFiniteCompletedMoment rho (N + 2) k -
          pairedEtaMomentParityCoefficient rho k * pairedEtaFiniteCompletedMoment rho (N + 2) 0‖ *
          ‖pairedEtaFiniteCompletedMoment rho (N + 2) l‖ +
        (‖pairedEtaMomentParityCoefficient rho k‖ * ‖pairedEtaFiniteCompletedMoment rho (N + 2) 0‖) *
          ‖pairedEtaFiniteCompletedMoment rho (N + 2) l -
            pairedEtaMomentParityCoefficient rho l * pairedEtaFiniteCompletedMoment rho (N + 2) 0‖ := by
      simpa only [norm_mul, norm_conj] using norm_add_le
        ((pairedEtaFiniteCompletedMoment rho (N + 2) k -
          pairedEtaMomentParityCoefficient rho k * pairedEtaFiniteCompletedMoment rho (N + 2) 0) *
          starRingEnd ℂ (pairedEtaFiniteCompletedMoment rho (N + 2) l))
        ((pairedEtaMomentParityCoefficient rho k * pairedEtaFiniteCompletedMoment rho (N + 2) 0) *
          starRingEnd ℂ (pairedEtaFiniteCompletedMoment rho (N + 2) l -
            pairedEtaMomentParityCoefficient rho l * pairedEtaFiniteCompletedMoment rho (N + 2) 0))
    _ ≤ (pairedEtaCurrentZeroMomentErrorConstant rho k * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ)) *
          pairedEtaCurrentMomentConstant rho +
        (‖pairedEtaMomentParityCoefficient rho k‖ * pairedEtaCurrentMomentConstant rho) *
          (pairedEtaCurrentZeroMomentErrorConstant rho l * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ)) :=
      add_le_add
        (mul_le_mul (norm_pairedEtaFiniteCompletedMoment_sub_coefficient_mul_zero_le rho hk N)
          (norm_pairedEtaFiniteCompletedMoment_le rho hl.le N) (norm_nonneg _) (by positivity))
        (mul_le_mul (mul_le_mul_of_nonneg_left (norm_pairedEtaFiniteCompletedMoment_le rho
          (analyticZetaZeroMultiplicity_positive rho).le N) (norm_nonneg _))
          (norm_pairedEtaFiniteCompletedMoment_sub_coefficient_mul_zero_le rho hl N) (norm_nonneg _) (by positivity))
    _ = _ := by unfold pairedEtaCurrentZeroPairErrorConstant; ring

end

end RiemannGaussian
