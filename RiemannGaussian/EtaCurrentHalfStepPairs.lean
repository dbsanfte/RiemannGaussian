import RiemannGaussian.EtaCurrentHalfStepHead

/-!
# Signed half-step endpoint pairs and their summable weighted error

The actual simple-zero head is replaced by its proved half-step endpoint
expression in both completion channels. The complex signed error remains
explicit. Its odd-weighted norm is summable, and the real leading pair has
two strictly positive coefficients with complementary horizontal decays.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The signed pair formed from the half-step heads and zeroth Euler moments. -/
def pairedEtaCurrentHalfStepHeadPair (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  etaSignedCompletedPair
    (pairedEtaCurrentHalfStepHead (NontrivialZetaZero.conjugatePartner rho) N)
    (pairedEtaCurrentEulerMoment (NontrivialZetaZero.conjugatePartner rho) N 0)
    (pairedEtaCurrentHalfStepHead rho N) (pairedEtaCurrentEulerMoment rho N 0)

/-- Both complex head defects retain the original signed orientation. -/
theorem pairedEtaCurrentEulerHeadPair_sub_halfStep (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCurrentEulerHeadPair rho N - pairedEtaCurrentHalfStepHeadPair rho N =
      etaSignedCompletedPair
        (pairedEtaHeadCompletedMoment (NontrivialZetaZero.conjugatePartner rho) N 0 -
          pairedEtaCurrentHalfStepHead (NontrivialZetaZero.conjugatePartner rho) N)
        (pairedEtaCurrentEulerMoment (NontrivialZetaZero.conjugatePartner rho) N 0)
        (pairedEtaHeadCompletedMoment rho N 0 - pairedEtaCurrentHalfStepHead rho N)
        (pairedEtaCurrentEulerMoment rho N 0) := by
  simp only [pairedEtaCurrentEulerHeadPair, pairedEtaCurrentHalfStepHeadPair,
    etaSignedCompletedPair, map_sub]
  ring

/-- The constant for one completed head-product defect. -/
def pairedEtaCurrentHalfStepPairErrorConstant (rho : NontrivialZetaZero) : ℝ :=
  pairedEtaCurrentHalfStepHeadErrorConstant rho * pairedEtaCurrentEulerMomentAmplitude rho 0

/-- The product-defect constant is nonnegative. -/
theorem pairedEtaCurrentHalfStepPairErrorConstant_nonneg (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaCurrentHalfStepPairErrorConstant rho := by
  have h := pairedEtaCurrentHalfStepHeadErrorConstant_nonneg rho
  unfold pairedEtaCurrentHalfStepPairErrorConstant pairedEtaCurrentEulerMomentAmplitude
  positivity

/-- One head-product defect keeps the extra two inverse-cutoff powers. -/
theorem norm_pairedEtaCurrent_halfStep_product_error_le (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaHeadCompletedMoment rho N 0 - pairedEtaCurrentHalfStepHead rho N‖ *
      ‖pairedEtaCurrentEulerMoment rho N 0‖ ≤
        pairedEtaCurrentHalfStepPairErrorConstant rho * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ) ^ 2 := by
  have ha : 0 ≤ pairedEtaCurrentEulerMomentAmplitude rho 0 := by
    unfold pairedEtaCurrentEulerMomentAmplitude
    positivity
  have hmodel : ‖pairedEtaCurrentEulerMoment rho N 0‖ ≤ pairedEtaCurrentEulerMomentAmplitude rho 0 :=
    (norm_pairedEtaCurrentEulerMoment_le rho N 0).trans
      (mul_le_of_le_one_right ha (pairedEtaCurrentMomentDecay_bounds rho N).2)
  have hD := pairedEtaCurrentHalfStepHeadErrorConstant_nonneg rho
  have hd := (pairedEtaCurrentMomentDecay_bounds rho N).1
  exact (mul_le_mul (norm_pairedEtaHeadCompletedMoment_sub_halfStep_le rho N) hmodel
    (norm_nonneg _) (by positivity)).trans_eq
      (by unfold pairedEtaCurrentHalfStepPairErrorConstant; ring)

/-- The complete signed pair error is bounded only after its two
complex head defects have been retained. -/
theorem norm_pairedEtaCurrentEulerHeadPair_sub_halfStep_le (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaCurrentEulerHeadPair rho N - pairedEtaCurrentHalfStepHeadPair rho N‖ ≤
      pairedEtaCurrentHalfStepPairErrorConstant (NontrivialZetaZero.conjugatePartner rho) *
          pairedEtaCurrentMomentDecay (NontrivialZetaZero.conjugatePartner rho) N / (N + 1 : ℝ) ^ 2 +
        pairedEtaCurrentHalfStepPairErrorConstant rho * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ) ^ 2 := by
  rw [pairedEtaCurrentEulerHeadPair_sub_halfStep]
  exact (norm_etaSignedCompletedPair_le _ _ _ _).trans
    (add_le_add (norm_pairedEtaCurrent_halfStep_product_error_le (NontrivialZetaZero.conjugatePartner rho) N)
      (norm_pairedEtaCurrent_halfStep_product_error_le rho N))

/-- The arithmetic summable envelope of the odd-weighted head correction. -/
def pairedEtaCurrentHalfStepErrorEnvelope (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  pairedEtaCurrentHalfStepPairErrorConstant (NontrivialZetaZero.conjugatePartner rho) *
      pairedEtaCurrentMomentDecay (NontrivialZetaZero.conjugatePartner rho) N / (N + 1 : ℝ) +
    pairedEtaCurrentHalfStepPairErrorConstant rho * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ)

/-- The head error envelope is nonnegative at every cutoff. -/
theorem pairedEtaCurrentHalfStepErrorEnvelope_nonneg (rho : NontrivialZetaZero) (N : ℕ) :
    0 ≤ pairedEtaCurrentHalfStepErrorEnvelope rho N := by
  have hp := pairedEtaCurrentHalfStepPairErrorConstant_nonneg (NontrivialZetaZero.conjugatePartner rho)
  have hr := pairedEtaCurrentHalfStepPairErrorConstant_nonneg rho
  have hdp := (pairedEtaCurrentMomentDecay_bounds (NontrivialZetaZero.conjugatePartner rho) N).1
  have hdr := (pairedEtaCurrentMomentDecay_bounds rho N).1
  unfold pairedEtaCurrentHalfStepErrorEnvelope
  positivity

/-- Both positive zero coordinates make the weighted head envelope summable. -/
theorem summable_pairedEtaCurrentHalfStepErrorEnvelope (rho : NontrivialZetaZero) :
    Summable (pairedEtaCurrentHalfStepErrorEnvelope rho) := by
  have hs (r : NontrivialZetaZero) : Summable (fun N : ℕ ↦ pairedEtaCurrentMomentDecay r N / (N + 1 : ℝ)) := by
    simpa only [pow_zero, one_mul] using summable_pairedEtaCurrent_logPower_mul_decay_div r 0
  change Summable (fun N ↦ pairedEtaCurrentHalfStepErrorEnvelope rho N)
  simpa only [pairedEtaCurrentHalfStepErrorEnvelope, mul_div_assoc] using
    ((hs (NontrivialZetaZero.conjugatePartner rho)).mul_left
      (pairedEtaCurrentHalfStepPairErrorConstant (NontrivialZetaZero.conjugatePartner rho))).add
        ((hs rho).mul_left (pairedEtaCurrentHalfStepPairErrorConstant rho))

/-- The original odd weight and the real-current factor are both included
in the summable head-error majorant. -/
theorem pairedEtaCurrentEulerHeadPair_weighted_halfStep_error_le (rho : NontrivialZetaZero) (N : ℕ) :
    (2 * N + 1 : ℝ) * |2 * (pairedEtaCurrentEulerHeadPair rho N).re - 2 * (pairedEtaCurrentHalfStepHeadPair rho N).re| ≤
      4 * pairedEtaCurrentHalfStepErrorEnvelope rho N := by
  have hreal : |2 * (pairedEtaCurrentEulerHeadPair rho N).re - 2 * (pairedEtaCurrentHalfStepHeadPair rho N).re| ≤
      2 * ‖pairedEtaCurrentEulerHeadPair rho N - pairedEtaCurrentHalfStepHeadPair rho N‖ := by
    rw [← mul_sub, ← Complex.sub_re, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
  have hx : 0 < (N + 1 : ℝ) := by positivity
  have hb := norm_pairedEtaCurrentEulerHeadPair_sub_halfStep_le rho N
  have hp := pairedEtaCurrentHalfStepPairErrorConstant_nonneg (NontrivialZetaZero.conjugatePartner rho)
  have hr := pairedEtaCurrentHalfStepPairErrorConstant_nonneg rho
  have hdp := (pairedEtaCurrentMomentDecay_bounds (NontrivialZetaZero.conjugatePartner rho) N).1
  have hdr := (pairedEtaCurrentMomentDecay_bounds rho N).1
  calc
    _ ≤ (2 * N + 1 : ℝ) * (2 * ‖pairedEtaCurrentEulerHeadPair rho N - pairedEtaCurrentHalfStepHeadPair rho N‖) :=
      mul_le_mul_of_nonneg_left hreal (by positivity)
    _ ≤ (2 * (N + 1 : ℝ)) * (2 *
        (pairedEtaCurrentHalfStepPairErrorConstant (NontrivialZetaZero.conjugatePartner rho) *
            pairedEtaCurrentMomentDecay (NontrivialZetaZero.conjugatePartner rho) N / (N + 1 : ℝ) ^ 2 +
          pairedEtaCurrentHalfStepPairErrorConstant rho * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ) ^ 2)) :=
      mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hb (by norm_num)) (by positivity) (by positivity)
    _ = _ := by unfold pairedEtaCurrentHalfStepErrorEnvelope; field_simp; ring

/-- The positive coefficient of one simple-zero principal endpoint channel. -/
def pairedEtaCurrentSimpleEndpointCoefficient (rho : NontrivialZetaZero) : ℝ :=
  2 * rho.1.re * Complex.normSq (pairedEtaXiCompletionFactor rho.1 * rho.1) *
    Complex.normSq (pairedEtaCurrentEulerMomentValue rho 0)

/-- The actual completion and Euler factors make each simple endpoint
coefficient strictly positive. -/
theorem pairedEtaCurrentSimpleEndpointCoefficient_pos (rho : NontrivialZetaZero) :
    0 < pairedEtaCurrentSimpleEndpointCoefficient rho := by
  have hr := NontrivialZetaZero.zero_lt_re rho
  have hc := Complex.normSq_pos.mpr (mul_ne_zero
    (pairedEtaXiCompletionFactor_ne_zero hr (NontrivialZetaZero.re_lt_one rho)) (NontrivialZetaZero.coe_ne_zero rho))
  have ha := Complex.normSq_pos.mpr (pairedEtaCurrentEulerMomentValue_ne_zero rho 0)
  unfold pairedEtaCurrentSimpleEndpointCoefficient
  positivity

/-- Common cutoff phase cancels in the complex half-step product before
the real signed endpoint current is taken. -/
theorem pairedEtaCurrentHalfStepHead_mul_conj_euler (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCurrentHalfStepHead rho N * starRingEnd ℂ (pairedEtaCurrentEulerMoment rho N 0) =
      ((pairedEtaLogTailShiftIncrement (N + 1) * Complex.normSq (pairedEtaXiCompletionFactor rho.1 * rho.1) *
        Complex.normSq (pairedEtaCurrentEulerMomentValue rho 0) *
          Real.exp (-2 * rho.1.re * pairedEtaLogTailCutoff (N + 2)) : ℝ) : ℂ) * rho.1 := by
  rw [pairedEtaCurrentHalfStepHead_eq_eulerMoment, mul_assoc, pairedEtaCurrentEulerMoment_mul_conj, Complex.mul_conj]
  push_cast
  ring

/-- The simple signed principal pair has the same complementary endpoint
decays as the repeated-zero branch, with two positive coefficients. -/
theorem pairedEtaCurrentHalfStepHeadPair_re (rho : NontrivialZetaZero) (N : ℕ) :
    2 * (pairedEtaCurrentHalfStepHeadPair rho N).re = pairedEtaLogTailShiftIncrement (N + 1) *
      (pairedEtaCurrentSimpleEndpointCoefficient (NontrivialZetaZero.conjugatePartner rho) *
          Real.exp (-2 * (NontrivialZetaZero.conjugatePartner rho).1.re * pairedEtaLogTailCutoff (N + 2)) -
        pairedEtaCurrentSimpleEndpointCoefficient rho * Real.exp (-2 * rho.1.re * pairedEtaLogTailCutoff (N + 2))) := by
  have he : pairedEtaCurrentHalfStepHeadPair rho N =
      pairedEtaCurrentHalfStepHead (NontrivialZetaZero.conjugatePartner rho) N *
          starRingEnd ℂ (pairedEtaCurrentEulerMoment (NontrivialZetaZero.conjugatePartner rho) N 0) -
        starRingEnd ℂ (pairedEtaCurrentHalfStepHead rho N * starRingEnd ℂ (pairedEtaCurrentEulerMoment rho N 0)) := by
    simp only [pairedEtaCurrentHalfStepHeadPair, etaSignedCompletedPair, map_mul, starRingEnd_apply, star_star]
  rw [he, pairedEtaCurrentHalfStepHead_mul_conj_euler, pairedEtaCurrentHalfStepHead_mul_conj_euler]
  simp only [Complex.sub_re, Complex.conj_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, pairedEtaCurrentSimpleEndpointCoefficient]
  ring

end

end RiemannGaussian
