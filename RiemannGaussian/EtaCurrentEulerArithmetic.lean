import RiemannGaussian.EtaCurrentEulerPairs

/-!
# Elementary endpoint arithmetic of the Euler current

The simple-zero head evaluates exactly as two endpoint exponentials.
In the adjacent Euler product the shared ordinate phase cancels exactly
at the complex level. Its remaining real coefficient is strictly positive.
These identities identify the contribution that an independent return
bound must control; no vanishing estimate is inferred from phase removal.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The actual completed order-zero head in elementary endpoint arithmetic. -/
theorem pairedEtaHeadCompletedMoment_zero_eq_endpoints (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaHeadCompletedMoment rho N 0 = pairedEtaXiCompletionFactor rho.1 *
      (Complex.exp (-rho.1 * (Real.log (((2 * (N + 1) + 2 : ℕ) : ℝ)) : ℂ)) -
        Complex.exp (-rho.1 * (pairedEtaLogTailCutoff (N + 1) : ℂ))) := by
  have hs := NontrivialZetaZero.coe_ne_zero rho
  have hw := (pairedEtaShiftedLogHeadWidth_pos (N + 1)).le
  have he : Complex.exp (-rho.1 * (pairedEtaLogTailCutoff (N + 1) : ℂ)) *
      Complex.exp (-rho.1 * (pairedEtaShiftedLogHeadWidth (N + 1) : ℂ)) =
      Complex.exp (-rho.1 * (Real.log (((2 * (N + 1) + 2 : ℕ) : ℝ)) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    unfold pairedEtaShiftedLogHeadWidth
    push_cast
    ring
  unfold pairedEtaHeadCompletedMoment pairedEtaLogLaplaceMomentCutoffCenteredHead pairedEtaShiftedLogHeadLaplaceMoment
  simp only [pow_zero, one_mul]
  rw [pairedEtaShiftedLogHeadMeasure_eq_restrict_Ioc, ← intervalIntegral.integral_of_le hw,
    integral_exp_mul_complex (neg_ne_zero.mpr hs)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  calc
    _ = pairedEtaXiCompletionFactor rho.1 *
        (Complex.exp (-rho.1 * (pairedEtaLogTailCutoff (N + 1) : ℂ)) *
          Complex.exp (-rho.1 * (pairedEtaShiftedLogHeadWidth (N + 1) : ℂ)) -
            Complex.exp (-rho.1 * (pairedEtaLogTailCutoff (N + 1) : ℂ))) := by field_simp
    _ = _ := by rw [he]

/-- The full complex endpoint product loses its common ordinate phase
by an exact identity, leaving a positive horizontal scale and the two
evaluated moment constants. -/
theorem pairedEtaCurrentEulerMoment_mul_conj (rho : NontrivialZetaZero) (N k l : ℕ) :
    pairedEtaCurrentEulerMoment rho N k * starRingEnd ℂ (pairedEtaCurrentEulerMoment rho N l) =
      ((Complex.normSq (pairedEtaXiCompletionFactor rho.1 * rho.1) *
        Real.exp (-2 * rho.1.re * pairedEtaLogTailCutoff (N + 2)) : ℝ) : ℂ) *
          (pairedEtaCurrentEulerMomentValue rho k * starRingEnd ℂ (pairedEtaCurrentEulerMomentValue rho l)) := by
  let c : ℂ := -(pairedEtaXiCompletionFactor rho.1 * rho.1) *
    Complex.exp (-rho.1 * (pairedEtaLogTailCutoff (N + 2) : ℂ))
  have hn : Complex.normSq c = Complex.normSq (pairedEtaXiCompletionFactor rho.1 * rho.1) *
      Real.exp (-2 * rho.1.re * pairedEtaLogTailCutoff (N + 2)) := by
    simp only [c, map_mul, Complex.normSq_neg]
    congr 1
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, pow_two, ← Real.exp_add]
    congr 1
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  change (c * pairedEtaCurrentEulerMomentValue rho k) *
    starRingEnd ℂ (c * pairedEtaCurrentEulerMomentValue rho l) = _
  rw [map_mul]
  calc
    _ = (c * starRingEnd ℂ c) *
        (pairedEtaCurrentEulerMomentValue rho k * starRingEnd ℂ (pairedEtaCurrentEulerMomentValue rho l)) := by ring
    _ = _ := by rw [Complex.mul_conj, hn]

/-- Adjacent evaluated moments obey the exact factorial-over-zero recurrence. -/
theorem pairedEtaCurrentEulerMomentValue_succ (rho : NontrivialZetaZero) (k : ℕ) :
    pairedEtaCurrentEulerMomentValue rho (k + 1) =
      ((k + 1 : ℕ) : ℂ) * pairedEtaCurrentEulerMomentValue rho k * rho.1⁻¹ := by
  unfold pairedEtaCurrentEulerMomentValue
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ, mul_inv_rev]
  ring

/-- The evaluated Euler moment is nonzero at every actual nontrivial zero. -/
theorem pairedEtaCurrentEulerMomentValue_ne_zero (rho : NontrivialZetaZero) (k : ℕ) :
    pairedEtaCurrentEulerMomentValue rho k ≠ 0 := by
  unfold pairedEtaCurrentEulerMomentValue
  exact div_ne_zero (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero k)
    (inv_ne_zero (pow_ne_zero _ (NontrivialZetaZero.coe_ne_zero rho)))) (by norm_num)

/-- The real adjacent Euler coefficient is evaluated as a strictly
positive multiple of a nonzero moment norm square. -/
theorem pairedEtaCurrentEuler_adjacent_coefficient (rho : NontrivialZetaZero) (k : ℕ) :
    (pairedEtaCurrentEulerMomentValue rho k * starRingEnd ℂ (pairedEtaCurrentEulerMomentValue rho (k + 1))).re =
      ((k + 1 : ℝ) * rho.1.re / Complex.normSq rho.1) * Complex.normSq (pairedEtaCurrentEulerMomentValue rho k) := by
  rw [pairedEtaCurrentEulerMomentValue_succ, map_mul, map_mul, map_natCast]
  have he : pairedEtaCurrentEulerMomentValue rho k *
      (((k + 1 : ℕ) : ℂ) * starRingEnd ℂ (pairedEtaCurrentEulerMomentValue rho k) * starRingEnd ℂ rho.1⁻¹) =
      (((k + 1 : ℝ) * Complex.normSq (pairedEtaCurrentEulerMomentValue rho k) : ℝ) : ℂ) *
        starRingEnd ℂ rho.1⁻¹ := by
    rw [Complex.ofReal_mul, ← Complex.mul_conj]
    push_cast
    ring
  rw [he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.conj_re, Complex.inv_re]
  ring

/-- Each separate completed adjacent Euler channel has positive real
coefficient; its leading contribution carries no cutoff Fourier oscillation. -/
theorem pairedEtaCurrentEuler_adjacent_coefficient_pos (rho : NontrivialZetaZero) (k : ℕ) :
    0 < (pairedEtaCurrentEulerMomentValue rho k * starRingEnd ℂ (pairedEtaCurrentEulerMomentValue rho (k + 1))).re := by
  rw [pairedEtaCurrentEuler_adjacent_coefficient]
  exact mul_pos (div_pos (mul_pos (by positivity) (NontrivialZetaZero.zero_lt_re rho))
    (Complex.normSq_pos.mpr (NontrivialZetaZero.coe_ne_zero rho)))
      (Complex.normSq_pos.mpr (pairedEtaCurrentEulerMomentValue_ne_zero rho k))

/-- The positive completion-weighted coefficient of one adjacent Euler channel. -/
def pairedEtaCurrentEulerAdjacentCoefficient (rho : NontrivialZetaZero) (k : ℕ) : ℝ :=
  Complex.normSq (pairedEtaXiCompletionFactor rho.1 * rho.1) *
    (pairedEtaCurrentEulerMomentValue rho k * starRingEnd ℂ (pairedEtaCurrentEulerMomentValue rho (k + 1))).re

/-- The completion factor cannot remove the positive adjacent Euler coefficient. -/
theorem pairedEtaCurrentEulerAdjacentCoefficient_pos (rho : NontrivialZetaZero) (k : ℕ) :
    0 < pairedEtaCurrentEulerAdjacentCoefficient rho k :=
  mul_pos (Complex.normSq_pos.mpr (mul_ne_zero
    (pairedEtaXiCompletionFactor_ne_zero (NontrivialZetaZero.zero_lt_re rho) (NontrivialZetaZero.re_lt_one rho))
    (NontrivialZetaZero.coe_ne_zero rho))) (pairedEtaCurrentEuler_adjacent_coefficient_pos rho k)

/-- The real adjacent Euler pair is exactly the signed difference of
two positive coefficients with complementary horizontal decay rates. -/
theorem pairedEtaCurrentEulerMomentPair_adjacent_re (rho : NontrivialZetaZero) (N k : ℕ) :
    (pairedEtaCurrentEulerMomentPair rho N k (k + 1)).re =
      pairedEtaCurrentEulerAdjacentCoefficient (NontrivialZetaZero.conjugatePartner rho) k *
          Real.exp (-2 * (NontrivialZetaZero.conjugatePartner rho).1.re * pairedEtaLogTailCutoff (N + 2)) -
        pairedEtaCurrentEulerAdjacentCoefficient rho k *
          Real.exp (-2 * rho.1.re * pairedEtaLogTailCutoff (N + 2)) := by
  have he : pairedEtaCurrentEulerMomentPair rho N k (k + 1) =
      pairedEtaCurrentEulerMoment (NontrivialZetaZero.conjugatePartner rho) N k *
          starRingEnd ℂ (pairedEtaCurrentEulerMoment (NontrivialZetaZero.conjugatePartner rho) N (k + 1)) -
        starRingEnd ℂ (pairedEtaCurrentEulerMoment rho N k *
          starRingEnd ℂ (pairedEtaCurrentEulerMoment rho N (k + 1))) := by
    simp only [pairedEtaCurrentEulerMomentPair, etaSignedCompletedPair, map_mul, starRingEnd_apply, star_star]
  rw [he, pairedEtaCurrentEulerMoment_mul_conj, pairedEtaCurrentEulerMoment_mul_conj]
  simp only [Complex.sub_re, Complex.conj_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, pairedEtaCurrentEulerAdjacentCoefficient]
  ring

end

end RiemannGaussian
