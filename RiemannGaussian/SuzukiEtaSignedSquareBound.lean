/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaPhaseEnergy
import RiemannGaussian.SuzukiEtaPhaseContours

/-!
# An independent upper bound for the signed eta derivative remainder

Completing a complex square controls the signed eta/derivative plus
Archimedean numerator by the true carrier denominator squared. No lower
bound on that denominator is needed. On favorable dyadic strip phases,
the corresponding quotient is at most `1/(2*log 2)`, uniformly in the
eta truncation. The exact weighted square identity retains arbitrary
complex weights; its upper bound requires a positive signed dyadic
coefficient. The full carrier still has its separate quadratic energy.
-/

open Complex
namespace RiemannGaussian
noncomputable section

/-- The full complex eta/derivative numerator before subtracting the
dyadic completion contribution. Its real part is the signed remainder
in the finite carrier energy decomposition. -/
def suzukiEtaFiniteCompletedNumerator (N : ℕ) (s : ℂ) : ℂ :=
  pairedEtaCorePartialSum N s * starRingEnd ℂ
    (pairedEtaCoreDerivativePartialSum N s +
      (1 + suzukiChebyshevMellinCompletedCorrection s) * pairedEtaCorePartialSum N s)

/-- The signed dyadic coefficient associated with an arbitrary complex
test. Its positivity is a condition to prove, not part of its definition. -/
def suzukiEtaDyadicWeightCoefficient (B s : ℂ) : ℝ :=
  -(B * starRingEnd ℂ (pairedEtaFactorLogDerivative s)).re

/-- The rich numerator's real part is exactly the scalar signed
eta/derivative plus Archimedean expression already used in the carrier. -/
theorem suzukiEtaFiniteCompletedNumerator_re (N : ℕ) (s : ℂ) :
    (suzukiEtaFiniteCompletedNumerator N s).re =
      (pairedEtaCorePartialSum N s * starRingEnd ℂ (pairedEtaCoreDerivativePartialSum N s)).re +
        (1 + (suzukiChebyshevMellinCompletedCorrection s).re) * normSq (pairedEtaCorePartialSum N s) := by
  simp only [suzukiEtaFiniteCompletedNumerator, map_add, map_mul, mul_re, mul_im,
    conj_re, conj_im, add_re, add_im, one_re, one_im, normSq_apply]
  ring

/-- The complete weighted carrier splits into its signed arithmetic
quotient and its exact signed dyadic multiple of carrier energy. -/
theorem im_mul_suzukiEtaFiniteCarrier_eq_completed_add_energy (B : ℂ) (N : ℕ) (s : ℂ) :
    (B * suzukiEtaFiniteCarrier N s).im =
      (B * suzukiEtaFiniteCompletedNumerator N s).re / normSq (suzukiEtaFiniteCarrierDenominator N s) +
        suzukiEtaDyadicWeightCoefficient B s * normSq (suzukiEtaFiniteCarrier N s) := by
  rw [im_mul_suzukiEtaFiniteCarrier, normSq_suzukiEtaFiniteCarrier]
  have he : (B * pairedEtaCorePartialSum N s * starRingEnd ℂ (suzukiEtaFiniteCarrierDenominator N s)).re =
      (B * suzukiEtaFiniteCompletedNumerator N s).re +
        suzukiEtaDyadicWeightCoefficient B s * normSq (pairedEtaCorePartialSum N s) := by
    unfold suzukiEtaFiniteCarrierDenominator suzukiEtaFiniteCompletedNumerator suzukiEtaDyadicWeightCoefficient
    rw [pairedEtaArithmeticXiRegularCorrection_eq_completed_sub_dyadic]
    simp only [map_add, map_sub, map_mul, mul_re, mul_im, conj_re, conj_im,
      add_re, add_im, sub_re, sub_im, one_re, one_im, normSq_apply]
    ring
  rw [he]
  ring

private lemma complex_square_identity (B e p f : ℂ) :
    normSq B * normSq (p + f * e) -
        4 * (B * starRingEnd ℂ f).re * (B * e * starRingEnd ℂ p).re =
      normSq (starRingEnd ℂ B * (p + f * e) -
        ((2 * (B * starRingEnd ℂ f).re : ℝ) : ℂ) * e) := by
  simp only [normSq_apply, add_re, add_im, sub_re, sub_im, mul_re, mul_im,
    conj_re, conj_im, ofReal_re, ofReal_im]
  ring

/-- Every complex test retains an exact square identity coupling the
signed arithmetic numerator to the original carrier denominator. -/
theorem suzukiEtaFiniteCompletedNumerator_square_identity (B : ℂ) (N : ℕ) (s : ℂ) :
    normSq B * normSq (suzukiEtaFiniteCarrierDenominator N s) -
        4 * suzukiEtaDyadicWeightCoefficient B s * (B * suzukiEtaFiniteCompletedNumerator N s).re =
      normSq (starRingEnd ℂ B * suzukiEtaFiniteCarrierDenominator N s -
        ((2 * suzukiEtaDyadicWeightCoefficient B s : ℝ) : ℂ) * pairedEtaCorePartialSum N s) := by
  have hD : suzukiEtaFiniteCarrierDenominator N s =
      (pairedEtaCoreDerivativePartialSum N s +
        (1 + suzukiChebyshevMellinCompletedCorrection s) * pairedEtaCorePartialSum N s) +
        (-pairedEtaFactorLogDerivative s) * pairedEtaCorePartialSum N s := by
    unfold suzukiEtaFiniteCarrierDenominator
    rw [pairedEtaArithmeticXiRegularCorrection_eq_completed_sub_dyadic]
    ring
  rw [hD]
  simpa only [suzukiEtaDyadicWeightCoefficient, suzukiEtaFiniteCompletedNumerator,
    map_neg, mul_neg, neg_re, mul_assoc] using
    complex_square_identity B (pairedEtaCorePartialSum N s)
      (pairedEtaCoreDerivativePartialSum N s +
        (1 + suzukiChebyshevMellinCompletedCorrection s) * pairedEtaCorePartialSum N s)
      (-pairedEtaFactorLogDerivative s)

/-- The square gives a homogeneous independent inequality for every
signed coefficient and complex test, even at a zero denominator. -/
theorem suzukiEtaFiniteCompletedNumerator_re_mul_le (B : ℂ) (N : ℕ) (s : ℂ) :
    4 * suzukiEtaDyadicWeightCoefficient B s * (B * suzukiEtaFiniteCompletedNumerator N s).re ≤
      normSq B * normSq (suzukiEtaFiniteCarrierDenominator N s) := by
  have h := suzukiEtaFiniteCompletedNumerator_square_identity B N s
  linarith [normSq_nonneg (starRingEnd ℂ B * suzukiEtaFiniteCarrierDenominator N s -
    ((2 * suzukiEtaDyadicWeightCoefficient B s : ℝ) : ℂ) * pairedEtaCorePartialSum N s)]

/-- When the dyadic test coefficient is positive, the signed quotient
has an independent upper bound requiring no denominator separation. -/
theorem suzukiEtaFiniteCompletedNumerator_quotient_le (B : ℂ) (N : ℕ) {s : ℂ}
    (hB : 0 < suzukiEtaDyadicWeightCoefficient B s) :
    (B * suzukiEtaFiniteCompletedNumerator N s).re / normSq (suzukiEtaFiniteCarrierDenominator N s) ≤
      normSq B / (4 * suzukiEtaDyadicWeightCoefficient B s) := by
  by_cases hD : suzukiEtaFiniteCarrierDenominator N s = 0
  · simp only [hD, normSq_zero, div_zero]
    exact div_nonneg (normSq_nonneg _) (by positivity)
  · have hd := Complex.normSq_pos.mpr hD
    apply (div_le_div_iff₀ hd (by positivity)).mpr
    simpa only [mul_comm] using suzukiEtaFiniteCompletedNumerator_re_mul_le B N s

/-- Reversing the sign of the dyadic test coefficient yields an
independent lower bound, retaining the same arithmetic quotient. -/
theorem le_suzukiEtaFiniteCompletedNumerator_quotient (B : ℂ) (N : ℕ) {s : ℂ}
    (hB : suzukiEtaDyadicWeightCoefficient B s < 0) :
    normSq B / (4 * suzukiEtaDyadicWeightCoefficient B s) ≤
      (B * suzukiEtaFiniteCompletedNumerator N s).re / normSq (suzukiEtaFiniteCarrierDenominator N s) := by
  have hneg : suzukiEtaDyadicWeightCoefficient (-B) s = -suzukiEtaDyadicWeightCoefficient B s := by
    simp [suzukiEtaDyadicWeightCoefficient]
  have h := suzukiEtaFiniteCompletedNumerator_quotient_le (-B) N (by rw [hneg]; linarith)
  rw [hneg] at h
  simpa only [neg_mul, neg_re, normSq_neg, mul_neg, div_neg, neg_div, neg_neg] using neg_le_neg h

/-- A negative coefficient bounded in units of the weight norm gives
a homogeneous uniform floor. The zero weight is included. -/
theorem suzukiEtaFiniteCompletedNumerator_quotient_lower_of_coefficient
    (B : ℂ) (N : ℕ) {s : ℂ} {c : ℝ} (hc : 0 < c)
    (hcoef : suzukiEtaDyadicWeightCoefficient B s ≤ -c * ‖B‖) :
    -‖B‖ / (4 * c) ≤
      (B * suzukiEtaFiniteCompletedNumerator N s).re / normSq (suzukiEtaFiniteCarrierDenominator N s) := by
  by_cases hB : B = 0
  · simp [hB]
  have hn : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have ha : suzukiEtaDyadicWeightCoefficient B s < 0 :=
    hcoef.trans_lt (mul_neg_of_neg_of_pos (neg_neg_of_pos hc) hn)
  refine le_trans ?_ (le_suzukiEtaFiniteCompletedNumerator_quotient B N ha)
  rw [← Complex.sq_norm]
  apply (le_div_iff_of_neg (by nlinarith : 4 * suzukiEtaDyadicWeightCoefficient B s < 0)).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < 4 * c)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hcoef hn.le]

/-- Favorable strip phases make the unweighted dyadic coefficient
uniformly positive; the imaginary dyadic component is still retained. -/
theorem suzukiEtaDyadicWeightCoefficient_one_lower {s : ℂ}
    (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 1)
    (hphase : Real.cos (s.im * Real.log 2) ≤ 0) :
    Real.log 2 / 2 ≤ suzukiEtaDyadicWeightCoefficient 1 s := by
  simpa only [suzukiEtaDyadicWeightCoefficient, one_mul, conj_re] using
    (pairedEtaFactorLogDerivative_re_phase_strip_bounds hlo hhi hphase).1

/-- The signed eta/derivative and Archimedean numerator is controlled
by the true denominator with a constant independent of the truncation. -/
theorem suzukiEtaFiniteCompletedNumerator_re_phase_le (N : ℕ) {s : ℂ}
    (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 1)
    (hphase : Real.cos (s.im * Real.log 2) ≤ 0) :
    2 * Real.log 2 * (suzukiEtaFiniteCompletedNumerator N s).re ≤
      normSq (suzukiEtaFiniteCarrierDenominator N s) := by
  have ha := suzukiEtaDyadicWeightCoefficient_one_lower hlo hhi hphase
  have hs := suzukiEtaFiniteCompletedNumerator_re_mul_le 1 N s
  simp only [normSq_one, one_mul] at hs
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hp : 0 ≤ (suzukiEtaFiniteCompletedNumerator N s).re
  · nlinarith [mul_le_mul_of_nonneg_right ha hp]
  · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_ge hp)).trans (normSq_nonneg _)

/-- The remaining scalar signed quotient is uniformly bounded above
by `1/(2*log 2)` on every favorable closed strip, even near carrier poles. -/
theorem suzukiEtaFiniteCompletedNumerator_quotient_phase_le (N : ℕ) {s : ℂ}
    (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 1)
    (hphase : Real.cos (s.im * Real.log 2) ≤ 0) :
    (suzukiEtaFiniteCompletedNumerator N s).re / normSq (suzukiEtaFiniteCarrierDenominator N s) ≤
      1 / (2 * Real.log 2) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hD : suzukiEtaFiniteCarrierDenominator N s = 0
  · simp only [hD, normSq_zero, div_zero]
    positivity
  · apply (div_le_div_iff₀ (Complex.normSq_pos.mpr hD) (by positivity)).mpr
    simpa only [one_mul, mul_comm] using suzukiEtaFiniteCompletedNumerator_re_phase_le N hlo hhi hphase

/-- Every favorable actual vertical side has the independent scalar
upper bound throughout the full original strip segment, uniformly in N. -/
theorem suzukiEtaFiniteCompletedNumerator_quotient_vertical_le (N : ℕ) {v y : ℝ}
    (hphase : Real.cos (v * Real.log 2) ≤ 0) (hy : y ∈ Set.Icc 0 (1 / 2)) :
    (suzukiEtaFiniteCompletedNumerator N (suzukiArithmeticZetaArgument ((v : ℂ) + (y : ℂ) * I))).re /
        normSq (suzukiEtaFiniteCarrierDenominator N
          (suzukiArithmeticZetaArgument ((v : ℂ) + (y : ℂ) * I))) ≤
      1 / (2 * Real.log 2) := by
  apply suzukiEtaFiniteCompletedNumerator_quotient_phase_le
  · rw [suzukiArithmeticZetaArgument_re]
    simpa using hy.1
  · rw [suzukiArithmeticZetaArgument_re]
    simp only [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add]
    linarith [hy.2]
  · rwa [cos_suzukiArithmeticZetaArgument_vertical]

end
end RiemannGaussian
