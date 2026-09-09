/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.EtaDyadicPhaseBounds

/-!
# Signed finite eta numerators with bounded dyadic completion

The literal numerator `eta_N * conj(D_N)` splits into its signed
eta/derivative interaction and its completion contribution. On favorable
dyadic phases we bound the latter independently, keeping the former
exact. An additional complex enclosure applies to every complex weight.
No sign or upper bound is assumed for the remaining eta interaction,
and no lower bound for the full carrier denominator is asserted.
-/

open Complex
namespace RiemannGaussian
noncomputable section

/-- The eta completion correction separates exactly into the previously
defined elementary/Archimedean correction and the dyadic derivative. -/
theorem pairedEtaArithmeticXiRegularCorrection_eq_completed_sub_dyadic (s : ℂ) :
    pairedEtaArithmeticXiRegularCorrection s =
      suzukiChebyshevMellinCompletedCorrection s - pairedEtaFactorLogDerivative s := rfl

/-- The finite signed numerator keeps the eta/derivative cross term
and the full completion coefficient, without dividing by eta. -/
theorem suzukiEtaFiniteCarrier_numerator_re_eq (N : ℕ) (s : ℂ) :
    (pairedEtaCorePartialSum N s * starRingEnd ℂ (suzukiEtaFiniteCarrierDenominator N s)).re =
      (pairedEtaCorePartialSum N s * starRingEnd ℂ (pairedEtaCoreDerivativePartialSum N s)).re +
        (1 + (suzukiChebyshevMellinCompletedCorrection s).re -
          (pairedEtaFactorLogDerivative s).re) * normSq (pairedEtaCorePartialSum N s) := by
  unfold suzukiEtaFiniteCarrierDenominator
  rw [pairedEtaArithmeticXiRegularCorrection_eq_completed_sub_dyadic]
  simp only [map_add, map_mul, conj_re, conj_im, mul_re, mul_im, add_re, add_im,
    sub_re, sub_im, one_re, one_im, normSq_apply]
  ring

/-- The actual finite signed numerator has a two-sided completion
enclosure of width `log(2)/6 * |eta_N|²`. Its signed eta/derivative
interaction is retained on both sides rather than norm-bounded. -/
theorem suzukiEtaFiniteCarrier_numerator_re_phase_bounds (N : ℕ) {s : ℂ}
    (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 1)
    (hphase : Real.cos (s.im * Real.log 2) ≤ 0) :
    (pairedEtaCorePartialSum N s * starRingEnd ℂ (pairedEtaCoreDerivativePartialSum N s)).re +
        (1 + (suzukiChebyshevMellinCompletedCorrection s).re + Real.log 2 / 2) *
          normSq (pairedEtaCorePartialSum N s) ≤
      (pairedEtaCorePartialSum N s * starRingEnd ℂ (suzukiEtaFiniteCarrierDenominator N s)).re ∧
    (pairedEtaCorePartialSum N s * starRingEnd ℂ (suzukiEtaFiniteCarrierDenominator N s)).re ≤
      (pairedEtaCorePartialSum N s * starRingEnd ℂ (pairedEtaCoreDerivativePartialSum N s)).re +
        (1 + (suzukiChebyshevMellinCompletedCorrection s).re + 2 * Real.log 2 / 3) *
          normSq (pairedEtaCorePartialSum N s) := by
  rw [suzukiEtaFiniteCarrier_numerator_re_eq]
  obtain ⟨hl, hu⟩ := pairedEtaFactorLogDerivative_re_phase_strip_bounds hlo hhi hphase
  have hq := normSq_nonneg (pairedEtaCorePartialSum N s)
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right hl hq,
    mul_le_mul_of_nonneg_right hu hq]

/-- The full complex weighted numerator has an exact centered
decomposition. The dyadic correction remains a complex product, with
every eta coefficient, weight and phase still present. -/
theorem suzukiEtaFiniteCarrier_weighted_numerator_centered (B : ℂ) (N : ℕ) (s : ℂ) :
    B * pairedEtaCorePartialSum N s * starRingEnd ℂ (suzukiEtaFiniteCarrierDenominator N s) -
      B * pairedEtaCorePartialSum N s * starRingEnd ℂ
        (pairedEtaCoreDerivativePartialSum N s +
          (1 + suzukiChebyshevMellinCompletedCorrection s + (Real.log 2 : ℂ) / 2) *
            pairedEtaCorePartialSum N s) =
      -(B * starRingEnd ℂ (pairedEtaFactorLogDerivative s + (Real.log 2 : ℂ) / 2)) *
        (normSq (pairedEtaCorePartialSum N s) : ℂ) := by
  unfold suzukiEtaFiniteCarrierDenominator
  rw [pairedEtaArithmeticXiRegularCorrection_eq_completed_sub_dyadic,
    Complex.normSq_eq_conj_mul_self]
  simp only [map_add, map_sub, map_mul]
  ring

/-- The dyadic part of the literal finite numerator is uniformly
controlled for every complex test weight. The remaining centered
eta/derivative numerator is still signed and unestimated. -/
theorem suzukiEtaFiniteCarrier_weighted_numerator_phase_error (B : ℂ) (N : ℕ) {s : ℂ}
    (hphase : Real.cos (s.im * Real.log 2) ≤ 0) :
    |(B * pairedEtaCorePartialSum N s *
        starRingEnd ℂ (suzukiEtaFiniteCarrierDenominator N s)).re -
      (B * pairedEtaCorePartialSum N s * starRingEnd ℂ
        (pairedEtaCoreDerivativePartialSum N s +
          (1 + suzukiChebyshevMellinCompletedCorrection s + (Real.log 2 : ℂ) / 2) *
            pairedEtaCorePartialSum N s)).re| ≤
      ‖B‖ * normSq (pairedEtaCorePartialSum N s) * (Real.log 2 / 2) := by
  rw [← sub_re, suzukiEtaFiniteCarrier_weighted_numerator_centered]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_neg, norm_mul, Complex.norm_conj, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (normSq_nonneg _)]
  calc
    ‖B‖ * ‖pairedEtaFactorLogDerivative s + (Real.log 2 : ℂ) / 2‖ *
        normSq (pairedEtaCorePartialSum N s) =
      (‖B‖ * normSq (pairedEtaCorePartialSum N s)) *
        ‖pairedEtaFactorLogDerivative s + (Real.log 2 : ℂ) / 2‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_pairedEtaFactorLogDerivative_add_half_le hphase)
      (mul_nonneg (norm_nonneg _) (normSq_nonneg _))

/-- The finite carrier's exact quadratic energy retains its true
denominator. This identity also respects the totalized value at zero. -/
theorem normSq_suzukiEtaFiniteCarrier (N : ℕ) (s : ℂ) :
    normSq (suzukiEtaFiniteCarrier N s) =
      normSq (pairedEtaCorePartialSum N s) / normSq (suzukiEtaFiniteCarrierDenominator N s) := by
  rw [suzukiEtaFiniteCarrier, normSq_div, normSq_mul, normSq_I, one_mul]

/-- The actual weighted finite carrier has a centered dyadic error
controlled by its own quadratic energy. The same true denominator
remains in the signed centered term, including near its zeros. -/
theorem suzukiEtaFiniteCarrier_im_phase_energy_error (B : ℂ) (N : ℕ) {s : ℂ}
    (hphase : Real.cos (s.im * Real.log 2) ≤ 0) :
    |(B * suzukiEtaFiniteCarrier N s).im -
      (B * pairedEtaCorePartialSum N s * starRingEnd ℂ
        (pairedEtaCoreDerivativePartialSum N s +
          (1 + suzukiChebyshevMellinCompletedCorrection s + (Real.log 2 : ℂ) / 2) *
            pairedEtaCorePartialSum N s)).re /
        normSq (suzukiEtaFiniteCarrierDenominator N s)| ≤
      ‖B‖ * normSq (suzukiEtaFiniteCarrier N s) * (Real.log 2 / 2) := by
  rw [im_mul_suzukiEtaFiniteCarrier, ← sub_div, abs_div,
    abs_of_nonneg (normSq_nonneg _)]
  calc
    _ ≤ (‖B‖ * normSq (pairedEtaCorePartialSum N s) * (Real.log 2 / 2)) /
        normSq (suzukiEtaFiniteCarrierDenominator N s) :=
      div_le_div_of_nonneg_right (suzukiEtaFiniteCarrier_weighted_numerator_phase_error B N hphase)
        (normSq_nonneg _)
    _ = _ := by rw [normSq_suzukiEtaFiniteCarrier]; ring

/-- The dyadic part of the actual finite carrier contributes a
strictly positive multiple of its energy on favorable strip phases.
The eta/derivative and Archimedean terms are kept as one signed term. -/
theorem suzukiEtaFiniteCarrier_im_phase_strip_energy_bounds (N : ℕ) {s : ℂ}
    (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 1)
    (hphase : Real.cos (s.im * Real.log 2) ≤ 0) :
    Real.log 2 / 2 * normSq (suzukiEtaFiniteCarrier N s) ≤
      (suzukiEtaFiniteCarrier N s).im -
        ((pairedEtaCorePartialSum N s * starRingEnd ℂ (pairedEtaCoreDerivativePartialSum N s)).re +
          (1 + (suzukiChebyshevMellinCompletedCorrection s).re) * normSq (pairedEtaCorePartialSum N s)) /
          normSq (suzukiEtaFiniteCarrierDenominator N s) ∧
    (suzukiEtaFiniteCarrier N s).im -
        ((pairedEtaCorePartialSum N s * starRingEnd ℂ (pairedEtaCoreDerivativePartialSum N s)).re +
          (1 + (suzukiChebyshevMellinCompletedCorrection s).re) * normSq (pairedEtaCorePartialSum N s)) /
          normSq (suzukiEtaFiniteCarrierDenominator N s) ≤
      2 * Real.log 2 / 3 * normSq (suzukiEtaFiniteCarrier N s) := by
  have hid : (suzukiEtaFiniteCarrier N s).im =
      (pairedEtaCorePartialSum N s * starRingEnd ℂ (suzukiEtaFiniteCarrierDenominator N s)).re /
        normSq (suzukiEtaFiniteCarrierDenominator N s) := by
    simpa only [one_mul] using im_mul_suzukiEtaFiniteCarrier 1 N s
  rw [hid, suzukiEtaFiniteCarrier_numerator_re_eq, normSq_suzukiEtaFiniteCarrier]
  obtain ⟨hl, hu⟩ := pairedEtaFactorLogDerivative_re_phase_strip_bounds hlo hhi hphase
  have hq : 0 ≤ normSq (pairedEtaCorePartialSum N s) /
      normSq (suzukiEtaFiniteCarrierDenominator N s) := div_nonneg (normSq_nonneg _) (normSq_nonneg _)
  have hlm := mul_le_mul_of_nonneg_right hl hq
  have hum := mul_le_mul_of_nonneg_right hu hq
  simp only [div_eq_mul_inv] at hlm hum ⊢
  constructor <;> nlinarith [hlm, hum]

end
end RiemannGaussian
