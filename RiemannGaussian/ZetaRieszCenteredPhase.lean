/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOppositePrimes
import RiemannGaussian.ZetaRieszCenteredCofactor

/-!
# The complete centered phase allowance

Preserve the full complex filter, original support and unmatched remainder.
Centering halves a proved pair allowance; a source-scale saving for the
whole carrier and a new zero-free region remain open.
-/

namespace RiemannGaussian.ZetaRieszCenteredPhase
noncomputable section
open scoped BigOperators Classical
open ZetaArithmeticBandCorrelation ZetaSquarefreeRieszWindows
open ZetaRieszPrimeReplacement ZetaRieszReplacementPhase
open ZetaRieszOppositePrimes ZetaRieszCenteredCofactor

/-- Centering the complete cofactor halves the fully explicit opposite-phase
cost for every eligible squarefree nonunit cofactor. The full polynomial,
physical support, smooth allowance and exact cosine phase are retained. -/
theorem norm_bandWeight_prime_pair_le_half_phaseCost (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hr3 : r ≤ 3 / 2)
    {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n)
    (hn : Squarefree n) (hn1 : n ≠ 1)
    (hBandP : p * n ∈ zetaPrimeLogBand (N + 1)) (hBandQ : q * n ∈ zetaPrimeLogBand (N + 1)) :
    ‖ZetaRieszConditionedEnergy.bandWeight L P (N + 1) t (p * n) +
      ZetaRieszConditionedEnergy.bandWeight L P (N + 1) t (q * n)‖ ≤
      oppositePrimeCost L P N t r p q n / 2 := by
  let A := min (Real.log (q * n : ℕ)) (Real.log (p * n : ℕ))
  let B := max (Real.log (q * n : ℕ)) (Real.log (p * n : ℕ))
  let E := B / L * logKernelEnvelope P (N + 1) (3 / 2 : ℂ) r A
  let D := logAmplitudeAllowance L P N (3 / 2 : ℂ) r A B
  let gap := |Real.log p - Real.log q|
  let chord := 2 * |Real.cos (t * (Real.log p - Real.log q) / 2)|
  have hA : 0 ≤ A := le_min (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have hx : Real.log (q * n : ℕ) ∈ Set.Icc A B := ⟨min_le_left _ _, le_max_left _ _⟩
  have hy : Real.log (p * n : ℕ) ∈ Set.Icc A B := ⟨min_le_right _ _, le_max_right _ _⟩
  have hrs : r ≤ (3 / 2 : ℂ).re := by norm_num; exact hr3
  have hsuqq := prime_mul_composite_support hq hn hn1 hqn
  have hsupp := prime_mul_composite_support hp hn hn1 hpn
  have hqeq := bandAmplitude_eq_logAmplitude L P (N + 1) t ⟨hBandQ, hsuqq⟩
  have hpeq := bandAmplitude_eq_logAmplitude L P (N + 1) t ⟨hBandP, hsupp⟩
  have hamp : ‖bandAmplitude L P (N + 1) t (p * n)‖ ≤ E := by
    rw [hpeq]
    have he := norm_logAmplitude_add_imag L P (N + 1) (3 / 2) t (Real.log (p * n : ℕ))
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at he
    rw [he]
    exact norm_logAmplitude_le P (N + 1) (3 / 2 : ℂ)
      (L := L) (r := r) (A := A) (B := B) (v := Real.log (p * n : ℕ))
      hL hr hrs (Real.log_natCast_nonneg (p * n)) hy.1 hy.2
  have hsum : ‖bandAmplitude L P (N + 1) t (p * n) + bandAmplitude L P (N + 1) t (q * n)‖ ≤
      D * gap + E * chord := by
    rw [hpeq, hqeq]
    have hh := norm_logAmplitude_add_le_phase P N (3 / 2) t hL hr hr3 hA hx hy
    rw [prime_insertion_log_difference hp.pos hq.pos (Nat.pos_of_ne_zero hn.ne_zero)] at hh
    simpa only [D, E, gap, chord, Complex.ofReal_div, Complex.ofReal_ofNat] using hh
  apply (norm_bandWeight_prime_pair_centered L P (N + 1) t hp hq hpn hqn hn1).trans
  change _ ≤ (E * gap + (D * gap + E * chord) * Real.log q) * _ / 2
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (by intros; positivity))
  exact add_le_add (mul_le_mul_of_nonneg_right hamp (abs_nonneg _))
    (mul_le_mul_of_nonneg_right hsum (Real.log_natCast_nonneg _))

end
end RiemannGaussian.ZetaRieszCenteredPhase
