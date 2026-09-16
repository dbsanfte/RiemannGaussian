/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRefinedMatching
import RiemannGaussian.ZetaRieszDescendingAmplitude

/-!
# The complete prime-pair cost on a descending interval

Keep the actual cutoff, full polynomial, local pair interval and phase.
The resulting pair costs are independently proved; aggregate cancellation
at source scale and a new zero-free region remain open.
-/

namespace RiemannGaussian.ZetaRieszSharpPair
noncomputable section
open scoped BigOperators Classical
open ZetaArithmeticBandCorrelation ZetaSquarefreeRieszWindows ZetaRieszOppositePrimes
open ZetaRieszPrimeReplacement ZetaRieszReplacementPhase ZetaRieszCenteredCofactor
open ZetaRieszTentSlope ZetaRieszRefinedMatching ZetaRieszDescendingAmplitude

/-- The complete pair cost keeps the exact factorial endpoint and its
descending derivative. The actual prime count selects the proved divisor
factor: two for prime cofactors, four for squarefree composite cofactors. -/
def descendingPrimeCost (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) (p q n : ℕ) : ℝ :=
  let A := min (Real.log (q * n : ℕ)) (Real.log (p * n : ℕ))
  let E := amplitudeMajorant L P N (3 / 2) A
  let gap := |Real.log p - Real.log q|
  let chord := 2 * |Real.cos (t * (Real.log p - Real.log q) / 2)|
  (E * gap + E * ((3 / 2) * gap + chord) * Real.log q) *
    (∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)|) /
      (if n.Prime then 2 else 4)

/-- Every actual original pair above all of its stationary points has
the full exact-endpoint cost. No analytic amplitude or derivative bound
is assumed; the sole geometric condition is checked on its actual logs. -/
theorem norm_bandWeight_pair_le_descending (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {L : ℝ} (hL : 0 < L) {p q n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n) (hn : Squarefree n) (hn1 : n ≠ 1)
    (hBandP : p * n ∈ zetaPrimeLogBand N) (hBandQ : q * n ∈ zetaPrimeLogBand N)
    (hdesc : ∀ k ∈ P.support, (N + k + 1 : ℕ) ≤ (3 / 2 : ℝ) *
      min (Real.log (q * n : ℕ)) (Real.log (p * n : ℕ))) :
    ‖ZetaRieszConditionedEnergy.bandWeight L P N t (p * n) +
      ZetaRieszConditionedEnergy.bandWeight L P N t (q * n)‖ ≤
      descendingPrimeCost L P N t p q n := by
  let A := min (Real.log (q * n : ℕ)) (Real.log (p * n : ℕ))
  let E := amplitudeMajorant L P N (3 / 2) A
  let gap := |Real.log p - Real.log q|
  let chord := 2 * |Real.cos (t * (Real.log p - Real.log q) / 2)|
  let d : ℝ := if n.Prime then 2 else 4
  have hd : 0 < d := by dsimp [d]; split_ifs <;> norm_num
  have hprofile : ‖ZetaRieszConditionedEnergy.bandWeight L P N t (p * n) +
      ZetaRieszConditionedEnergy.bandWeight L P N t (q * n)‖ ≤
      (‖bandAmplitude L P N t (p * n)‖ * gap +
        ‖bandAmplitude L P N t (p * n) + bandAmplitude L P N t (q * n)‖ * Real.log q) *
        (∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)|) / d := by
    by_cases hPrime : n.Prime
    · simpa only [d, gap, if_pos hPrime] using
        norm_bandWeight_prime_pair_centered L P N t hp hq hpn hqn hn1
    · simpa only [d, gap, if_neg hPrime] using
        norm_bandWeight_prime_pair_quarter L P N t hp hq hpn hqn hn
          (two_le_prime_count hn hn1 hPrime)
  have hA : 0 ≤ A := le_min (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have hx : A ≤ Real.log (q * n : ℕ) := min_le_left _ _
  have hy : A ≤ Real.log (p * n : ℕ) := min_le_right _ _
  have hqeq := bandAmplitude_eq_logAmplitude L P N t
    ⟨hBandQ, prime_mul_composite_support hq hn hn1 hqn⟩
  have hpeq := bandAmplitude_eq_logAmplitude L P N t
    ⟨hBandP, prime_mul_composite_support hp hn hn1 hpn⟩
  have hamp : ‖bandAmplitude L P N t (p * n)‖ ≤ E := by
    rw [hpeq]
    have he := norm_logAmplitude_add_imag L P N (3 / 2) t (Real.log (p * n : ℕ))
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at he
    rw [he]
    have hh := norm_logAmplitude_le_left P N ((3 / 2 : ℝ) : ℂ) hL
      (by norm_num : (0 : ℝ) ≤ 3 / 2) hA hy hdesc
    change _ ≤ E at hh
    simpa only [E, Complex.ofReal_re, Complex.ofReal_div, Complex.ofReal_ofNat] using hh
  have hsum : ‖bandAmplitude L P N t (p * n) + bandAmplitude L P N t (q * n)‖ ≤
      E * ((3 / 2) * gap + chord) := by
    rw [hpeq, hqeq]
    have hh := norm_logAmplitude_add_le_endpoint_phase P N t hL
      (by norm_num : (0 : ℝ) ≤ 3 / 2) hA hx hy hdesc
    rw [prime_insertion_log_difference hp.pos hq.pos (Nat.pos_of_ne_zero hn.ne_zero)] at hh
    simpa only [E, gap, chord, Complex.ofReal_div, Complex.ofReal_ofNat] using hh
  apply hprofile.trans
  change _ ≤ (E * gap + E * ((3 / 2) * gap + chord) * Real.log q) * _ / d
  apply div_le_div_of_nonneg_right _ hd.le
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (by intros; positivity))
  exact add_le_add (mul_le_mul_of_nonneg_right hamp (abs_nonneg _))
    (mul_le_mul_of_nonneg_right hsum (Real.log_natCast_nonneg _))

end
end RiemannGaussian.ZetaRieszSharpPair
