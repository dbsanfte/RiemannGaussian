/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszTentSlope
import RiemannGaussian.ZetaRieszPrimeMatching

/-!
# Quarter the profile allowance for composite cofactors

Keep the actual cutoff, full polynomial, local pair interval and phase.
The resulting pair costs are independently proved; aggregate cancellation
at source scale and a new zero-free region remain open.
-/

namespace RiemannGaussian.ZetaRieszRefinedMatching
noncomputable section
open scoped BigOperators Classical
open ZetaRieszConditionedEnergy ZetaRieszPrimeMatching ZetaRieszPairMatching
open ZetaRieszTentSlope

/-- The actual nonunit squarefree composite has at least two prime
factors. No extra factor-count assumption is needed in the edge test. -/
theorem two_le_prime_count {n : ℕ} (hn : Squarefree n) (hn1 : n ≠ 1) (hnp : ¬ n.Prime) :
    2 ≤ n.primeFactors.card := by
  by_contra hcard
  have hh : n.primeFactors.card = 0 ∨ n.primeFactors.card = 1 := by omega
  rcases hh with hh | hh
  · apply hn1
    rw [← Nat.prod_primeFactors_of_squarefree hn, Finset.card_eq_zero.mp hh, Finset.prod_empty]
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hh
    have he : n = p := by rw [← Nat.prod_primeFactors_of_squarefree hn, hp, Finset.prod_singleton]
    exact hnp (he ▸ Nat.prime_of_mem_primeFactors (by rw [hp]; simp))

/-- The original pair cost is halved once more whenever its actual
shared cofactor is composite; prime cofactors retain their sharp unit slope. -/
def refinedPairCost (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t r : ℝ) (e : ℕ × ℕ) : ℝ :=
  if (Nat.gcd e.1 e.2).Prime then primePairCost L P N t r e
  else primePairCost L P N t r e / 2

/-- Every candidate's complete refined cost follows from its actual
arithmetic support, with no additional prime-count or cancellation premise. -/
theorem refinedPairCost_bound (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hr3 : r ≤ 3 / 2)
    {e : ℕ × ℕ} (he : e ∈ primePairEdges (N + 1)) :
    ‖bandWeight L P (N + 1) t e.1 + bandWeight L P (N + 1) t e.2‖ ≤
      refinedPairCost L P N t r e := by
  unfold refinedPairCost
  split_ifs with hgPrime
  · exact primePairCost_bound P N t hL hr hr3 he
  · simp only [primePairEdges, Finset.mem_filter, Finset.mem_product] at he
    obtain ⟨⟨hi, hj⟩, hcompatible⟩ := he
    change e.1 ≠ e.2 ∧ (e.1 / Nat.gcd e.1 e.2).Prime ∧
      (e.2 / Nat.gcd e.1 e.2).Prime ∧ Squarefree (Nat.gcd e.1 e.2) ∧
      Nat.gcd e.1 e.2 ≠ 1 ∧ ¬ (e.1 / Nat.gcd e.1 e.2) ∣ Nat.gcd e.1 e.2 ∧
      ¬ (e.2 / Nat.gcd e.1 e.2) ∣ Nat.gcd e.1 e.2 at hcompatible
    obtain ⟨_, hp, hq, hg, hg1, hpg, hqg⟩ := hcompatible
    have hei : (e.1 / Nat.gcd e.1 e.2) * Nat.gcd e.1 e.2 = e.1 :=
      Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
    have hej : (e.2 / Nat.gcd e.1 e.2) * Nat.gcd e.1 e.2 = e.2 :=
      Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
    have h := norm_bandWeight_prime_pair_le_quarter_phaseCost P N t hL hr hr3 hp hq hpg hqg hg
      (two_le_prime_count hg hg1 hgPrime)
      (by simpa only [hei] using hi) (by simpa only [hej] using hj)
    rw [hei, hej] at h
    exact h.trans_eq (by unfold primePairCost; dsimp only; ring)

/-- Refinement cannot increase any actual candidate cost. -/
theorem refinedPairCost_le (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hr3 : r ≤ 3 / 2)
    {e : ℕ × ℕ} (he : e ∈ primePairEdges (N + 1)) :
    refinedPairCost L P N t r e ≤ primePairCost L P N t r e := by
  have hC := (norm_nonneg _).trans (primePairCost_bound P N t hL hr hr3 he)
  unfold refinedPairCost
  split_ifs <;> linarith

/-- The whole original carrier attains its best disjoint saving with
all higher-prime-count pairs charged the sharper quarter-cost allowance.
The original prime cofactors and the unmatched remainder remain included;
a positive or source-scale aggregate saving is not asserted. -/
theorem exists_actual_band_refined_prime_pairs (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hr3 : r ≤ 3 / 2) :
    ∃ E ∈ candidateMatchings (primePairEdges (N + 1)),
      (∀ F ∈ candidateMatchings (primePairEdges (N + 1)),
        (∑ e ∈ F, edgeSaving (bandWeight L P (N + 1) t) (refinedPairCost L P N t r) e) ≤
          ∑ e ∈ E, edgeSaving (bandWeight L P (N + 1) t) (refinedPairCost L P N t r) e) ∧
      ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P (N + 1) t‖ ≤
        (∑ n ∈ zetaPrimeLogBand (N + 1), ‖bandWeight L P (N + 1) t n‖) -
          ∑ e ∈ E, edgeSaving (bandWeight L P (N + 1) t) (refinedPairCost L P N t r) e := by
  have hQ : primePairEdges (N + 1) ⊆ zetaPrimeLogBand (N + 1) ×ˢ zetaPrimeLogBand (N + 1) :=
    by unfold primePairEdges; exact Finset.filter_subset _ _
  obtain ⟨E, hE, hmax, hbound⟩ := exists_maximal_pair_savings (zetaPrimeLogBand (N + 1))
    (primePairEdges (N + 1)) hQ (bandWeight L P (N + 1) t) (refinedPairCost L P N t r)
    (fun _ he => refinedPairCost_bound P N t hL hr hr3 he)
  have he : (∑ n ∈ zetaPrimeLogBand (N + 1), bandWeight L P (N + 1) t n) =
      zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P (N + 1) t := by
    unfold bandWeight zetaArithmeticBand
    apply Finset.sum_congr rfl
    intro n hn
    rw [if_pos hn]
  rw [he] at hbound
  exact ⟨E, hE, hmax, hbound⟩

end
end RiemannGaussian.ZetaRieszRefinedMatching
