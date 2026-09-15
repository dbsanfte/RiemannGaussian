/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCenteredPhase
import RiemannGaussian.ZetaRieszPairMatching

/-!
# All eligible prime pairs in the original carrier

Preserve the full complex filter, original support and unmatched remainder.
Centering halves a proved pair allowance; a source-scale saving for the
whole carrier and a new zero-free region remain open.
-/

namespace RiemannGaussian.ZetaRieszPrimeMatching
noncomputable section
open scoped BigOperators Classical
open ZetaRieszOppositePrimes ZetaRieszPairMatching
open ZetaRieszConditionedEnergy

/-- A literal pair of original integers has a shared squarefree cofactor
and distinct prime insertions precisely when these finite arithmetic tests
succeed. The common factor is its actual gcd, not a freely chosen weight. -/
def primePairCompatible (i j : ℕ) : Prop :=
  let g := Nat.gcd i j
  i ≠ j ∧ (i / g).Prime ∧ (j / g).Prime ∧ Squarefree g ∧ g ≠ 1 ∧
    ¬ (i / g) ∣ g ∧ ¬ (j / g) ∣ g

/-- All eligible prime-insertion pairs in the original band are kept,
with both orientations available. A matching will prevent duplicate use. -/
@[irreducible] def primePairEdges (N : ℕ) : Finset (ℕ × ℕ) :=
  (zetaPrimeLogBand N ×ˢ zetaPrimeLogBand N).filter (fun e => primePairCompatible e.1 e.2)

/-- The fully specified arithmetic pair cost uses its actual gcd and
quotients. Centering halves the cost for every eligible nonunit gcd. -/
def primePairCost (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t r : ℝ) (e : ℕ × ℕ) : ℝ :=
  let g := Nat.gcd e.1 e.2
  let C := oppositePrimeCost L P N t r (e.1 / g) (e.2 / g) g
  C / 2

/-- Every candidate edge has its actual full amplitude bound, with all
factorization, support and centered-cofactor obligations discharged.
There is no residual pair-cancellation hypothesis. -/
theorem primePairCost_bound (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hr3 : r ≤ 3 / 2)
    {e : ℕ × ℕ} (he : e ∈ primePairEdges (N + 1)) :
    ‖bandWeight L P (N + 1) t e.1 + bandWeight L P (N + 1) t e.2‖ ≤
      primePairCost L P N t r e := by
  simp only [primePairEdges, Finset.mem_filter, Finset.mem_product] at he
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
  unfold primePairCost
  dsimp only
  have h := ZetaRieszCenteredPhase.norm_bandWeight_prime_pair_le_half_phaseCost
    P N t hL hr hr3 hp hq hpg hqg hg hg1
    (by simpa only [hei] using hi) (by simpa only [hej] using hj)
  simpa only [hei, hej] using h

/-- The whole original carrier has an attained optimal pair-saving
budget over every eligible prime-insertion family simultaneously. All
arithmetic pair costs and non-overlap requirements are proved from the
literal finite construction. A positive or source-scale saving is not
asserted; its arithmetic lower bound remains the next obligation. -/
theorem exists_actual_band_optimal_prime_pairs (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hr3 : r ≤ 3 / 2) :
    ∃ E ∈ candidateMatchings (primePairEdges (N + 1)),
      (∀ F ∈ candidateMatchings (primePairEdges (N + 1)),
        (∑ e ∈ F, edgeSaving (bandWeight L P (N + 1) t) (primePairCost L P N t r) e) ≤
          ∑ e ∈ E, edgeSaving (bandWeight L P (N + 1) t) (primePairCost L P N t r) e) ∧
      ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P (N + 1) t‖ ≤
        (∑ n ∈ zetaPrimeLogBand (N + 1), ‖bandWeight L P (N + 1) t n‖) -
          ∑ e ∈ E, edgeSaving (bandWeight L P (N + 1) t) (primePairCost L P N t r) e := by
  have hQ : primePairEdges (N + 1) ⊆ zetaPrimeLogBand (N + 1) ×ˢ zetaPrimeLogBand (N + 1) :=
    by unfold primePairEdges; exact Finset.filter_subset _ _
  obtain ⟨E, hE, hmax, hbound⟩ := exists_maximal_pair_savings (zetaPrimeLogBand (N + 1))
    (primePairEdges (N + 1)) hQ (bandWeight L P (N + 1) t) (primePairCost L P N t r)
    (fun _ he => primePairCost_bound P N t hL hr hr3 he)
  have he : (∑ n ∈ zetaPrimeLogBand (N + 1), bandWeight L P (N + 1) t n) =
      zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P (N + 1) t := by
    unfold bandWeight zetaArithmeticBand
    apply Finset.sum_congr rfl
    intro n hn
    rw [if_pos hn]
  rw [he] at hbound
  exact ⟨E, hE, hmax, hbound⟩

end
end RiemannGaussian.ZetaRieszPrimeMatching
