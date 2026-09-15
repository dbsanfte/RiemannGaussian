/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszReplacementFamily

/-!
# Exact disjoint cancellation matchings

Preserve the full complex filter, original support and unmatched remainder.
Centering halves a proved pair allowance; a source-scale saving for the
whole carrier and a new zero-free region remain open.
-/

namespace RiemannGaussian.ZetaRieszPairMatching
noncomputable section
open scoped BigOperators Classical

/-- The two original integer labels in a cancellation pair. -/
def pairVertices (e : ℕ × ℕ) : Finset ℕ := {e.1, e.2}

/-- Every selected pair has distinct ends and different pairs spend
disjoint sets of original integers. -/
def separatedPairs (E : Finset (ℕ × ℕ)) : Prop :=
  (∀ e ∈ E, e.1 ≠ e.2) ∧ (E : Set (ℕ × ℕ)).PairwiseDisjoint pairVertices

/-- The original integer support of a complete selected matching. -/
def matchedVertices (E : Finset (ℕ × ℕ)) : Finset ℕ := E.biUnion pairVertices

/-- Exact transport of any additive observable through the matching.
It applies to both the complex carrier and its absolute-mass budget. -/
theorem sum_matchedVertices {α : Type*} [AddCommMonoid α]
    (E : Finset (ℕ × ℕ)) (hE : separatedPairs E) (f : ℕ → α) :
    (∑ n ∈ matchedVertices E, f n) = ∑ e ∈ E, (f e.1 + f e.2) := by
  rw [matchedVertices, Finset.sum_biUnion hE.2]
  apply Finset.sum_congr rfl
  intro e he
  exact Finset.sum_pair (hE.1 e he)

/-- All matched labels remain inside their original finite support. -/
theorem matchedVertices_subset {S : Finset ℕ} {E : Finset (ℕ × ℕ)}
    (hE : E ⊆ S ×ˢ S) : matchedVertices E ⊆ S := by
  intro n hn
  obtain ⟨e, he, hn⟩ := Finset.mem_biUnion.mp hn
  have hs := Finset.mem_product.mp (hE he)
  have hn' : n = e.1 ∨ n = e.2 := by
    simpa only [pairVertices, Finset.mem_insert, Finset.mem_singleton] using hn
  rcases hn' with hn | hn
  · simpa only [hn] using hs.1
  · simpa only [hn] using hs.2

/-- Every proved pair cost has a nonnegative certified gain over its
two separate norms, with an unhelpful cost clipped away. -/
def edgeSaving (f : ℕ → ℂ) (C : ℕ × ℕ → ℝ) (e : ℕ × ℕ) : ℝ :=
  max (‖f e.1‖ + ‖f e.2‖ - C e) 0

/-- The full signed carrier splits exactly into selected pairs and
the original unmatched integers. No amplitude or phase is discarded. -/
theorem sum_eq_pairs_add_remainder (S : Finset ℕ) (E : Finset (ℕ × ℕ))
    (hE : separatedPairs E) (hS : E ⊆ S ×ˢ S) (f : ℕ → ℂ) :
    (∑ n ∈ S, f n) = (∑ e ∈ E, (f e.1 + f e.2)) +
      ∑ n ∈ S \ matchedVertices E, f n := by
  rw [← sum_matchedVertices E hE, add_comm]
  exact (Finset.sum_sdiff (matchedVertices_subset hS)).symm

/-- A complete matching pays every proved pair saving exactly once.
The richer complex partition remains available in the preceding identity. -/
theorem norm_sum_le_mass_sub_pair_savings (S : Finset ℕ) (E : Finset (ℕ × ℕ))
    (hE : separatedPairs E) (hS : E ⊆ S ×ˢ S) (f : ℕ → ℂ) (C : ℕ × ℕ → ℝ)
    (hC : ∀ e ∈ E, ‖f e.1 + f e.2‖ ≤ C e) :
    ‖∑ n ∈ S, f n‖ ≤ (∑ n ∈ S, ‖f n‖) - ∑ e ∈ E, edgeSaving f C e := by
  have hpair : ‖∑ e ∈ E, (f e.1 + f e.2)‖ ≤
      (∑ e ∈ E, (‖f e.1‖ + ‖f e.2‖)) - ∑ e ∈ E, edgeSaving f C e := by
    rw [← Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun e he =>
      ZetaRieszReplacementFamily.norm_pair_le_sub_saving _ _ (hC e he)))
  have hmass : (∑ e ∈ E, (‖f e.1‖ + ‖f e.2‖)) +
      (∑ n ∈ S \ matchedVertices E, ‖f n‖) = ∑ n ∈ S, ‖f n‖ := by
    rw [← sum_matchedVertices E hE (fun n => ‖f n‖), add_comm]
    exact Finset.sum_sdiff (matchedVertices_subset hS)
  rw [sum_eq_pairs_add_remainder S E hE hS f]
  apply (norm_add_le _ _).trans
  have h := add_le_add hpair (norm_sum_le (S \ matchedVertices E) (fun n => f n))
  linarith

/-- Every disjoint subfamily of the candidate arithmetic edges is
considered; this does not pick a special coefficient or prime family. -/
def candidateMatchings (Q : Finset (ℕ × ℕ)) : Finset (Finset (ℕ × ℕ)) :=
  Q.powerset.filter separatedPairs

/-- The empty selection guarantees existence even when no candidate
pair yields a useful cancellation. -/
theorem empty_mem_candidateMatchings (Q : Finset (ℕ × ℕ)) : ∅ ∈ candidateMatchings Q := by
  simp [candidateMatchings, separatedPairs, Set.PairwiseDisjoint]

/-- The best finite saving over all disjoint candidate families is
attained. Its amount remains an arithmetic quantity to be estimated. -/
theorem exists_maximal_pair_savings (S : Finset ℕ) (Q : Finset (ℕ × ℕ))
    (hQ : Q ⊆ S ×ˢ S) (f : ℕ → ℂ) (C : ℕ × ℕ → ℝ)
    (hC : ∀ e ∈ Q, ‖f e.1 + f e.2‖ ≤ C e) :
    ∃ E ∈ candidateMatchings Q,
      (∀ F ∈ candidateMatchings Q, (∑ e ∈ F, edgeSaving f C e) ≤ ∑ e ∈ E, edgeSaving f C e) ∧
      ‖∑ n ∈ S, f n‖ ≤ (∑ n ∈ S, ‖f n‖) - ∑ e ∈ E, edgeSaving f C e := by
  obtain ⟨E, hE, hmax⟩ := Finset.exists_max_image (candidateMatchings Q)
    (fun E => ∑ e ∈ E, edgeSaving f C e) ⟨∅, empty_mem_candidateMatchings Q⟩
  have hsubset : E ⊆ Q := Finset.mem_powerset.mp (Finset.mem_filter.mp hE).1
  refine ⟨E, hE, hmax, ?_⟩
  exact norm_sum_le_mass_sub_pair_savings S E (Finset.mem_filter.mp hE).2
    (hsubset.trans hQ) f C (fun e he => hC e (hsubset he))

end
end RiemannGaussian.ZetaRieszPairMatching
