/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSharpPair

/-!
# Sharper proved costs for the whole original carrier

Keep the actual cutoff, full polynomial, local pair interval and phase.
The resulting pair costs are independently proved; aggregate cancellation
at source scale and a new zero-free region remain open.
-/

namespace RiemannGaussian.ZetaRieszSharpMatching
noncomputable section
open scoped BigOperators Classical
open ZetaRieszConditionedEnergy ZetaRieszPrimeMatching ZetaRieszPairMatching
open ZetaRieszRefinedMatching ZetaRieszSharpPair

/-- The exact finite stationary-point test on the two original labels. -/
def stationaryPair (P : Polynomial ℂ) (N : ℕ) (e : ℕ × ℕ) : Prop :=
  ∀ k ∈ P.support, (N + k + 1 : ℕ) ≤ (3 / 2 : ℝ) * min (Real.log e.2) (Real.log e.1)

/-- Every pair keeps its proved refined cost; where the actual stationary
condition holds, it can use the better exact factorial-endpoint cost. -/
def sharpPairCost (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t r : ℝ) (e : ℕ × ℕ) : ℝ :=
  if stationaryPair P (N + 1) e then
    min (refinedPairCost L P N t r e)
      (descendingPrimeCost L P (N + 1) t (e.1 / Nat.gcd e.1 e.2)
        (e.2 / Nat.gcd e.1 e.2) (Nat.gcd e.1 e.2))
  else refinedPairCost L P N t r e

/-- The new endpoint option never increases the preceding pair cost. -/
theorem sharpPairCost_le_refined (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t r : ℝ) (e : ℕ × ℕ) :
    sharpPairCost L P N t r e ≤ refinedPairCost L P N t r e := by
  unfold sharpPairCost
  split_ifs
  · exact min_le_left _ _
  · rfl

/-- The literal pair test discharges all sharp-amplitude hypotheses.
The original cost covers every pair below its stationary range, so no
part of the original band is lost in the sharper estimate. -/
theorem sharpPairCost_bound (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hr3 : r ≤ 3 / 2)
    {e : ℕ × ℕ} (he : e ∈ primePairEdges (N + 1)) :
    ‖bandWeight L P (N + 1) t e.1 + bandWeight L P (N + 1) t e.2‖ ≤
      sharpPairCost L P N t r e := by
  have hold := refinedPairCost_bound P N t hL hr hr3 he
  unfold sharpPairCost
  split_ifs with hdesc
  · apply le_min hold
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
    have h := norm_bandWeight_pair_le_descending P (N + 1) t hL hp hq hpg hqg hg hg1
      (by simpa only [hei] using hi) (by simpa only [hej] using hj)
      (by simpa only [stationaryPair, hei, hej] using hdesc)
    simpa only [hei, hej] using h
  · exact hold

/-- The complete original carrier uses the best disjoint savings after
all cofactor, derivative, phase and stationary-region refinements. Every
candidate's analytic cost is proved, including the fallback branch. The
aggregate source-scale saving and any new zero-free conclusion remain open. -/
theorem exists_actual_band_sharp_prime_pairs (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hr3 : r ≤ 3 / 2) :
    ∃ E ∈ candidateMatchings (primePairEdges (N + 1)),
      (∀ F ∈ candidateMatchings (primePairEdges (N + 1)),
        (∑ e ∈ F, edgeSaving (bandWeight L P (N + 1) t) (sharpPairCost L P N t r) e) ≤
          ∑ e ∈ E, edgeSaving (bandWeight L P (N + 1) t) (sharpPairCost L P N t r) e) ∧
      ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P (N + 1) t‖ ≤
        (∑ n ∈ zetaPrimeLogBand (N + 1), ‖bandWeight L P (N + 1) t n‖) -
          ∑ e ∈ E, edgeSaving (bandWeight L P (N + 1) t) (sharpPairCost L P N t r) e := by
  have hQ : primePairEdges (N + 1) ⊆ zetaPrimeLogBand (N + 1) ×ˢ zetaPrimeLogBand (N + 1) :=
    by unfold primePairEdges; exact Finset.filter_subset _ _
  obtain ⟨E, hE, hmax, hbound⟩ := exists_maximal_pair_savings (zetaPrimeLogBand (N + 1))
    (primePairEdges (N + 1)) hQ (bandWeight L P (N + 1) t) (sharpPairCost L P N t r)
    (fun _ he => sharpPairCost_bound P N t hL hr hr3 he)
  have he : (∑ n ∈ zetaPrimeLogBand (N + 1), bandWeight L P (N + 1) t n) =
      zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P (N + 1) t := by
    unfold bandWeight zetaArithmeticBand
    apply Finset.sum_congr rfl
    intro n hn
    rw [if_pos hn]
  rw [he] at hbound
  exact ⟨E, hE, hmax, hbound⟩

end
end RiemannGaussian.ZetaRieszSharpMatching
