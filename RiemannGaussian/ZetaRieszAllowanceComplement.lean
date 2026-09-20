/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOneSidedArithmetic

/-!
# Auditing the exact improved allowance

The fixed allowance is `antichainBudget - 3/4 * fourCharge`. Balanced
three-prime integers retain their whole charge in its complement. In
particular, the small assigned fraction is not a small unassigned fraction.
-/

namespace RiemannGaussian.ZetaRieszAllowanceComplement
noncomputable section
open scoped BigOperators Classical
open ZetaRieszOneSidedArithmetic ZetaRieszJointAllocation
open ZetaRieszDominantAllocation ZetaRieszPrimeCountFrequency ZetaRieszSperner
open ZetaRieszMaskSupport

/-- The four-prime charge is a sub-sum of the original positive allowance. -/
theorem fourCharge_le {u : ℝ} (hu : 0 ≤ u) (y : ℝ) (j : ℕ) :
    fourCharge u y j ≤ antichainBudget u y j := by
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu _)
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro n _ _
  exact mul_nonneg (weight_nonneg _ _ _) (mul_nonneg
    (middleLayerAllowance_nonneg (SquarefreeVaughanLogSource.length_pos _ _) _) (abs_nonneg _))

/-- Even complete coverage by the credited class leaves a quarter of the old allowance. -/
theorem quarter_antichain_le {u : ℝ} (hu : 0 ≤ u) (y : ℝ) (j : ℕ) :
    (1 / 4 : ℝ) * antichainBudget u y j ≤
      antichainBudget u y j - (3 / 4 : ℝ) * fourCharge u y j := by
  linarith [fourCharge_le hu y j]

/-- Every subfamily outside the credited class is paid in full by the complement. -/
theorem subfamily_le_complement {u : ℝ} (hu : 0 ≤ u) (y : ℝ) (j : ℕ)
    (T : Finset ℕ)
    (hT : T ⊆ nondominantBand u (dyadicMomentOrder j) (dyadicPrimeCount j))
    (hout : ∀ n ∈ T, ¬ FourSavingClass
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n) :
    u ^ (dyadicMomentOrder j + 1) * ∑ n ∈ T,
      weight (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
        (dyadicMomentOrder j) n *
        (middleLayerAllowance (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n *
          |Real.cos (y * Real.log n)|) ≤ antichainBudget u y j - fourCharge u y j := by
  let S := nondominantBand u (dyadicMomentOrder j) (dyadicPrimeCount j)
  let P := FourSavingClass (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
  let f := fun n => weight (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
    (dyadicMomentOrder j) n *
      (middleLayerAllowance (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n *
        |Real.cos (y * Real.log n)|)
  have hf (n : ℕ) : 0 ≤ f n := mul_nonneg (weight_nonneg _ _ _)
    (mul_nonneg (middleLayerAllowance_nonneg (SquarefreeVaughanLogSource.length_pos _ _) _)
      (abs_nonneg _))
  have hsub : T ⊆ S \ S.filter P := by
    intro n hn
    exact Finset.mem_sdiff.mpr ⟨hT hn, fun h => hout n hn (Finset.mem_filter.mp h).2⟩
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf n)
  have he := Finset.sum_sdiff (f := f) (Finset.filter_subset P S)
  have hm := mul_le_mul_of_nonneg_left hs (pow_nonneg hu (dyadicMomentOrder j + 1))
  change _ ≤ u ^ (dyadicMomentOrder j + 1) * ∑ n ∈ S, f n -
    u ^ (dyadicMomentOrder j + 1) * ∑ n ∈ S.filter P, f n
  change u ^ (dyadicMomentOrder j + 1) * ∑ n ∈ T, f n ≤ _
  rw [eq_sub_iff_add_eq.mpr he, mul_sub] at hm
  exact hm

/-- Balanced products retain almost all of their original weight. -/
theorem balanced_weight_lower (A : Finset ℕ) (N : ℕ) {n : ℕ}
    (hn : Squarefree n) (hn1 : 1 < n)
    (hbal : ∀ p ∈ n.primeFactors, Real.log p ≤ Real.log n / 2) :
    (1 - (n.primeFactors.card : ℝ) * Real.exp (-(N : ℝ) / 64)) * amplitude N n ≤
      weight A N n := by
  have hb : boundedShare A N n ≤
      (n.primeFactors.card : ℝ) * Real.exp (-(N : ℝ) / 64) := by
    unfold boundedShare
    split_ifs
    · exact ZetaRieszBalancedCompanion.share_small_of_selected_primes_balanced A N hn hn1
        (fun p hp _ _ => hbal p hp)
    · positivity
  exact mul_le_mul_of_nonneg_right (by linarith)
    (ZetaRieszCosineCarrier.factorial_envelope_nonneg N n)

/-- Every balanced lower-count product in the window survives all existing support deletions. -/
theorem balanced_mem_nondominant (j : ℕ) (hj : 32 ≤ j) {u : ℝ}
    (hu : 1 / 2 < u) (huh : u ≤ Real.exp (-(11 / 16 : ℝ)))
    (hL : (5 / 4 : ℝ) * dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    {n : ℕ} (hn : Squarefree n)
    (hW : n ∈ literalWindow (dyadicMomentOrder j))
    (hk : 3 ≤ n.primeFactors.card) (hK : n.primeFactors.card < dyadicPrimeCount j)
    (hbal : ∀ p ∈ n.primeFactors, Real.log p ≤ Real.log n / 2) :
    n ∈ nondominantBand u (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  let N := dyadicMomentOrder j
  have hN : 0 < (N : ℝ) := by
    have h := four_le_dyadicPrimeCount j
    dsimp [N, dyadicMomentOrder]
    positivity
  have hw := (mem_literalWindow N n).mp hW
  have ht : 0 < Real.log n := by nlinarith [hw.1]
  have hpX (p : ℕ) (hp : p ∈ n.primeFactors) :
      p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 := by
    have hlog : Real.log p < SquarefreeVaughanLogSource.length u N := by
      have := hbal p hp
      change (5 / 4 : ℝ) * N ≤ _ at hL
      nlinarith [hw.2]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    have hX0 : (0 : ℝ) < (((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2)^2 : ℕ) : ℝ) := by positivity
    have he : Real.log (((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2)^2 : ℕ) : ℝ) =
        SquarefreeVaughanLogSource.length u N := by
      simp only [SquarefreeVaughanLogSource.length, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
    exact_mod_cast (Real.log_lt_log_iff hp0 hX0).mp (he ▸ hlog)
  have hm := ZetaRieszMaskSupport.window_mem_originalMask j hj hu huh hL hW hn hk hK hpX
  have hnot : n ∉ cancellingSector u N (dyadicPrimeCount j) := by
    intro h
    obtain ⟨_, _, _, _, _, p, hp, _, _, _, hr⟩ := Finset.mem_filter.mp h
    have hpp := Nat.prime_of_mem_primeFactors hp
    have he : Real.log (n / p : ℕ) = Real.log n - Real.log p := by
      rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors hp) (by exact_mod_cast hpp.ne_zero),
        Real.log_div (by exact_mod_cast hn.ne_zero) (by exact_mod_cast hpp.ne_zero)]
    rw [he] at hr
    have := (div_le_iff₀ ht).mp hr
    linarith [hbal p hp]
  have hret : n ∈ retainedBand u N (dyadicPrimeCount j) := Finset.mem_sdiff.mpr ⟨hm, hnot⟩
  apply Finset.mem_sdiff.mpr
  refine ⟨hret, ?_⟩
  intro h
  obtain ⟨_, _, _, _, p, hp, _, _, hlarge⟩ := Finset.mem_filter.mp h
  linarith [hbal p hp]

end
end RiemannGaussian.ZetaRieszAllowanceComplement
