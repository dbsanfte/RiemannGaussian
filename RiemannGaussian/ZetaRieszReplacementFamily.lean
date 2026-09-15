/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszReplacementPhase

/-!
# Disjoint replacements in the whole original carrier

Retain the actual prime support, cutoff and full complex amplitudes.
Quantitative pair bounds do not establish source-scale saving of the
whole signed carrier or a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszReplacementFamily
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open ZetaRieszPrimeReplacement ZetaRieszReplacementPhase ZetaRieszConditionedEnergy

/-- All common cofactors for which both original integers lie in the
literal band and the two smaller profiles are saturated. These are finite
arithmetic tests, not a cancellation or zero-location premise. -/
def replacementCofactors (L : ℝ) (N a b q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (2 ^ (32 * N))).filter (fun n =>
    Squarefree n ∧ n ≠ 1 ∧ ¬ a ∣ n ∧ ¬ b ∣ n ∧ ¬ q ∣ n ∧
    Real.log (a * n : ℕ) ≤ L ∧ Real.log (b * n : ℕ) ≤ L ∧
    q * n ∈ zetaPrimeLogBand N ∧ a * (b * n) ∈ zetaPrimeLogBand N)

/-- Both complete integer families, including every retained cofactor,
are selected in the original band before any pair norm is taken. -/
def replacementBand (L : ℝ) (N a b q : ℕ) : Finset ℕ :=
  (replacementCofactors L N a b q).image (fun n => q * n) ∪
    (replacementCofactors L N a b q).image (fun n => a * (b * n))

/-- The selected family is a genuine subset of the original carrier. -/
theorem replacementBand_subset (L : ℝ) (N a b q : ℕ) :
    replacementBand L N a b q ⊆ zetaPrimeLogBand N := by
  intro k hk
  rcases Finset.mem_union.mp hk with hk | hk
  · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    exact (Finset.mem_filter.mp hn).2.2.2.2.2.2.2.2.1
  · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    exact (Finset.mem_filter.mp hn).2.2.2.2.2.2.2.2.2

/-- Prime support forbids every collision between the two families.
The same original integer cannot be spent in two different matches. -/
theorem replacement_images_disjoint (L : ℝ) (N : ℕ) {a b q : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hq : q.Prime) (hqa : q ≠ a) (hqb : q ≠ b) :
    Disjoint ((replacementCofactors L N a b q).image (fun n => q * n))
      ((replacementCofactors L N a b q).image (fun n => a * (b * n))) := by
  apply Finset.disjoint_left.mpr
  intro k hk1 hk2
  obtain ⟨n, hn, hnk⟩ := Finset.mem_image.mp hk1
  obtain ⟨m, hm, hmk⟩ := Finset.mem_image.mp hk2
  have hqm : ¬ q ∣ m := (Finset.mem_filter.mp hm).2.2.2.2.2.1
  have hqbm : ¬ q ∣ b * m := not_dvd_prime_mul hq hb hqb hqm
  have hqabm : ¬ q ∣ a * (b * m) := not_dvd_prime_mul hq ha hqa hqbm
  apply hqabm
  rw [hmk, ← hnk]
  exact dvd_mul_right q n

/-- The selected original sum is exactly a sum of disjoint signed
pairs, with both families' amplitudes and phases intact. -/
theorem sum_replacementBand_eq_pairs {α : Type*} [AddCommMonoid α]
    (L : ℝ) (N : ℕ) {a b q : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hq : q.Prime) (hqa : q ≠ a) (hqb : q ≠ b)
    (f : ℕ → α) :
    (∑ k ∈ replacementBand L N a b q, f k) =
      ∑ n ∈ replacementCofactors L N a b q, (f (q * n) + f (a * (b * n))) := by
  rw [replacementBand, Finset.sum_union (replacement_images_disjoint L N ha hb hq hqa hqb)]
  rw [Finset.sum_image (fun n _ m _ h => Nat.eq_of_mul_eq_mul_left hq.pos h),
    Finset.sum_image (fun n _ m _ h => Nat.eq_of_mul_eq_mul_left hb.pos
      (Nat.eq_of_mul_eq_mul_left ha.pos h)), Finset.sum_add_distrib]

/-- The entire selected original arithmetic class has an independent
prime-gap bound. Selection, saturation and support are all discharged
from its literal definition, and no double counting occurs. -/
theorem norm_replacementBand_le_gap (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hr3 : r ≤ 3 / 2)
    {a b q : ℕ} (ha : a.Prime) (hb : b.Prime) (hq : q.Prime)
    (hab : a ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) :
    ‖∑ k ∈ replacementBand L (N + 1) a b q, bandWeight L P (N + 1) t k‖ ≤
      (∑ n ∈ replacementCofactors L (N + 1) a b q,
        replacementAllowance L P N t r a b q n) *
          |Real.log q - Real.log (a * b : ℕ)| := by
  rw [sum_replacementBand_eq_pairs L (N + 1) ha hb hq hqa hqb]
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro n hn
  obtain ⟨_, hs, hn1, han, hbn, hqn, haL, hbL, hQ, hAB⟩ := Finset.mem_filter.mp hn
  exact norm_bandWeight_replacement_pair_le_gap P N t hL hr hr3
    ha hb hq hab han hbn hqn hs hn1 haL hbL hQ hAB

/-- The complete original carrier splits exactly into the selected
matched class and its actual unmatched remainder. Neither is dropped. -/
theorem actual_band_eq_replacement_add_remainder (L : ℝ) (P : Polynomial ℂ)
    (N : ℕ) (t : ℝ) (a b q : ℕ) :
    zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t =
      (∑ k ∈ replacementBand L N a b q, bandWeight L P N t k) +
        ∑ k ∈ zetaPrimeLogBand N \ replacementBand L N a b q, bandWeight L P N t k := by
  have hs : (∑ k ∈ zetaPrimeLogBand N, bandWeight L P N t k) =
      zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t := by
    unfold bandWeight zetaArithmeticBand
    apply Finset.sum_congr rfl
    intro n hn
    rw [if_pos hn]
  rw [← hs, add_comm]
  exact (Finset.sum_sdiff (replacementBand_subset L N a b q)).symm

/-- Both independently proved costs remain available. Each pair pays
the better one, preserving phase resonances as well as small integer gaps. -/
def pairCost (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t r : ℝ) (a b q n : ℕ) : ℝ :=
  min (replacementAllowance L P N t r a b q n * |Real.log q - Real.log (a * b : ℕ)|)
    (phaseReplacementCost L P N t r a b q n)

/-- A nonnegative saving for one literal pair, clipped at zero so that
an unhelpful gap estimate is never substituted for its better triangle bound. -/
def pairSaving (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t r : ℝ) (a b q n : ℕ) : ℝ :=
  max (‖bandWeight L P (N + 1) t (q * n)‖ + ‖bandWeight L P (N + 1) t (a * (b * n))‖ -
    pairCost L P N t r a b q n) 0

/-- The saving budget uses every disjoint match in the selected
arithmetic class and remains an explicit finite quantity. -/
def totalSaving (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t r : ℝ) (a b q : ℕ) : ℝ :=
  ∑ n ∈ replacementCofactors L (N + 1) a b q, pairSaving L P N t r a b q n

/-- The new arithmetic budget cannot worsen the ordinary triangle
bound, even when a particular match has no certified saving. -/
theorem totalSaving_nonneg (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t r : ℝ) (a b q : ℕ) :
    0 ≤ totalSaving L P N t r a b q :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)

/-- Keep the stronger of a proved pair bound and the ordinary
triangle bound, expressing its gain as a nonnegative subtraction. -/
theorem norm_pair_le_sub_saving (z w : ℂ) {C : ℝ} (hC : ‖z + w‖ ≤ C) :
    ‖z + w‖ ≤ ‖z‖ + ‖w‖ - max (‖z‖ + ‖w‖ - C) 0 := by
  by_cases h : 0 ≤ ‖z‖ + ‖w‖ - C
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right (le_of_not_ge h), sub_zero]
    exact norm_add_le _ _

/-- The entire selected class pays its certified pair savings before
the sum across pairs is relaxed. All pair supports and amplitudes are actual. -/
theorem norm_replacementBand_le_mass_sub_saving (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hr3 : r ≤ 3 / 2)
    {a b q : ℕ} (ha : a.Prime) (hb : b.Prime) (hq : q.Prime)
    (hab : a ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) :
    ‖∑ k ∈ replacementBand L (N + 1) a b q, bandWeight L P (N + 1) t k‖ ≤
      (∑ k ∈ replacementBand L (N + 1) a b q, ‖bandWeight L P (N + 1) t k‖) -
        totalSaving L P N t r a b q := by
  rw [sum_replacementBand_eq_pairs L (N + 1) ha hb hq hqa hqb,
    sum_replacementBand_eq_pairs L (N + 1) ha hb hq hqa hqb, totalSaving,
    ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  obtain ⟨_, hs, hn1, han, hbn, hqn, haL, hbL, hQ, hAB⟩ := Finset.mem_filter.mp hn
  apply norm_pair_le_sub_saving
  exact le_min
    (norm_bandWeight_replacement_pair_le_gap P N t hL hr hr3
      ha hb hq hab han hbn hqn hs hn1 haL hbL hQ hAB)
    (norm_bandWeight_replacement_pair_le_phase P N t hL hr hr3
      ha hb hq hab han hbn hqn hs hn1 haL hbL hQ hAB)

/-- A whole-carrier arithmetic bound with an explicit nonnegative
subtraction for every selected disjoint prime-to-product match. The exact
signed decomposition remains upstream. No source-scale lower bound on this
saving, asymptotic decay, or zero-free conclusion is asserted. -/
theorem norm_actual_band_le_mass_sub_saving (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hr3 : r ≤ 3 / 2)
    {a b q : ℕ} (ha : a.Prime) (hb : b.Prime) (hq : q.Prime)
    (hab : a ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) :
    ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P (N + 1) t‖ ≤
      (∑ k ∈ zetaPrimeLogBand (N + 1), ‖bandWeight L P (N + 1) t k‖) -
        totalSaving L P N t r a b q := by
  have hs : (∑ k ∈ replacementBand L (N + 1) a b q, ‖bandWeight L P (N + 1) t k‖) +
      (∑ k ∈ zetaPrimeLogBand (N + 1) \ replacementBand L (N + 1) a b q,
        ‖bandWeight L P (N + 1) t k‖) =
      ∑ k ∈ zetaPrimeLogBand (N + 1), ‖bandWeight L P (N + 1) t k‖ := by
    rw [add_comm]
    exact Finset.sum_sdiff (replacementBand_subset L (N + 1) a b q)
  rw [actual_band_eq_replacement_add_remainder L P (N + 1) t a b q]
  apply (norm_add_le _ _).trans
  have hh := add_le_add (norm_replacementBand_le_mass_sub_saving P N t hL hr hr3 ha hb hq hab hqa hqb)
    (norm_sum_le (zetaPrimeLogBand (N + 1) \ replacementBand L (N + 1) a b q)
      (fun k => bandWeight L P (N + 1) t k))
  linarith

end
end RiemannGaussian.ZetaRieszReplacementFamily
