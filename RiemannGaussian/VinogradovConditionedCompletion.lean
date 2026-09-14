/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovSignedTailMoment

/-!
# Coarse block counts with actual signed tail completions

The complete translation keeps arbitrary integer coefficients on both the
blocks and tails. Literal positive residue-window tails force the original
degree-specific congruences. Counting exact row fibres before using their
normalized Vinogradov budget combines the coarse congruence count with all
finite signed tail completions for each fixed opposite block.

The counted block entries are canonical representatives modulo p^(k*b).
No arbitrary-height block lifting, singular conditioning or efficient
high-moment iteration is claimed by this finite completion count.
-/

namespace RiemannGaussian.VinogradovConditionedCompletion
noncomputable section
open scoped BigOperators Classical

/-- Both sets of original integer coefficients survive common translation. -/
theorem translated_weighted_moment_equation {k r n : ℕ}
    (c x y : Fin k → ℤ) (tau v w : Fin r → ℤ) (eta : ℤ)
    (h : ∀ d, 1 ≤ d → d ≤ n →
      (∑ i, c i * x i ^ d) + (∑ i, tau i * v i ^ d) =
        (∑ i, c i * y i ^ d) + ∑ i, tau i * w i ^ d) :
    (∑ i, c i * (x i - eta) ^ n) + (∑ i, tau i * (v i - eta) ^ n) =
      (∑ i, c i * (y i - eta) ^ n) + ∑ i, tau i * (w i - eta) ^ n := by
  simp only [VinogradovConditionedMoment.translated_weighted_power_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have he : (∑ i, c i * x i ^ d) + (∑ i, tau i * v i ^ d) =
      (∑ i, c i * y i ^ d) + ∑ i, tau i * w i ^ d := by
    by_cases hd0 : d = 0
    · subst d
      simp
    · exact h d (by omega) (by simpa using Finset.mem_range.mp hd)
  rw [← mul_add, ← mul_add, he]

/-- Arbitrary integer tail weights retain the actual degree divisibilities. -/
theorem conditioned_weighted_power_difference {p b k r n : ℕ}
    (c x y : Fin k → ℤ) (tau v w : Fin r → ℤ) (eta : ℤ)
    (hv : ∀ i, (p : ℤ) ^ b ∣ v i - eta)
    (hw : ∀ i, (p : ℤ) ^ b ∣ w i - eta)
    (h : ∀ d, 1 ≤ d → d ≤ n →
      (∑ i, c i * x i ^ d) + (∑ i, tau i * v i ^ d) =
        (∑ i, c i * y i ^ d) + ∑ i, tau i * w i ^ d) :
    (p : ℤ) ^ (n * b) ∣ (∑ i, c i * (x i - eta) ^ n) -
      ∑ i, c i * (y i - eta) ^ n := by
  have he := translated_weighted_moment_equation c x y tau v w eta h
  have hx : (∑ i, c i * (x i - eta) ^ n) - (∑ i, c i * (y i - eta) ^ n) =
      (∑ i, tau i * (w i - eta) ^ n) - ∑ i, tau i * (v i - eta) ^ n := by linarith
  rw [hx]
  apply dvd_sub
  · apply Finset.dvd_sum
    intro i hi
    apply dvd_mul_of_dvd_right
    simpa only [← pow_mul, mul_comm b n] using pow_dvd_pow_of_dvd (hw i) n
  · apply Finset.dvd_sum
    intro i hi
    apply dvd_mul_of_dvd_right
    simpa only [← pow_mul, mul_comm b n] using pow_dvd_pow_of_dvd (hv i) n

/-- The exact finite pair count keeps every original row fibre. -/
theorem card_pairs_eq_sum_fibres {α β : Type*} [Fintype α] [Fintype β]
    (P : α → β → Prop) [DecidableRel P] :
    (Finset.univ.filter (fun p : α × β => P p.1 p.2)).card =
      ∑ a, (Finset.univ.filter (P a)).card := by
  simp only [Finset.card_filter, Fintype.sum_prod_type]

/-- Support restriction keeps the exact count of each surviving row. -/
theorem card_pairs_eq_sum_supported_fibres {α β : Type*} [Fintype α] [Fintype β]
    (P : α → β → Prop) [DecidableRel P] (S : Finset α)
    (hsupport : ∀ a b, P a b → a ∈ S) :
    (Finset.univ.filter (fun p : α × β => P p.1 p.2)).card =
      ∑ a ∈ S, (Finset.univ.filter (P a)).card := by
  rw [card_pairs_eq_sum_fibres]
  symm
  apply Finset.sum_subset (Finset.subset_univ S)
  intro a ha hna
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  exact hna (hsupport a b (Finset.mem_filter.mp hb).2)

/-- A row budget is spent only after retaining the exact supported sum. -/
theorem card_pairs_le_support_mul {α β : Type*} [Fintype α] [Fintype β]
    (P : α → β → Prop) [DecidableRel P] (S : Finset α) (C : ℝ)
    (hsupport : ∀ a b, P a b → a ∈ S)
    (hrow : ∀ a ∈ S, ((Finset.univ.filter (P a)).card : ℝ) ≤ C) :
    ((Finset.univ.filter (fun p : α × β => P p.1 p.2)).card : ℝ) ≤ (S.card : ℝ) * C := by
  rw [card_pairs_eq_sum_supported_fibres P S hsupport, Nat.cast_sum]
  calc
    (∑ a ∈ S, ((Finset.univ.filter (P a)).card : ℝ)) ≤ ∑ _a ∈ S, C :=
      Finset.sum_le_sum hrow
    _ = (S.card : ℝ) * C := by simp

/-- Literal finite positive tail entries in the prime-power class of eta. -/
abbrev PrimeTailWindow (p b : ℕ) (eta : ℤ) (X : ℕ) :=
  VinogradovResidueMoment.ResidueWindow (p ^ b) (eta : ZMod (p ^ b)).val X

/-- Original complete signed block equations with actual finite tails. -/
def blockTailEquation {p k b r X : ℕ} {eta : ℤ}
    (colour : Fin k → Bool) (tau : Fin r → Bool) (y : Fin k → ℤ)
    (x : Fin k → Fin (p ^ (k * b)))
    (vw : (Fin r → PrimeTailWindow p b eta X) × (Fin r → PrimeTailWindow p b eta X)) : Prop :=
  ∀ i : Fin k,
    (∑ j, VinogradovSignedCongruence.sign (colour j) * ((x j).val : ℤ) ^ (i.val + 1)) +
      (∑ j, VinogradovSignedCongruence.sign (tau j) *
        ((vw.1 j).val.val + 1 : ℤ) ^ (i.val + 1)) =
    (∑ j, VinogradovSignedCongruence.sign (colour j) * y j ^ (i.val + 1)) +
      ∑ j, VinogradovSignedCongruence.sign (tau j) *
        ((vw.2 j).val.val + 1 : ℤ) ^ (i.val + 1)

/-- A finite signed tail completion forces every original block congruence. -/
theorem blockTailEquation_congruence {p k b r X : ℕ} [Fact p.Prime] {eta : ℤ}
    (colour : Fin k → Bool) (tau : Fin r → Bool) (y : Fin k → ℤ)
    (x : Fin k → Fin (p ^ (k * b)))
    (vw : (Fin r → PrimeTailWindow p b eta X) × (Fin r → PrimeTailWindow p b eta X))
    (h : blockTailEquation colour tau y x vw) (i : Fin k) :
    (p : ℤ) ^ ((i.val + 1) * b) ∣
      (∑ j, VinogradovSignedCongruence.sign (colour j) * (((x j).val : ℤ) - eta) ^ (i.val + 1)) -
      ∑ j, VinogradovSignedCongruence.sign (colour j) * (y j - eta) ^ (i.val + 1) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  let : NeZero (p ^ b) := ⟨pow_ne_zero b hp⟩
  have htail (z : PrimeTailWindow p b eta X) : (p : ℤ) ^ b ∣ ((z.val.val + 1 : ℕ) : ℤ) - eta := by
    have hz := (VinogradovResidueMoment.residue_mod_iff_dvd_sub eta (z.val.val + 1)).mp z.property
    simpa only [Nat.cast_pow] using hz
  apply conditioned_weighted_power_difference
    (fun j => VinogradovSignedCongruence.sign (colour j)) (fun j => ((x j).val : ℤ)) y
    (fun j => VinogradovSignedCongruence.sign (tau j))
    (fun j => ((vw.1 j).val.val + 1 : ℤ)) (fun j => ((vw.2 j).val.val + 1 : ℤ)) eta
  · intro j
    simpa only [Nat.cast_add, Nat.cast_one] using htail (vw.1 j)
  · intro j
    simpa only [Nat.cast_add, Nat.cast_one] using htail (vw.2 j)
  · intro d hd hdi
    have he := h ⟨d - 1, by omega⟩
    simpa only [Nat.sub_add_cancel hd] using he

/-- Every fixed original block has the proved finite signed tail budget. -/
theorem blockTailEquation_card_le {p k b r X : ℕ} [Fact p.Prime] {eta : ℤ}
    (colour : Fin k → Bool) (tau : Fin r → Bool) (y : Fin k → ℤ)
    (x : Fin k → Fin (p ^ (k * b))) :
    ((Finset.univ.filter (blockTailEquation (eta := eta) (X := X) colour tau y x)).card : ℝ) ≤
      VinogradovMeanValue.meanValue r k (X / p ^ b + 1) := by
  unfold blockTailEquation
  convert VinogradovSignedTailMoment.signed_tail_completions_le_meanValue
      (q := p ^ b) (xi := (eta : ZMod (p ^ b)).val) (X := X)
      (pow_ne_zero b (Fact.out : p.Prime).ne_zero) tau k
      (fun j => VinogradovSignedCongruence.sign (colour j)) (fun j => ((x j).val : ℤ)) y using 1
  congr 2
  ext vw
  simp

/-- Count actual coarse blocks and all their finite signed tail completions,
spending the full normalized mean value only after the exact row sum. -/
theorem conditioned_complete_count_le {p k a b r X : ℕ} [Fact p.Prime]
    (hkp : k < p) (hk : 0 < k) (hab : a ≤ b)
    (colour : Fin k → Bool) (tau : Fin r → Bool) (xi : ℕ) (eta : ℤ) (y : Fin k → ℤ) :
    ((Finset.univ.filter (fun xv : (Fin k → Fin (p ^ (k * b))) ×
        ((Fin r → PrimeTailWindow p b eta X) × (Fin r → PrimeTailWindow p b eta X)) =>
      (∀ j, (xv.1 j).val % p ^ a = xi) ∧
      Function.Injective (fun j => (((xv.1 j).val / p ^ a : ℕ) : ZMod p)) ∧
      blockTailEquation colour tau y xv.1 xv.2)).card : ℝ) ≤
    ((p ^ ((a + b) * (k * (k - 1) / 2)) *
      VinogradovSignedCongruence.colourFactorial colour : ℕ) : ℝ) *
      VinogradovMeanValue.meanValue r k (X / p ^ b + 1) := by
  classical
  let S := Finset.univ.filter (fun x : Fin k → Fin (p ^ (k * b)) =>
    (∀ j, (x j).val % p ^ a = xi) ∧
    Function.Injective (fun j => (((x j).val / p ^ a : ℕ) : ZMod p)) ∧ ∀ i : Fin k,
    (p : ℤ) ^ ((i.val + 1) * b) ∣
      (∑ j, VinogradovSignedCongruence.sign (colour j) * (((x j).val : ℤ) - eta) ^ (i.val + 1)) -
      ∑ j, VinogradovSignedCongruence.sign (colour j) * (y j - eta) ^ (i.val + 1))
  let P (x : Fin k → Fin (p ^ (k * b)))
      (vw : (Fin r → PrimeTailWindow p b eta X) × (Fin r → PrimeTailWindow p b eta X)) :=
    (∀ j, (x j).val % p ^ a = xi) ∧
    Function.Injective (fun j => (((x j).val / p ^ a : ℕ) : ZMod p)) ∧
    blockTailEquation colour tau y x vw
  have hs : ∀ x vw, P x vw → x ∈ S := by
    intro x vw hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.1, hx.2.1,
      blockTailEquation_congruence colour tau y x vw hx.2.2⟩
  have hr (x) (hx : x ∈ S) : ((Finset.univ.filter (P x)).card : ℝ) ≤
      VinogradovMeanValue.meanValue r k (X / p ^ b + 1) := by
    have hsub : Finset.univ.filter (P x) ⊆
        Finset.univ.filter (blockTailEquation (eta := eta) (X := X) colour tau y x) := by
      intro vw hvw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hvw).2.2.2⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (blockTailEquation_card_le colour tau y x)
  have hb := card_pairs_le_support_mul P S _ hs hr
  have hc := VinogradovCoarseCongruence.conditioned_residue_card_le hkp hk hab colour xi eta
    (fun i => ∑ j, VinogradovSignedCongruence.sign (colour j) * (y j - eta) ^ (i.val + 1))
  have hcR : (S.card : ℝ) ≤ ((p ^ ((a + b) * (k * (k - 1) / 2)) *
      VinogradovSignedCongruence.colourFactorial colour : ℕ) : ℝ) := by exact_mod_cast hc
  exact hb.trans (mul_le_mul_of_nonneg_right hcR (by
    rw [VinogradovMeanValue.meanValue_eq_count]
    positivity))

end
end RiemannGaussian.VinogradovConditionedCompletion
