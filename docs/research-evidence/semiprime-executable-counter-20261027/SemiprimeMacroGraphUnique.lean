/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMacroGraphSemantics
import RiemannGaussian.SemiprimeMacroFlagExtension

/-!
# Uniqueness of actual macro graph extensions

Accepted assignments with the same active source digits have identical literal
word values, flags and Boolean wires. This concerns the actual local tables,
not an assumed transform or flag extension oracle.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeMacroGraphUnique
open scoped BigOperators
open SemiprimeMacroGraph SemiprimeMacroGraphSemantics SemiprimeMacroFermatNetwork
open SemiprimeBooleanNetwork

/-- Canonical graph word checks make equality in the Fermat ring faithful. -/
theorem canonical_word_eq (p : Config) (a b : BitSignal p.r p.t p.digits → Bool)
    (ha : OriginalAccepted p a) (hb : OriginalAccepted p b) (signal : WordSignal p.r p.t)
    (he : (wordNat p a signal : MacroRing p.depth) = (wordNat p b signal : MacroRing p.depth)) :
    wordNat p a signal = wordNat p b signal := by
  exact canonical_nat_unique (2^(macroLength p.depth)+1) _ _
    (by simpa only [p.shape] using all_words_canonical p a ha signal)
    (by simpa only [p.shape] using all_words_canonical p b hb signal) he

/-- All three stages of one transform are fixed by their actual input wires. -/
theorem transform_eq (p : Config) (a b : BitSignal p.r p.t p.digits → Bool)
    (ha : OriginalAccepted p a) (hb : OriginalAccepted p b) (tr : Transform)
    (hin : ∀ k, wordNat p a (inputSignal p tr k) = wordNat p b (inputSignal p tr k)) :
    (∀ j k, wordNat p a (.first tr j k) = wordNat p b (.first tr j k)) ∧
    (∀ j k, wordNat p a (.twiddle tr j k) = wordNat p b (.twiddle tr j k)) ∧
    (∀ k j, wordNat p a (.second tr k j) = wordNat p b (.second tr k j)) := by
  have hf : ∀ j k, wordNat p a (.first tr j k) = wordNat p b (.first tr j k) := by
    intro j k
    apply canonical_word_eq p a b ha hb
    rw [(first_checks p a ha tr j).2.2 k, (first_checks p b hb tr j).2.2 k]
    apply Finset.sum_congr rfl
    intro i _
    rw [hin]
  have ht : ∀ j k, wordNat p a (.twiddle tr j k) = wordNat p b (.twiddle tr j k) := by
    intro j k
    apply canonical_word_eq p a b ha hb
    rw [(scale_checks p a ha tr j k).2.2, (scale_checks p b hb tr j k).2.2, hf]
  refine ⟨hf, ht, ?_⟩
  intro k j
  apply canonical_word_eq p a b ha hb
  rw [(second_checks p a ha tr k).2.2 j, (second_checks p b hb tr k).2.2 j]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [ht]

/-- Actual active source-digit equality determines every physical word. -/
theorem all_words_eq (p : Config) (a b : BitSignal p.r p.t p.digits → Bool)
    (ha : OriginalAccepted p a) (hb : OriginalAccepted p b)
    (hin : ∀ side (i : Fin p.digits),
      wordNat p a (.input side ⟨i.val, lt_of_lt_of_le i.isLt p.cap⟩) =
      wordNat p b (.input side ⟨i.val, lt_of_lt_of_le i.isLt p.cap⟩)) :
    ∀ signal, wordNat p a signal = wordNat p b signal := by
  have hinput : ∀ side (i : Fin (p.r*p.t)),
      wordNat p a (.input side i) = wordNat p b (.input side i) := by
    intro side i
    by_cases hi : i.val < p.digits
    · exact hin side ⟨i.val, hi⟩
    · have ha0 := source_checks p a ha side i
      have hb0 := source_checks p b hb side i
      simp only [dite_eq_right hi] at ha0 hb0
      exact ha0.trans hb0.symm
  have forward := fun side => transform_eq p a b ha hb (.inl side) (by
    intro k; exact hinput side k)
  have hfinal : ∀ side k, wordNat p a (finalSignal p (.inl side) k) =
      wordNat p b (finalSignal p (.inl side) k) := by
    intro side k
    exact (forward side).2.2 _ _
  have hprod : ∀ k, wordNat p a (.product k) = wordNat p b (.product k) := by
    intro k
    apply canonical_word_eq p a b ha hb
    rw [(product_checks p a ha k).2.2, (product_checks p b hb k).2.2,
      hfinal 0 k, hfinal 1 k]
  have inverse := transform_eq p a b ha hb (.inr ()) (by intro k; exact hprod k)
  have hcoeff : ∀ k, wordNat p a (finalSignal p (.inr ()) k) =
      wordNat p b (finalSignal p (.inr ()) k) := by
    intro k; exact inverse.2.2 _ _
  have hcarry : ∀ k (hk : k ≤ p.r*p.t),
      wordNat p a (.carry ⟨k, by omega⟩) = wordNat p b (.carry ⟨k, by omega⟩) := by
    intro k
    induction k with
    | zero => intro hk; exact (carry_endpoints p a ha).1.trans (carry_endpoints p b hb).1.symm
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hca := (carry_checks p a ha ⟨k, by omega⟩).2.2.2
      have hcb := (carry_checks p b hb ⟨k, by omega⟩).2.2.2
      have hc := hcoeff ⟨k, by omega⟩
      rw [hc, hprev] at hca
      have hp : 0 < 2^p.bits := by positivity
      nlinarith
  intro signal
  cases signal with
  | input side i => exact hinput side i
  | first tr j k => cases tr with
    | inl side => exact (forward side).1 j k
    | inr u => cases u; exact inverse.1 j k
  | twiddle tr j k => cases tr with
    | inl side => exact (forward side).2.1 j k
    | inr u => cases u; exact inverse.2.1 j k
  | second tr k j => cases tr with
    | inl side => exact (forward side).2.2 k j
    | inr u => cases u; exact inverse.2.2 k j
  | product k => exact hprod k
  | carry k => exact hcarry k.val (by have := k.isLt; omega)

/-- Equality of literal decoded Boolean words is equality at every bit port. -/
theorem readWord_injective (width : ℕ) : Function.Injective (readWord width) := by
  intro a b h
  apply (bitPortsEquiv width).symm.injective
  apply BitVec.eq_of_toNat_eq
  exact h

/-- Accepted extensions with the same active source digits are identical. -/
theorem accepted_unique (p : Config) (a b : BitSignal p.r p.t p.digits → Bool)
    (ha : OriginalAccepted p a) (hb : OriginalAccepted p b)
    (hin : ∀ side (i : Fin p.digits),
      wordNat p a (.input side ⟨i.val, lt_of_lt_of_le i.isLt p.cap⟩) =
      wordNat p b (.input side ⟨i.val, lt_of_lt_of_le i.isLt p.cap⟩)) : a = b := by
  have hw := all_words_eq p a b ha hb hin
  have hdigit : ∀ side i, flagValue p a (.digit side i) = flagValue p b (.digit side i) := by
    intro side i
    have hca := (source_checks p a ha side ⟨i.val, lt_of_lt_of_le i.isLt p.cap⟩)
    have hcb := (source_checks p b hb side ⟨i.val, lt_of_lt_of_le i.isLt p.cap⟩)
    simp only [i.isLt, dite_true] at hca hcb
    rw [hca.2 ⟨i, rfl⟩, hcb.2 ⟨i, rfl⟩, hw]
  let flags := fun side i => flagValue p a (.digit side i)
  have hfa := SemiprimeMacroFlagExtension.unique_flags p.digits_pos flags (flagValue p a)
    (fun _ _ => rfl) (by
      intro side i
      simpa only [SemiprimeMacroFlagExtension.previous, previousFlag] using or_checks p a ha side i)
  have hfb := SemiprimeMacroFlagExtension.unique_flags p.digits_pos flags (flagValue p b)
    (fun side i => (hdigit side i).symm) (by
      intro side i
      simpa only [SemiprimeMacroFlagExtension.previous, previousFlag, flags, hdigit] using or_checks p b hb side i)
  have hflags : flagValue p a = flagValue p b := hfa.trans hfb.symm
  funext signal
  cases signal with
  | inl pair =>
    obtain ⟨word, bit⟩ := pair
    have he := readWord_injective (p.r*p.t+1) (hw word)
    exact congrFun he bit
  | inr flag => exact congrFun hflags flag

end RiemannGaussian.SemiprimeMacroGraphUnique

#print axioms RiemannGaussian.SemiprimeMacroGraphUnique.accepted_unique
