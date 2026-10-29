/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramPrefix
import RiemannGaussian.SemiprimeSourceHistogramFeatureBits
import RiemannGaussian.SemiprimeSourceCompactWordBank

/-! # Actual acquired prefix dictionaries discharge semantic label interfaces
All word functions below are specifications. The runtime dictionary is exactly
Prefix.acquire on selected IDs from the actual compact candidate bank.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeSourceHistogramDictRefinement
open OAI.Algorithms.SubexponentialSAT.LocalExpectation
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeBitArithmetic
open SemiprimeSourceCompactBits (Compact)
open SemiprimeSourceHistogramTrie (stored value)

/-- Original semantic assignment of the actually supplied reverse prefix. -/
def labels (r Q : ℕ) [NeZero r] (fixed : List (List Bool)) : ℕ → Word r Q :=
  decode (SemiprimeSourceWordBankSemantics.decode r Q [])
    (fixed.map (SemiprimeSourceWordBankSemantics.decode r Q))

/-- Original reverse-prefix decoding commutes with semantic interpretation. -/
theorem decoder_map {A B : Type*} (f : A → B) (default : A) (xs : List A) (i : ℕ) :
    decode (f default) (xs.map f) i=f (decode default xs i) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : i=xs.length <;> simp [decode,h,ih]

/-- The final appended position retains the original total default convention. -/
theorem getD_append_single {A : Type*} (xs : List A) (x default : A) (i : ℕ) :
    ((xs++[x])[i]?).getD default=
      if i=xs.length then x else (xs[i]?).getD default := by
  induction xs generalizing i with
  | nil => cases i <;> simp
  | cons y ys ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i

/-- Literal original decoder is lookup in the reversed prefix, including absence. -/
theorem decoder_reverse {A : Type*} (default : A) (xs : List A) (i : ℕ) :
    decode default xs i=(xs.reverse[i]?).getD default := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons,getD_append_single,List.length_reverse]
    by_cases h : i=xs.length <;> simp [decode,h,ih]

/-- Exact source labels agree with the previously proved original environment. -/
theorem labels_original (r Q : ℕ) [NeZero r] (fixed : List (List Bool)) :
    SemiprimeMaterializedScoreEnvironment.denote
      (SemiprimeMaterializedScoreEnvironment.baseEnvironment
        (SemiprimeSourceWordBankSemantics.decode r Q [])
        (fixed.map (SemiprimeSourceWordBankSemantics.decode r Q)))=labels r Q fixed :=
  SemiprimeMaterializedScoreEnvironment.denote_baseEnvironment _ _

/-- A physical trim is an exact byte identity on an actually compact input. -/
theorem trim_eq (bits : List Bool) (hc : Compact bits) :
    (SemiprimeSourceCompactBits.trim bits).bits=bits :=
  SemiprimeSourceCompactWordIds.compact_value_injective _ _
    (SemiprimeSourceCompactBits.trim_compact bits) hc
    (SemiprimeSourceCompactBits.trim_value bits)

/-- Every dictionary payload is an actual acquired candidate, even for arbitrary
raw/absent query strings. This is an invariant derived from actual prefix data. -/
theorem stored_mem (r Q : ℕ) [NeZero r] (fixed : List (List Bool))
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids)
    (key : List Bool) :
    stored (SemiprimeSourceHistogramPrefix.acquire fixed).trie key∈
      (SemiprimeSourceCompactWordBank.acquire r Q).ids := by
  induction fixed with
  | nil =>
    simpa only [SemiprimeSourceHistogramPrefix.acquire,SemiprimeSourceHistogramTrie.stored_empty] using
      SemiprimeSourceCompactWordBank.default_mem r Q
  | cons id ids ih =>
    have hid := hf id List.mem_cons_self
    have hc := SemiprimeSourceCompactWordBank.ids_compact r Q id hid
    change stored (SemiprimeSourceHistogramTrieStore.put
      (SemiprimeSourceHistogramPrefix.acquire ids).trie
      (SemiprimeSourceHistogramPrefix.acquire ids).nextKey
      (SemiprimeSourceCompactBits.trim id).bits).trie key∈_
    rw [SemiprimeSourceHistogramTrieStore.put_stored]
    split_ifs
    · rw [trim_eq id hc]
      exact hid
    · exact ih (fun x hx => hf x (List.mem_cons_of_mem id hx))

/-- An actual dictionary read denotes the original word at the represented key. -/
theorem stored_decode (r Q : ℕ) [NeZero r] (fixed : List (List Bool))
    (key : List Bool) (hk : Compact key) :
    SemiprimeSourceWordBankSemantics.decode r Q
      (stored (SemiprimeSourceHistogramPrefix.acquire fixed).trie key)=
        labels r Q fixed (bitValue key) := by
  rw [SemiprimeSourceHistogramPrefix.stored_eq fixed key hk]
  unfold SemiprimeSourceHistogramPrefix.expected labels
  rw [decoder_map,decoder_reverse]
  simp only [SemiprimeSourceWordBankSemantics.decode,SemiprimeSourceCompactBits.trim_value]

/-- The concrete original prefix and compact acquired bank discharge the
feature producer's INTERNAL dictionary equality relation for every code bound. -/
theorem dict_rep (r Q : ℕ) [NeZero r] (fixed : List (List Bool)) (N : ℕ)
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    SemiprimeSourceHistogramFeatureBits.DictRep
      (SemiprimeSourceHistogramPrefix.acquire fixed).trie (labels r Q fixed) N := by
  intro a b ka kb ha hb
  have hka := stored_decode r Q fixed ka ha.1
  have hkb := stored_decode r Q fixed kb hb.1
  rw [ha.2.1] at hka
  rw [hb.2.1] at hkb
  constructor
  · intro h
    exact hka.symm.trans ((congrArg (SemiprimeSourceWordBankSemantics.decode r Q) h).trans hkb)
  · intro h
    exact SemiprimeSourceCompactWordBank.decode_injective r Q
      (stored_mem r Q fixed hf ka) (stored_mem r Q fixed hf kb)
      (hka.trans (h.trans hkb.symm))

/-- Actual original selected-ID membership supplies every dictionary value cap. -/
theorem count_cap (r Q : ℕ) [NeZero r] (fixed : List (List Bool))
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    SemiprimeSourceHistogramTrieBounds.CountCap
      (SemiprimeSourceHistogramPrefix.acquire fixed).trie (r^Q) := by
  intro key
  exact (SemiprimeSourceCompactWordBank.id_lt r Q _ (stored_mem r Q fixed hf key)).le

end RiemannGaussian.SemiprimeSourceHistogramDictRefinement
