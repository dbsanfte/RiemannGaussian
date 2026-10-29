/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramHeadBits

/-! # Exact original-coordinate semantics of the physical head key stream
Canonical numeric encodings and Word-valued labels below are proof-side only.
The executed producer still consumes only cached physical keys/rows and IDs.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHistogramHeadRefinement
open SemiprimeBitArithmetic SemiprimeRationalBits
open SemiprimeSourceHistogramHeadBits
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeSourceCompactBits (Compact)
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes

/-- Proof-side unique compact byte string for a natural number. -/
def numberKey (n : ℕ) : List Bool :=
  (SemiprimeSourceCompactBits.trim (SemiprimeSourceOffsetInputsCore.natBits n).bits).bits

/-- The proof encoding has exactly its named numerical value. -/
theorem numberKey_value (n : ℕ) : bitValue (numberKey n)=n := by
  simp only [numberKey,SemiprimeSourceCompactBits.trim_value,
    SemiprimeSourceOffsetInputsCore.natBits_value]

/-- The proof encoding is compact, including literal zero. -/
theorem numberKey_compact (n : ℕ) : Compact (numberKey n) :=
  SemiprimeSourceCompactBits.trim_compact _

/-- Canonical numerical encodings cannot alias. -/
theorem numberKey_injective : Function.Injective numberKey := by
  intro a b h
  simpa only [numberKey_value] using congrArg bitValue h

private theorem compact_lists (xs ys : List (List Bool))
    (hx : ∀ x∈xs,Compact x) (hy : ∀ y∈ys,Compact y)
    (hv : xs.map bitValue=ys.map bitValue) : xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hv
    | cons y ys =>
      have he := List.cons.inj hv
      have hxy := SemiprimeSourceCompactWordIds.compact_value_injective _ _
        (hx x (by simp)) (hy y (by simp)) he.1
      rw [hxy,ih ys (fun z hz => hx z (List.mem_cons_of_mem x hz))
        (fun z hz => hy z (List.mem_cons_of_mem y hz)) he.2]

private theorem finRange_values (Q : ℕ) : (List.finRange Q).map Fin.val=List.range Q := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- Actual acquired coordinate IDs are precisely the canonical numerical bytes. -/
theorem coordinate_ids (Q : ℕ) :
    (SemiprimeSourceCompactWordIds.acquire Q).value=
      (List.finRange Q).map (fun q => numberKey q.val) := by
  apply compact_lists
  · exact SemiprimeSourceCompactWordIds.acquire_compact Q
  · intro key hk
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hk
    exact numberKey_compact q.val
  · rw [SemiprimeSourceCompactWordIds.acquire_values,List.map_map]
    simpa only [Function.comp_def,numberKey_value] using (finRange_values Q).symm

/-- The acquired physical compact colour fields are the original finite coordinates. -/
theorem row_fields (r Q : ℕ) [NeZero r] (id : List Bool)
    (hi : id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    ((SemiprimeSourceWordBank.readRow (SemiprimeSourceCompactWordBank.acquire r Q) id).value.map
      (fun x => (SemiprimeSourceCompactBits.trim x.numerator.magnitude).bits))=
      (List.finRange Q).map (fun q =>
        numberKey ((SemiprimeSourceWordBankSemantics.decode r Q id) q).val) := by
  apply compact_lists
  · intro key hk
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hk
    exact SemiprimeSourceCompactBits.trim_compact _
  · intro key hk
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hk
    exact numberKey_compact _
  · apply (Nat.cast_injective (R:=ℚ)).list_map
    have h := SemiprimeSourceHistogramRowKeys.original_colour_values r Q id hi
    simpa only [List.map_map,Function.comp_def,numberKey_value,
      SemiprimeSourceWordBankRows.coordinates,List.ofFn_eq_map] using h

private theorem keys_fields (qs : List (List Bool)) (row : List RationalWord) :
    SemiprimeSourceHistogramRowKeys.keys qs row=
      (qs.zip (row.map (fun x => (SemiprimeSourceCompactBits.trim x.numerator.magnitude).bits))).map
        (fun p => frame p.1 p.2) := by
  induction qs generalizing row with
  | nil => rfl
  | cons q qs ih => cases row with
    | nil => rfl
    | cons x xs => exact congrArg (List.cons _) (ih xs)

private theorem zip_same {A B C : Type*} (xs : List A) (f : A→B) (g : A→C) :
    (xs.map f).zip (xs.map g)=xs.map (fun x => (f x,g x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.zip_cons_cons,ih]

/-- Original encoded row parsing yields exactly coordinate-major semantic keys. -/
theorem readKeys_semantic (r Q : ℕ) [NeZero r] (id : List Bool)
    (hi : id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    (SemiprimeSourceHistogramRowKeys.readKeys (SemiprimeSourceHistogramRows.acquire r Q)
      (SemiprimeSourceCompactWordIds.acquire Q).value id).keys=
      (List.finRange Q).map (fun q => frame (numberKey q.val)
        (numberKey ((SemiprimeSourceWordBankSemantics.decode r Q id) q).val)) := by
  rw [SemiprimeSourceHistogramRowKeys.readKeys_original r Q id hi,keys_fields,
    coordinate_ids,row_fields r Q id hi,zip_same,List.map_map]
  rfl

/-- Proof-side physical key of one actual original vertex-coordinate occurrence. -/
def headKey (r Q : ℕ) [NeZero r] (fixed : List (List Bool)) (v : ℕ) (q : Fin Q) : List Bool :=
  frame (numberKey q.val)
    (numberKey ((SemiprimeSourceHistogramDictRefinement.labels r Q fixed v) q).val)

/-- Actual key equality is exactly original coordinate/colour equality. -/
theorem headKey_eq_iff (r Q : ℕ) [NeZero r] (fixed : List (List Bool))
    (v w : ℕ) (q t : Fin Q) : headKey r Q fixed v q=headKey r Q fixed w t ↔
      (q.val,((SemiprimeSourceHistogramDictRefinement.labels r Q fixed v) q).val)=
        (t.val,((SemiprimeSourceHistogramDictRefinement.labels r Q fixed w) t).val) := by
  unfold headKey
  rw [SemiprimeSourceHistogramRowKeys.key_eq_iff,Prod.mk.injEq]
  exact and_congr (numberKey_injective.eq_iff) (numberKey_injective.eq_iff)

/-- Actual prefix data discharges the fixed-vertex key interpretation internally. -/
theorem original_one (r Q : ℕ) [NeZero r] (fixed : List (List Bool))
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids)
    (key : List Bool) (hk : Compact key) :
    (SemiprimeSourceHistogramRowKeys.readKeys
      (SemiprimeSourceHistogramRowKeys.acquireCaches r Q).source.dictionary
      (SemiprimeSourceHistogramRowKeys.acquireCaches r Q).coordinates
      (SemiprimeSourceHistogramTrie.stored (SemiprimeSourceHistogramPrefix.acquire fixed).trie key)).keys=
      (List.finRange Q).map (headKey r Q fixed (bitValue key)) := by
  rw [SemiprimeSourceHistogramRowKeys.acquireCaches_dictionary,
    SemiprimeSourceHistogramRowKeys.acquireCaches_coordinates,
    readKeys_semantic r Q _ (SemiprimeSourceHistogramDictRefinement.stored_mem r Q fixed hf key)]
  have hd := SemiprimeSourceHistogramDictRefinement.stored_decode r Q fixed key hk
  rw [hd]
  rfl

/-- Exact original fixed-major occurrence stream, without quadratic term generation. -/
theorem produce_original_keys {n : ℕ} (r Q : ℕ) [NeZero r] (fixed : List (List Bool))
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids)
    (k s : ℕ) (is : List (Fin n)) :
    (produce (SemiprimeSourceHistogramRowKeys.acquireCaches r Q)
      (SemiprimeSourceHistogramPrefix.acquire fixed).trie k s (verticesWith is).value).keys=
      (is.filter (fun v => !(SemiprimeSourceHistogramFeatureBits.active k s v.val))).flatMap
        (fun v => (List.finRange Q).map (headKey r Q fixed v.val)) := by
  rw [produce_keys,verticesWith_value]
  unfold keyList
  rw [List.flatMap_map]
  induction is with
  | nil => rfl
  | cons i is ih =>
    have he := original_one r Q fixed hf (vertex i).value.key (vertex_rep i).1
    rw [(vertex_rep i).2] at he
    have hc : (vertex i).value.code=i.val := rfl
    by_cases ha : SemiprimeSourceHistogramFeatureBits.active k s i.val=true
    · simp only [List.flatMap_cons,hc,ha,ite_true,List.nil_append,
        List.filter_cons,Bool.not_true,Bool.false_eq_true,ite_false,ih]
    · simp only [List.flatMap_cons,hc,ha,Bool.false_eq_true,ite_false,List.filter_cons,
        Bool.not_false,ite_true,List.flatMap_cons]
      rw [he,ih]

end RiemannGaussian.SemiprimeSourceHistogramHeadRefinement
