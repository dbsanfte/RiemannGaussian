/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceWordBank

/-! # Exact canonical ordering of the original acquired physical word bank -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceWordBankSemantics
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeRationalBits SemiprimeSourceWordBankRows SemiprimeSourceWordBank

/-- Canonical coordinate interpretation respects head/tail construction. -/
theorem coordinates_cons {r q : ℕ} (h : Fin r) (t : Word r q) :
    coordinates (Fin.cons h t)=(h.val:ℚ)::coordinates t := by
  simp only [coordinates,List.ofFn_succ,Fin.cons_zero,Fin.cons_succ]

/-- Mapping both factors of a head-major Cartesian list preserves exact ordering. -/
theorem mapped_product {α β γ δ ε : Type*} (xs : List α) (ys : List β)
    (f : α→γ) (g : β→δ) (h : γ×δ→ε) :
    ((xs.map f).product (ys.map g)).map h=
      (xs.product ys).map (fun p => h (f p.1,g p.2)) := by
  simp only [List.product,List.flatMap_map,List.map_flatMap,List.map_map]
  rfl

/-- The ORIGINAL head-major function enumeration has this concrete coordinate recursion. -/
theorem canonical_step (r q : ℕ) :
    ((SemiprimeFiniteEnumerations.words r (q+1)).values.map coordinates)=
      ((List.finRange r).product (SemiprimeFiniteEnumerations.words r q).values).map
        (fun p => (p.1.val:ℚ)::coordinates p.2) := by
  change (((List.finRange r).product (SemiprimeFiniteEnumerations.words r q).values).map
    (fun p => Fin.cons p.1 p.2)).map coordinates = _
  simp only [List.map_map]
  congr 1
  funext p
  exact coordinates_cons p.1 p.2

/-- Exact decoded ordered bank from original dimensions, not a set/permutation relation. -/
theorem rows_values (r Q : ℕ) :
    ((SemiprimeSourceWordBankRows.rows r Q).value.map (List.map RationalWord.value))=
      (SemiprimeFiniteEnumerations.words r Q).values.map coordinates := by
  induction Q with
  | zero => rfl
  | succ q ih =>
    change ((rowsWith (colours r).value (q+1)).value.map (List.map RationalWord.value))=_
    rw [rowsWith_values,colours_values]
    change ((rowsWith (colours r).value q).value.map (List.map RationalWord.value))=_ at ih
    rw [ih,mapped_product,canonical_step]
/-- Actual row cardinality follows the exact canonical coordinate ordering. -/
theorem rows_length (r Q : ℕ) : (SemiprimeSourceWordBankRows.rows r Q).value.length=r^Q := by
  have h := congrArg List.length (rows_values r Q)
  simpa only [List.length_map,SemiprimeFiniteEnumerations.words_length] using h

/-- Actual acquired index values cover precisely the ascending original bank range. -/
theorem ids_values (r Q : ℕ) : (acquire r Q).ids.map SemiprimeBitArithmetic.bitValue=List.range (r^Q) := by
  have h := ascending_values [] (SemiprimeSourceWordBankRows.rows r Q).value.length
  simpa only [acquire,SemiprimeBitArithmetic.bitValue,rows_length,← List.range_eq_range'] using h

/-- Proof-only original finite-word interpretation, absent from every bank runtime. -/
def decode (r Q : ℕ) [NeZero r] (id : List Bool) : Word r Q :=
  ((SemiprimeFiniteEnumerations.words r Q).values[SemiprimeBitArithmetic.bitValue id]?).getD (fun _ => 0)

/-- Reconstruct an ordered finite list by its actual in-range indices. -/
theorem map_range_lookup {α : Type*} (xs : List α) (fallback : α) :
    (List.range xs.length).map (fun i => (xs[i]?).getD fallback)=xs := by
  apply List.ext_getElem
  · simp
  · intro i _ hi
    simp only [List.getElem_map,List.getElem_range,List.getElem?_eq_getElem hi,Option.getD_some]

/-- IDs decode in EXACT original order; this is stronger than coverage/permutation. -/
theorem ids_decode (r Q : ℕ) [NeZero r] :
    (acquire r Q).ids.map (decode r Q)=(SemiprimeFiniteEnumerations.words r Q).values := by
  have h := congrArg (List.map (fun i =>
    ((SemiprimeFiniteEnumerations.words r Q).values[i]?).getD (fun _ => 0))) (ids_values r Q)
  simp only [List.map_map] at h
  change (acquire r Q).ids.map (decode r Q)=_ at h
  rw [← SemiprimeFiniteEnumerations.words_length r Q] at h
  exact h.trans (map_range_lookup _ _)

/-- Every acquired candidate ID is in range, including the zero-dimensional bank. -/
theorem id_lt (r Q : ℕ) (id : List Bool) (hid : id∈(acquire r Q).ids) :
    SemiprimeBitArithmetic.bitValue id < r^Q := by
  have h : SemiprimeBitArithmetic.bitValue id ∈ (acquire r Q).ids.map SemiprimeBitArithmetic.bitValue :=
    List.mem_map.mpr ⟨id,hid,rfl⟩
  rw [ids_values] at h
  exact List.mem_range.mp h

/-- Valid IDs read exactly the original decoded coordinate row. -/
theorem readRow_coordinates (r Q : ℕ) [NeZero r] (id : List Bool) (hid : id∈(acquire r Q).ids) :
    (readRow (acquire r Q) id).value.map RationalWord.value=coordinates (decode r Q id) := by
  have hi := id_lt r Q id hid
  have hr : SemiprimeBitArithmetic.bitValue id < (SemiprimeSourceWordBankRows.rows r Q).value.length := by
    simpa only [rows_length] using hi
  have hc : SemiprimeBitArithmetic.bitValue id < (SemiprimeFiniteEnumerations.words r Q).values.length := by
    simpa only [SemiprimeFiniteEnumerations.words_length] using hi
  have h := congrArg (fun rs : List (List ℚ) => (rs[SemiprimeBitArithmetic.bitValue id]?).getD []) (rows_values r Q)
  rw [readRow_value]
  change (((SemiprimeSourceWordBankRows.rows r Q).value[SemiprimeBitArithmetic.bitValue id]?).getD []).map RationalWord.value=_
  simp only [List.getElem?_map,List.getElem?_eq_getElem hr,List.getElem?_eq_getElem hc,
    Option.map_some,Option.getD_some] at h
  simpa only [decode,List.getElem?_eq_getElem hr,List.getElem?_eq_getElem hc,Option.getD_some] using h

/-- Distinct acquired candidate IDs denote distinct original finite words. -/
theorem decode_injective (r Q : ℕ) [NeZero r] :
    Set.InjOn (decode r Q) {id | id∈(acquire r Q).ids} := by
  apply List.inj_on_of_nodup_map
  rw [ids_decode]
  exact (SemiprimeFiniteEnumerations.words r Q).nodup

end RiemannGaussian.SemiprimeSourceWordBankSemantics
