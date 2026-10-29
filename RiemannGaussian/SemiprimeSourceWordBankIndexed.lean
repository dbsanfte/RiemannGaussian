/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceWordBankBounds
import RiemannGaussian.SemiprimeSourceWordMenuOrder

/-! # Original indexed-menu adapter for the acquired physical bank
The canonical lookup decoder occurs only in proof specifications, never in the
bank/ID acquisition or physical row-reader data paths.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceWordBankIndexed
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeSourceWordBank SemiprimeSourceWordBankSemantics SemiprimeSourceWordBankBounds
open SemiprimeSourceWordBankRows SemiprimeRationalBits SemiprimeBitArithmetic SemiprimeBitProductSort

/-- The actual bank has exactly the original candidate cardinality. -/
theorem acquire_length (r Q : ℕ) : (acquire r Q).rows.length=r^Q := rows_length r Q

/-- Physical IDs decode to the exact original indexed zero-first/filter-tail menu. -/
theorem ids_indexed (n F r Q : ℕ) [NeZero r] (arity : Fin F → ℕ) :
    (acquire r Q).ids.map (decode r Q)=
      (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value.wordFirst::
        (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value.wordTail := by
  rw [ids_decode]
  exact (SemiprimeSourceWordMenuOrder.indexed_menu n F r Q arity).symm

/-- Index zero is ACTUALLY present in the acquired Boolean-ID bank. -/
theorem default_mem (r Q : ℕ) [NeZero r] : defaultID∈(acquire r Q).ids := by
  change []∈(ascending [] (SemiprimeSourceWordBankRows.rows r Q).value.length).value
  rw [rows_length]
  have hp : 0<r^Q := pow_pos (NeZero.pos r) Q
  cases h : r^Q with
  | zero => omega
  | succ k => simp only [ascending,fitBits_self,List.mem_cons,true_or]

/-- The literal default ID decodes to the original zero-first source word. -/
theorem decode_default (r Q : ℕ) [NeZero r] : decode r Q defaultID=(fun _ => 0) := by
  simp only [decode,defaultID,bitValue]
  rw [SemiprimeSourceWordMenuOrder.words_zero_first]
  rfl

/-- The acquired candidate menu is nonempty, including Q=0. -/
theorem ids_nonempty (r Q : ℕ) [NeZero r] : (acquire r Q).ids≠[] := by
  intro h
  have hm := default_mem r Q
  rw [h] at hm
  exact List.not_mem_nil hm

/-- Every valid physical candidate lookup has exactly Q coordinates. -/
theorem readRow_length (r Q : ℕ) [NeZero r] (id : List Bool) (hid : id∈(acquire r Q).ids) :
    (readRow (acquire r Q) id).value.length=Q := by
  have h := congrArg List.length (readRow_coordinates r Q id hid)
  simpa only [List.length_map,coordinates,List.length_ofFn] using h

/-- Concrete original-input coordinate semantics and validity, with no bank advice. -/
theorem acquired_representation (r Q : ℕ) [NeZero r] (id : List Bool)
    (hid : id∈(acquire r Q).ids) :
    (readRow (acquire r Q) id).value.map RationalWord.value=coordinates (decode r Q id) ∧
      ∀ x∈(readRow (acquire r Q) id).value,x.Valid := by
  exact ⟨readRow_coordinates r Q id hid,fun x hx => (readRow_good r Q id x hx).1⟩

end RiemannGaussian.SemiprimeSourceWordBankIndexed
