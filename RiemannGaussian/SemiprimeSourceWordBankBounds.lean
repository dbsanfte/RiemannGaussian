/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceWordBankSemantics

/-! # Physical original word-bank validity, widths and acquisition/lookup work -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceWordBankBounds
open SemiprimeSourceWordBank SemiprimeSourceWordBankRows SemiprimeRationalBits
open SemiprimeSourceScorePredicateBits SemiprimeSourceScorePredicateBitsBounds
open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitPrimeScan SemiprimeBitProductSort
open SemiprimeSourceOffsetInputsCore SemiprimeMaterializedSourceUniversal

/-- Every physically acquired original colour is valid with width derived from r. -/
theorem colours_good (r : ℕ) :
    ∀ x∈(colours r).value,x.Valid ∧ Width x (r+1) := by
  intro x hx
  simp only [colours,collect_value,SemiprimePaidFiniteEnumerationLists.fin_value,List.mem_map] at hx
  obtain ⟨i,_,rfl⟩ := hx
  exact ⟨(encodeNat_spec i.val).2.1,width_mono (encodeNat_spec i.val).2.2 (by omega)⟩

/-- Generic row construction preserves all actually copied payloads and their bounds. -/
theorem rowsWith_good (cs : List RationalWord) (W q : ℕ)
    (hc : ∀ x∈cs,x.Valid ∧ Width x W) :
    ∀ row∈(rowsWith cs q).value,∀ x∈row,x.Valid ∧ Width x W := by
  induction q with
  | zero => simp [rowsWith]
  | succ q ih =>
    intro row hr x hx
    simp only [rowsWith,collect_value,SemiprimePaidFiniteEnumerationLists.product_value,List.mem_map] at hr
    obtain ⟨p,hp,rfl⟩ := hr
    rw [prepend_value] at hx
    rcases List.mem_cons.mp hx with rfl|hx
    · exact hc p.1 (List.mem_product.mp hp).1
    · exact ih p.2 (List.mem_product.mp hp).2 x hx

/-- Original acquired bank payloads have a uniform original-dimension bound. -/
theorem acquire_good (r Q : ℕ) :
    ∀ row∈(acquire r Q).rows,∀ x∈row,x.Valid ∧ Width x (r+1) :=
  rowsWith_good (colours r).value (r+1) Q (colours_good r)

/-- Original row lengths are exact, not a supplied generic cache condition. -/
theorem acquire_row_length (r Q : ℕ) :
    ∀ row∈(acquire r Q).rows,row.length=Q := rowsWith_length _ _

/-- Even out-of-range lookup preserves validity and payload-width bounds. -/
theorem readRow_good (r Q : ℕ) (id : List Bool) :
    ∀ x∈(readRow (acquire r Q) id).value,x.Valid ∧ Width x (r+1) := by
  rw [readRow_value]
  cases h : (acquire r Q).rows[bitValue id]? with
  | none => simp
  | some row => exact acquire_good r Q row (List.mem_of_getElem? h)

/-- Physical lookup includes every visited-row copy, address test and decrement. -/
theorem readRows_clock (rows : List Row) (address : List Bool) (W Q B : ℕ)
    (hB : 1≤B) (ha : address.length≤B)
    (hr : ∀ row∈rows,row.length≤Q ∧ ∀ x∈row,Width x W) :
    (readRows rows address).work≤(rows.length+1)*(copyBudget W Q+15*B+30) := by
  induction rows generalizing address with
  | nil => simp only [readRows,List.length_nil];omega
  | cons row rows ih =>
    have hh := hr row List.mem_cons_self
    have hv := copyRow_work row W Q hh
    have ht := nonzeroBits_cost address
    have hd := subBits_cost address [true] false
    have hlen : (subBits address [true] false).result.bits.length≤B := by
      rw [(subBits_counts address [true] false).2.2.2.2]
      simp only [List.length_cons,List.length_nil]
      exact max_le ha hB
    have hc := ih (subBits address [true] false).result.bits hlen
      (fun row h => hr row (List.mem_cons_of_mem _ h))
    have hm : max address.length [true].length≤B := max_le ha (by simpa using hB)
    simp only [readRows,List.length_cons]
    split_ifs <;> dsimp only <;> nlinarith

/-- Explicit original bank lookup work, paid in original cardinality and bit lengths. -/
theorem readRow_clock (r Q : ℕ) (id : List Bool) (B : ℕ) (hB : 1≤B) (hi : id.length≤B) :
    (readRow (acquire r Q) id).work≤
      (r^Q+1)*(copyBudget (r+1) Q+15*B+30) := by
  have h := readRows_clock (acquire r Q).rows id (r+1) Q B hB hi (by
    intro row hr
    exact ⟨(acquire_row_length r Q row hr).le,fun x hx => (acquire_good r Q row hr x hx).2⟩)
  simpa only [acquire,readRow,SemiprimeSourceWordBankSemantics.rows_length] using h

end RiemannGaussian.SemiprimeSourceWordBankBounds
