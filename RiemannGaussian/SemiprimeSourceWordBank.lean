/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceWordBankRows

/-! # Original-input physical word bank and Boolean-address lookup -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceWordBank
open SemiprimeSourceScorePredicateBits SemiprimeRationalBits
open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitPrimeScan
open SemiprimeBitProductSort SemiprimeSourceOffsetInputsCore SemiprimeBitIndexTraversal

/-- Concrete original coordinate bank with acquired Boolean candidate IDs. -/
structure Bank where
  /-- Complete ordered physical coordinate rows. -/
  rows : List Row
  /-- Acquired ascending physical index words. -/
  ids : List (List Bool)
  /-- Original row acquisition and all index/cell/control work. -/
  clock : ℕ

/-- Actual ascending Boolean IDs; increments and current-ID copies are paid. -/
def ascending (current : List Bool) : ℕ → SemiprimeMaterializedWords.Run (List (List Bool))
  | 0 => ⟨[],1⟩
  | n+1 =>
    let copied := fitBits current current
    let next := addBits current [true] false
    let rest := ascending next.bits n
    ⟨copied.bits::rest.value,bitCost copied+bitCost next+rest.work+5⟩

/-- Index zero is a literal empty little-endian magnitude. -/
def defaultID : List Bool := []

/-- Construct rows and indices solely from original r,Q; no word-bank argument. -/
def acquire (r Q : ℕ) : Bank :=
  let table := SemiprimeSourceWordBankRows.rows r Q
  let indices := ascending [] table.value.length
  ⟨table.value,indices.value,table.work+indices.work+table.value.length+4⟩

/-- Physical row lookup copies every visited row, tests/decrements the address,
and returns the empty physical row only on genuine out-of-range lookup. -/
def readRows : List Row → List Bool → SemiprimeMaterializedWords.Run Row
  | [],_ => ⟨[],4⟩
  | row::rows,address =>
    let visit := copyRow row
    let test := nonzeroBits address
    if test.nonzero then
      let decrement := subBits address [true] false
      let rest := readRows rows decrement.result.bits
      ⟨rest.value,visit.work+test.clock+bitCost decrement.result+rest.work+6⟩
    else ⟨visit.value,visit.work+test.clock+4⟩

/-- Concrete bank lookup used by physical ID environments. -/
def readRow (bank : Bank) (id : List Bool) : SemiprimeMaterializedWords.Run Row :=
  readRows bank.rows id

/-- Exact physical address semantics, with no native integer lookup in runtime. -/
theorem readRows_value (rows : List Row) (address : List Bool) :
    (readRows rows address).value=(rows[bitValue address]?).getD [] := by
  induction rows generalizing address with
  | nil => simp [readRows]
  | cons row rows ih =>
    by_cases h : (nonzeroBits address).nonzero=true
    · have hp := (nonzeroBits_correct address).mp h
      have hd := (decrementBits_value hp).2
      have he : bitValue address=(bitValue address-1)+1 := by omega
      simp only [readRows,h,ite_true,ih,hd]
      conv_rhs => rw [he]
      rw [List.getElem?_cons_succ]
    · have hz := (nonzeroBits_false_iff address).mp (Bool.eq_false_of_not_eq_true h)
      simp only [readRows,Bool.eq_false_of_not_eq_true h,Bool.false_eq_true,ite_false,
        copyRow_value,hz,List.getElem?_cons_zero,Option.getD_some]

/-- The public lookup has exactly the acquired row-index interpretation. -/
theorem readRow_value (bank : Bank) (id : List Bool) :
    (readRow bank id).value=(bank.rows[bitValue id]?).getD [] := readRows_value _ _

/-- Generated ID values are the literal ascending range, with no integer encoder oracle. -/
theorem ascending_values (current : List Bool) (n : ℕ) :
    (ascending current n).value.map bitValue=List.range' (bitValue current) n := by
  induction n generalizing current with
  | zero => rfl
  | succ n ih =>
    simp only [ascending,List.map_cons,fitBits_self,addBits_correct,bitNat,Bool.false_eq_true,
      ite_false,Nat.add_zero,bitValue,List.range'_succ,ih]
    rfl

/-- Exact number of physical IDs. -/
theorem ascending_length (current : List Bool) (n : ℕ) : (ascending current n).value.length=n := by
  have h := congrArg List.length (ascending_values current n)
  simpa only [List.length_map,List.length_range'] using h

/-- IDs and acquired rows have the same actual length. -/
theorem acquire_ids_length (r Q : ℕ) : (acquire r Q).ids.length=(acquire r Q).rows.length := by
  exact ascending_length [] _

end RiemannGaussian.SemiprimeSourceWordBank
