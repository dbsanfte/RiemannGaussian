/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryIntegerBits

/-! # Physical child-coordinate cache access
The input is literal nested Boolean data, not a semantic child getter. Every
visited cache payload is copied and both row/coordinate addresses are operated
on as actual Boolean words. Native node/index digits are separately reported.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1RecoveryChildBits
open SemiprimeBitArithmetic SemiprimeBitDivision
open SemiprimeBitPrimeScan SemiprimeBitIndexTraversal
open SemiprimeD1RecoveryIntegerBits

/-- An actual copied row of child coefficient words. -/
structure RowReport where
  /-- Actual physical word payloads. -/
  words : List (List Bool)
  /-- Every copied/read/allocated payload cell. -/
  clock : ℕ

/-- Deep copy of actual child coordinate words. -/
def copyRow : List (List Bool) → RowReport
  | [] => ⟨[],1⟩
  | x::xs =>
    let copied:=fitBits x x
    let tail:=copyRow xs
    ⟨copied.bits::tail.words,bitCost copied+tail.clock+3⟩

/-- The actual same-width bit copy preserves its literal payload. -/
theorem copy_bits (x : List Bool) : (fitBits x x).bits=x := by
  induction x with
  | nil => rfl
  | cons b xs ih => simpa only [fitBits] using congrArg (b::·) ih

/-- Deep copying preserves every actual child bit. -/
theorem copyRow_words (xs : List (List Bool)) : (copyRow xs).words=xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hc:=copy_bits x
    simp only [copyRow,ih,hc]

/-- Actual child-row selection scans a physical decrementing address and copies
all visited rows; out-of-range selection is the literal empty row. -/
def readRow : List (List (List Bool)) → List Bool → RowReport
  | [],_ => ⟨[],4⟩
  | x::xs,address =>
    let visit:=copyRow x
    let test:=nonzeroBits address
    if test.nonzero then
      let decrement:=subBits address [true] false
      let rest:=readRow xs decrement.result.bits
      ⟨rest.words,visit.clock+test.clock+bitCost decrement.result+rest.clock+6⟩
    else ⟨visit.words,visit.clock+test.clock+4⟩

/-- Exact literal child-row lookup; only the proof decodes the address. -/
theorem readRow_words (xs : List (List (List Bool))) (address : List Bool) :
    (readRow xs address).words=(xs[bitValue address]?).getD [] := by
  induction xs generalizing address with
  | nil => simp [readRow]
  | cons x xs ih =>
    by_cases h:(nonzeroBits address).nonzero=true
    · have hp:=(nonzeroBits_correct address).mp h
      have hd:=(decrementBits_value hp).2
      have he:bitValue address=(bitValue address-1)+1 := by omega
      simp only [readRow,h,ite_true,ih,hd]
      conv_rhs => rw [he]
      rw [List.getElem?_cons_succ]
    · have hz:=(nonzeroBits_false_iff address).mp (Bool.eq_false_of_not_eq_true h)
      simp only [readRow,Bool.eq_false_of_not_eq_true h,Bool.false_eq_true,ite_false,
        copyRow_words,hz,List.getElem?_cons_zero,Option.getD_some]

/-- Literal coefficient-word lookup with physical address operations and copies. -/
def readWord : List (List Bool) → List Bool → UnsignedReport
  | [],_ => ⟨[],4⟩
  | x::xs,address =>
    let visit:=fitBits x x
    let test:=nonzeroBits address
    if test.nonzero then
      let decrement:=subBits address [true] false
      let rest:=readWord xs decrement.result.bits
      ⟨rest.bits,bitCost visit+test.clock+bitCost decrement.result+rest.clock+6⟩
    else ⟨visit.bits,bitCost visit+test.clock+4⟩

/-- Exact physical coordinate lookup, including the out-of-range zero default. -/
theorem readWord_bits (xs : List (List Bool)) (address : List Bool) :
    (readWord xs address).bits=(xs[bitValue address]?).getD [] := by
  induction xs generalizing address with
  | nil => simp [readWord]
  | cons x xs ih =>
    have hc:=copy_bits x
    have hcopy:(fitBits x x).bits=x := by simpa using hc
    by_cases h:(nonzeroBits address).nonzero=true
    · have hp:=(nonzeroBits_correct address).mp h
      have hd:=(decrementBits_value hp).2
      have he:bitValue address=(bitValue address-1)+1 := by omega
      simp only [readWord,h,ite_true,ih,hd]
      conv_rhs => rw [he]
      rw [List.getElem?_cons_succ]
    · have hz:=(nonzeroBits_false_iff address).mp (Bool.eq_false_of_not_eq_true h)
      simp only [readWord,Bool.eq_false_of_not_eq_true h,Bool.false_eq_true,ite_false,
        hcopy,hz,List.getElem?_cons_zero,Option.getD_some]

/-- Two literal physical address words select one actual child coefficient. -/
def read (children : List (List (List Bool))) (node coordinate : List Bool) : UnsignedReport :=
  let row:=readRow children node
  let out:=readWord row.words coordinate
  ⟨out.bits,row.clock+out.clock+4⟩

/-- The actual nested physical lookup has the expected literal cache semantics. -/
theorem read_bits (children : List (List (List Bool))) (node coordinate : List Bool) :
    (read children node coordinate).bits=
      (((children[bitValue node]?).getD [])[bitValue coordinate]?).getD [] := by
  simp only [read,readWord_bits,readRow_words]

/-- Every copied child row has a linear actual payload report. -/
theorem copyRow_clock (xs : List (List Bool)) (P : ℕ)
    (hx : ∀ x ∈ xs, x.length ≤ P) :
    (copyRow xs).clock ≤ xs.length*(4*P+4)+1 := by
  induction xs with
  | nil => simp [copyRow]
  | cons x xs ih =>
    have hc:=fitBits_cost x x
    have hh:=hx x (by simp)
    have ht:=ih (fun y hy => hx y (by simp [hy]))
    simp only [copyRow,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Row selection preserves actual cache shape, including its empty default. -/
theorem readRow_shape (xs : List (List (List Bool))) (address : List Bool) (A P : ℕ)
    (hx : ∀ row ∈ xs, row.length ≤ A ∧ ∀ x ∈ row, x.length ≤ P) :
    (readRow xs address).words.length ≤ A ∧
      ∀ x ∈ (readRow xs address).words, x.length ≤ P := by
  rw [readRow_words]
  cases he:xs[bitValue address]? with
  | none => simp
  | some row => exact hx row (List.mem_of_getElem? he)

/-- Every visited physical row, address test and decrement is charged. -/
theorem readRow_clock (xs : List (List (List Bool))) (address : List Bool) (A P B : ℕ)
    (hB : 1 ≤ B) (ha : address.length ≤ B)
    (hx : ∀ row ∈ xs, row.length ≤ A ∧ ∀ x ∈ row, x.length ≤ P) :
    (readRow xs address).clock ≤ (xs.length+1)*(A*(4*P+4)+15*B+40) := by
  induction xs generalizing address with
  | nil => simp only [readRow,List.length_nil]; omega
  | cons row xs ih =>
    have hr:=hx row (by simp)
    have hv:=copyRow_clock row P hr.2
    have ht:=nonzeroBits_cost address
    have hd:=subBits_cost address [true] false
    have hlen : (subBits address [true] false).result.bits.length ≤ B := by
      rw [(subBits_counts address [true] false).2.2.2.2]
      simp only [List.length_cons,List.length_nil]
      exact max_le ha hB
    have hc:=ih (subBits address [true] false).result.bits hlen
      (fun y hy => hx y (by simp [hy]))
    have hmax : max address.length [true].length ≤ B := max_le ha (by simpa using hB)
    have hv' : (copyRow row).clock ≤ A*(4*P+4)+1 :=
      hv.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hr.1) 1)
    simp only [readRow,List.length_cons]
    split_ifs <;> dsimp only <;> nlinarith

/-- Every visited child coefficient and physical address transition is paid. -/
theorem readWord_clock (xs : List (List Bool)) (address : List Bool) (P B : ℕ)
    (hB : 1 ≤ B) (ha : address.length ≤ B)
    (hx : ∀ x ∈ xs, x.length ≤ P) :
    (readWord xs address).clock ≤ (xs.length+1)*(4*P+15*B+30) := by
  induction xs generalizing address with
  | nil => simp only [readWord,List.length_nil]; omega
  | cons x xs ih =>
    have hv:=fitBits_cost x x
    have hh:=hx x (by simp)
    have ht:=nonzeroBits_cost address
    have hd:=subBits_cost address [true] false
    have hlen : (subBits address [true] false).result.bits.length ≤ B := by
      rw [(subBits_counts address [true] false).2.2.2.2]
      simp only [List.length_cons,List.length_nil]
      exact max_le ha hB
    have hc:=ih (subBits address [true] false).result.bits hlen
      (fun y hy => hx y (by simp [hy]))
    have hmax : max address.length [true].length ≤ B := max_le ha (by simpa using hB)
    simp only [readWord,List.length_cons]
    split_ifs <;> dsimp only <;> nlinarith

/-- Full literal two-address child-cache access has a closed polynomial report. -/
theorem read_clock (children : List (List (List Bool))) (node coordinate : List Bool)
    (A P B : ℕ) (hB : 1 ≤ B) (hn : node.length ≤ B) (hc : coordinate.length ≤ B)
    (hx : ∀ row ∈ children, row.length ≤ A ∧ ∀ x ∈ row, x.length ≤ P) :
    (read children node coordinate).clock ≤
      (children.length+1)*(A*(4*P+4)+15*B+40)+(A+1)*(4*P+15*B+30)+4 := by
  have hr:=readRow_clock children node A P B hB hn hx
  have hs:=readRow_shape children node A P hx
  have hw:=readWord_clock (readRow children node).words coordinate P B hB hc hs.2
  have hm:=Nat.mul_le_mul_right (4*P+15*B+30) (Nat.add_le_add_right hs.1 1)
  simp only [read]
  omega

end RiemannGaussian.SemiprimeD1RecoveryChildBits
