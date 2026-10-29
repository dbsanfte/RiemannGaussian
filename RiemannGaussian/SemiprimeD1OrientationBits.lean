/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1CounterMaximum
import RiemannGaussian.SemiprimeSourceCompactWordIds
import RiemannGaussian.SemiprimeSourceHistogramKeyBits

/-! # Executed D1 orientation packets from physical colour rows
Only Boolean colour fields and padding-index bits enter execution. One physical
unsigned comparison supplies order and both borrow flags; equal coordinates
consume a padding bit, unequal coordinates supply the ordered-pair orientation.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace RiemannGaussian.SemiprimeD1OrientationBits
open SemiprimeBitArithmetic SemiprimeBitIndexClipping SemiprimeBitIndexRoots
open SemiprimeSourceCompactBits (Compact)
open SemiprimeSourceHistogramKeyBits (frame)

/-- Equality from the two already acquired physical borrow flags. -/
def equality (order : SignedOrderReport) : Bool := !order.forward.borrow && !order.backward.borrow

/-- Physical borrow equality is exactly unsigned value equality, including zero. -/
theorem equality_exact (left right : List Bool) :
    equality (leSignedBits ⟨false,left⟩ ⟨false,right⟩)=true ↔ bitValue left=bitValue right := by
  simp only [equality,leSignedBits,Bool.and_eq_true,Bool.not_eq,Bool.not_eq_true,
    subBits_borrow_false]
  omega

/-- One copied unordered colour field, slot bit, remaining padding and report. -/
structure Coordinate where
  /-- Copied smaller unsigned colour payload. -/
  low : List Bool
  /-- Copied larger unsigned colour payload. -/
  high : List Bool
  /-- Acquired unambiguous pair field. -/
  field : List Bool
  /-- Actual orientation or consumed padding bit. -/
  slot : Bool
  /-- Remaining original padding-index tail, shared immutably. -/
  next : List Bool
  /-- Already acquired physical equality flag. -/
  equal : Bool
  /-- Already acquired unsigned order flag. -/
  ordered : Bool
  /-- Both borrows, zero scans, copies, framing and finite control. -/
  clock : ℕ

/-- Acquire one coordinate without a native colour comparison or equality answer. -/
def coordinate (left right j : List Bool) : Coordinate :=
  let order := leSignedBits ⟨false,left⟩ ⟨false,right⟩
  let eq := equality order
  let low := SemiprimeSourceCompactBits.copy (if order.le then left else right)
  let high := SemiprimeSourceCompactBits.copy (if order.le then right else left)
  let field := SemiprimeSourceHistogramKeyBits.pair low.bits high.bits
  let bit := if eq then j.headD false else !order.le
  let next := if eq then j.tail else j
  ⟨low.bits,high.bits,field.bits,bit,next,eq,order.le,
    order.clock+low.clock+high.clock+field.clock+20⟩

/-- No semantic pair encoding supplies the actual returned coordinate bytes. -/
theorem coordinate_field (left right j : List Bool) :
    (coordinate left right j).field=frame (coordinate left right j).low (coordinate left right j).high :=
  SemiprimeSourceHistogramKeyBits.pair_bits _ _

/-- Exact copied unordered fields, from the single actual acquired comparison. -/
theorem coordinate_fields (left right j : List Bool) :
    (coordinate left right j).low=(if (leSignedBits ⟨false,left⟩ ⟨false,right⟩).le then left else right) ∧
    (coordinate left right j).high=(if (leSignedBits ⟨false,left⟩ ⟨false,right⟩).le then right else left) := by
  simp [coordinate,SemiprimeSourceCompactBits.copy_bits]

/-- Original input bit operations are precisely the consumed equal-coordinate bit. -/
theorem coordinate_next (left right j : List Bool) :
    (coordinate left right j).next=if (coordinate left right j).equal then j.tail else j := rfl

/-- No colour values are decoded to select the physical slot bit. -/
theorem coordinate_slot (left right j : List Bool) :
    (coordinate left right j).slot=if (coordinate left right j).equal then j.headD false
      else !(coordinate left right j).ordered := rfl

/-- Equality and order flags have exact original unsigned meanings. -/
theorem coordinate_flags (left right j : List Bool) :
    ((coordinate left right j).equal=true ↔ bitValue left=bitValue right) ∧
    ((coordinate left right j).ordered=true ↔ bitValue left≤bitValue right) :=
  ⟨equality_exact left right,SemiprimeD1CounterMaximum.unsigned_order left right⟩

/-- Packet key, coordinate-order slot bits, remaining high padding and report. -/
structure Packet where
  /-- Nested framed unordered coordinate fields with high padding as final tail. -/
  key : List Bool
  /-- Exactly one low-to-high slot bit per acquired coordinate. -/
  slots : List Bool
  /-- Actual copied remaining high padding-index bits. -/
  high : List Bool
  /-- Whether the two actual input rows had identical lengths. -/
  valid : Bool
  /-- Every coordinate, tail, field frame, copy and loop stage. -/
  clock : ℕ

/-- Actual physical row scan. Equal coordinates consume low padding bits; missing
high padding bits are literal false, so compact zero never needs extra storage. -/
def acquire : List (List Bool) → List (List Bool) → List Bool → Packet
  | [],[],j =>
    let tail := SemiprimeSourceCompactBits.copy j
    ⟨tail.bits,[],tail.bits,true,tail.clock+3⟩
  | left::ls,right::rs,j =>
    let here := coordinate left right j
    let tail := acquire ls rs here.next
    let key := SemiprimeSourceHistogramKeyBits.pair here.field tail.key
    ⟨key.bits,here.slot::tail.slots,tail.high,tail.valid,here.clock+tail.clock+key.clock+8⟩
  | _,_,j =>
    let tail := SemiprimeSourceCompactBits.copy j
    ⟨tail.bits,[],tail.bits,false,tail.clock+3⟩

/-- The actual validity flag detects only row-length mismatch. -/
theorem acquire_valid (left right : List (List Bool)) (j : List Bool) :
    (acquire left right j).valid=true ↔ left.length=right.length := by
  induction left generalizing right j with
  | nil => cases right <;> simp [acquire]
  | cons x xs ih => cases right <;> simp [acquire,ih]

/-- The acquired slot has the original coordinate count on every valid row pair. -/
theorem acquire_slots_length (left right : List (List Bool)) (j : List Bool)
    (h : left.length=right.length) : (acquire left right j).slots.length=left.length := by
  induction left generalizing right j with
  | nil => cases right <;> simp_all [acquire]
  | cons x xs ih =>
    cases right with
    | nil => simp at h
    | cons y ys =>
      simpa only [acquire,List.length_cons] using
        congrArg Nat.succ (ih ys (coordinate x y j).next (by simpa using h))

/-- Remaining high bits are an actual original index suffix, never a new index answer. -/
theorem acquire_high_length (left right : List (List Bool)) (j : List Bool) :
    (acquire left right j).high.length≤j.length := by
  induction left generalizing right j with
  | nil => cases right <;> simp [acquire,SemiprimeSourceCompactBits.copy_bits]
  | cons x xs ih =>
    cases right with
    | nil => simp [acquire,SemiprimeSourceCompactBits.copy_bits]
    | cons y ys =>
      have ht := ih ys (coordinate x y j).next
      change (acquire xs ys _).high.length≤_
      apply ht.trans
      rw [coordinate_next]
      split_ifs
      · simp only [List.length_tail];omega
      · exact le_rfl

end RiemannGaussian.SemiprimeD1OrientationBits
