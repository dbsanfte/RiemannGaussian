/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeWindowSqrt
import Mathlib.Data.Bool.Basic

/-!
# Boolean-list addition and multiplication with explicit primitive charges

Values use little-endian Boolean lists. The data path performs Boolean
gates, list inspection and bit-cell construction; natural evaluation is a
proof specification. The charged model counts those primitive categories
and branching, with operation reports serving as mathematical clocks.
This local backend does not yet implement quotient/remainder or prove the
whole factorizer's bit cost, and universal one-sixth coverage remains open.
-/

namespace RiemannGaussian.SemiprimeBitArithmetic

/-- The natural value of a Boolean digit, used only in specifications. -/
def bitNat (bit : Bool) : ℕ := if bit=true then 1 else 0

/-- Mathematical natural evaluation of little-endian digits. The Boolean
arithmetic routines do not call this specification. -/
def bitValue : List Bool → ℕ
  | [] => 0
  | bit::tail => bitNat bit+2*bitValue tail

/-- One fixed six-gate full adder: two XORs, two ANDs and two ORs. -/
def fullAdder (x y carry : Bool) : Bool×Bool :=
  (Bool.xor (Bool.xor x y) carry,
    Bool.or (Bool.and x y) (Bool.and carry (Bool.or x y)))

/-- The six-gate circuit preserves the exact digit plus carry sum. -/
theorem fullAdder_correct (x y carry : Bool) :
    bitNat (fullAdder x y carry).1+2*bitNat (fullAdder x y carry).2=
      bitNat x+bitNat y+bitNat carry := by
  cases x <;> cases y <;> cases carry <;> rfl

/-- Boolean output and clocks for explicitly charged bit primitives.
Clock arithmetic is instrumentation, not an integer operation in the data path. -/
structure BitReport where
  /-- Actual output bit cells, with possible high zero padding. -/
  bits : List Bool
  /-- Boolean gates in the fixed circuits used by this run. -/
  gates : ℕ
  /-- Input bit-cell reads, charged again when a list is revisited. -/
  reads : ℕ
  /-- Every new bit cell, including intermediate shifted or summed lists. -/
  writes : ℕ
  /-- List-constructor and Boolean branch tests. -/
  tests : ℕ

/-- Total clock in the charged Boolean-gate and persistent-bit-cell model. -/
def bitCost (report : BitReport) : ℕ := report.gates+report.reads+report.writes+report.tests

/-- Ripple addition evaluates the fixed circuit for every digit, padding
the shorter input with literal zero. Two list tests are charged per digit;
the terminal carry also pays its Boolean test and optional output cell. -/
def addBits : List Bool → List Bool → Bool → BitReport
  | [],[],carry => if carry=true then ⟨[true],0,0,1,3⟩ else ⟨[],0,0,0,3⟩
  | x::xs,[],carry =>
    let digit := fullAdder x false carry
    let tail := addBits xs [] digit.2
    ⟨digit.1::tail.bits,tail.gates+6,tail.reads+1,tail.writes+1,tail.tests+2⟩
  | [],y::ys,carry =>
    let digit := fullAdder false y carry
    let tail := addBits [] ys digit.2
    ⟨digit.1::tail.bits,tail.gates+6,tail.reads+1,tail.writes+1,tail.tests+2⟩
  | x::xs,y::ys,carry =>
    let digit := fullAdder x y carry
    let tail := addBits xs ys digit.2
    ⟨digit.1::tail.bits,tail.gates+6,tail.reads+2,tail.writes+1,tail.tests+2⟩
termination_by xs ys _ => xs.length+ys.length
decreasing_by all_goals simp_wf <;> omega

/-- Every actual output of the Boolean-list adder has the intended value,
including unequal input lengths, high zeros and terminal carry. -/
theorem addBits_correct (xs ys : List Bool) (carry : Bool) :
    bitValue (addBits xs ys carry).bits=bitValue xs+bitValue ys+bitNat carry := by
  induction xs generalizing ys carry with
  | nil =>
    induction ys generalizing carry with
    | nil => cases carry <;> simp [addBits,bitValue,bitNat]
    | cons y ys ih =>
      have hc := fullAdder_correct false y carry
      rw [addBits]
      dsimp only
      simp only [bitValue]
      rw [ih]
      simp only [bitValue,bitNat,Bool.false_eq_true,if_false] at hc ⊢
      omega
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hc := fullAdder_correct x false carry
      rw [addBits]
      dsimp only
      simp only [bitValue]
      rw [ih]
      simp only [bitValue,bitNat,Bool.false_eq_true,if_false] at hc ⊢
      omega
    | cons y ys =>
      have hc := fullAdder_correct x y carry
      rw [addBits]
      dsimp only
      simp only [bitValue]
      rw [ih]
      omega

/-- Ripple addition reads every input cell once and has one fixed circuit
per position. It constructs its actual complete output, including carry. -/
theorem addBits_counts (xs ys : List Bool) (carry : Bool) :
    (addBits xs ys carry).gates=6*max xs.length ys.length ∧
    (addBits xs ys carry).reads=xs.length+ys.length ∧
    (addBits xs ys carry).writes=(addBits xs ys carry).bits.length ∧
    (addBits xs ys carry).tests=2*max xs.length ys.length+3 ∧
    (addBits xs ys carry).bits.length≤max xs.length ys.length+1 := by
  induction xs generalizing ys carry with
  | nil =>
    induction ys generalizing carry with
    | nil => cases carry <;> simp [addBits]
    | cons y ys ih =>
      have hc := ih (fullAdder false y carry).2
      rw [addBits]
      dsimp only [List.length_cons,List.length_nil] at hc ⊢
      omega
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hc := ih [] (fullAdder x false carry).2
      rw [addBits]
      dsimp only [List.length_cons,List.length_nil] at hc ⊢
      omega
    | cons y ys =>
      have hc := ih ys (fullAdder x y carry).2
      rw [addBits]
      dsimp only [List.length_cons] at hc ⊢
      omega

/-- The actual charged addition clock is linear in the longer bit input. -/
theorem addBits_cost (xs ys : List Bool) (carry : Bool) :
    bitCost (addBits xs ys carry)≤11*max xs.length ys.length+4 := by
  obtain ⟨hg,hr,hw,ht,hlen⟩ := addBits_counts xs ys carry
  dsimp only [bitCost]
  omega

/-- Shift-and-add multiplication has a Boolean-list data path. Each shifted
intermediate allocates one cell; every reread of the right operand by an
adder is included. No natural multiplication computes the output. -/
def mulBits (xs ys : List Bool) : BitReport :=
  match xs with
  | [] => ⟨[],0,0,0,1⟩
  | x::tail =>
    let child := mulBits tail ys
    let shifted := false::child.bits
    if x=true then
      let sum := addBits ys shifted false
      ⟨sum.bits,child.gates+sum.gates,child.reads+sum.reads+1,
        child.writes+sum.writes+1,child.tests+sum.tests+2⟩
    else
      ⟨shifted,child.gates,child.reads+1,child.writes+1,child.tests+2⟩

/-- The actual Boolean output equals the literal product of both input
values, without a supplied integer product or arithmetic oracle. -/
theorem mulBits_correct (xs ys : List Bool) :
    bitValue (mulBits xs ys).bits=bitValue xs*bitValue ys := by
  induction xs with
  | nil => simp only [mulBits,bitValue,Nat.zero_mul]
  | cons x xs ih =>
    cases x <;> rw [mulBits] <;> dsimp only
    · simp only [Bool.false_eq_true,if_false,bitValue,bitNat,ih]
      ring
    · simp only [if_true,addBits_correct,bitValue,bitNat,ih,Bool.false_eq_true,if_false]
      ring

/-- Actual intermediate bit-list widths remain linear despite high-zero
padding; no exponentially long output representation is hidden in the clock. -/
theorem mulBits_length (xs ys : List Bool) :
    (mulBits xs ys).bits.length≤2*xs.length+ys.length := by
  induction xs with
  | nil => simp only [mulBits,List.length_nil,Nat.mul_zero,Nat.zero_add,Nat.zero_le]
  | cons x xs ih =>
    have ha := (addBits_counts ys (false::(mulBits xs ys).bits) false).2.2.2.2
    rw [mulBits]
    dsimp only [List.length_cons] at ha ⊢
    split <;> dsimp only [List.length_cons] <;> omega

/-- The charged scalar product has quadratic bit work. This includes every
adder gate, right-operand revisit and intermediate bit-cell allocation. -/
theorem mulBits_cost (xs ys : List Bool) :
    bitCost (mulBits xs ys)≤12*xs.length*(xs.length+ys.length+2)+1 := by
  induction xs with
  | nil => simp only [mulBits,bitCost,List.length_nil,Nat.mul_zero,Nat.zero_mul,
      Nat.zero_add,le_refl]
  | cons x xs ih =>
    have hl := mulBits_length xs ys
    have ha := addBits_cost ys (false::(mulBits xs ys).bits) false
    have hb : max ys.length (false::(mulBits xs ys).bits).length≤2*xs.length+ys.length+1 := by
      dsimp only [List.length_cons]
      omega
    rw [mulBits]
    dsimp only [List.length_cons]
    split
    · dsimp only [bitCost] at ih ha ⊢
      have hc := Nat.mul_le_mul_left 11 hb
      nlinarith
    · dsimp only [bitCost] at ih ⊢
      nlinarith

/-- Every represented value fits its actual physical bit width. -/
theorem bitValue_lt_width (bits : List Bool) : bitValue bits<2^bits.length := by
  induction bits with
  | nil => simp only [bitValue,List.length_nil,pow_zero,Nat.zero_lt_one]
  | cons bit bits ih =>
    cases bit <;> simp only [bitValue,bitNat,Bool.false_eq_true,if_false,if_true,
      List.length_cons,pow_succ] <;> omega

/-- Canonical value width never exceeds the physical list length; high
zero padding is still paid in every operation's actual clock. -/
theorem bitValue_bits (bits : List Bool) : Nat.clog 2 (bitValue bits+1)≤bits.length :=
  Nat.clog_le_of_le_pow (by have h:=bitValue_lt_width bits; omega)

/-- Bounded-width addition has a linear charged primitive clock and at
most one carry bit beyond its input width. -/
theorem bounded_addBits {L : ℕ} {xs ys : List Bool} (hx : xs.length≤L) (hy : ys.length≤L)
    (carry : Bool) : bitCost (addBits xs ys carry)≤11*L+4 ∧
      (addBits xs ys carry).bits.length≤L+1 := by
  have hc := addBits_cost xs ys carry
  have hl := (addBits_counts xs ys carry).2.2.2.2
  omega

/-- Bounded-width products have a quadratic charged primitive clock and
linear output width, without treating a scalar multiplication as one bit op. -/
theorem bounded_mulBits {L : ℕ} {xs ys : List Bool} (hx : xs.length≤L) (hy : ys.length≤L) :
    bitCost (mulBits xs ys)≤24*(L+1)^2+1 ∧ (mulBits xs ys).bits.length≤3*L := by
  have hc := mulBits_cost xs ys
  have hl := mulBits_length xs ys
  have hm := Nat.mul_le_mul hx (by omega : xs.length+ys.length+2≤2*(L+1))
  constructor
  · nlinarith
  · omega

/-- Actual product reports and the composed clock for a list of operands. -/
structure ProductBatch where
  /-- Each scalar computation is retained once, with its actual output. -/
  products : List BitReport
  /-- All scalar clocks plus one list test and report cell per product. -/
  clock : ℕ

/-- Compute every requested scalar product, charging traversal and retained
report cells as well as the complete Boolean multiplication clocks. -/
def multiplyBatch : List (List Bool×List Bool) → ProductBatch
  | [] => ⟨[],1⟩
  | pair::tail =>
    let product := mulBits pair.1 pair.2
    let rest := multiplyBatch tail
    ⟨product::rest.products,bitCost product+rest.clock+2⟩

/-- The computed batch has exactly one actual report for every input pair. -/
theorem multiplyBatch_length (pairs : List (List Bool×List Bool)) :
    (multiplyBatch pairs).products.length=pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair tail ih => simp only [multiplyBatch,List.length_cons,ih]

/-- Every actual product value agrees with its input pair in the original
order; this is computation, rather than supplied or assumed product advice. -/
theorem multiplyBatch_correct (pairs : List (List Bool×List Bool)) :
    (multiplyBatch pairs).products.map (fun report => bitValue report.bits)=
      pairs.map (fun pair => bitValue pair.1*bitValue pair.2) := by
  induction pairs with
  | nil => rfl
  | cons pair tail ih => simp only [multiplyBatch,List.map_cons,mulBits_correct,ih]

/-- The composed charged clock remains linear in the number of actual
products and quadratic in their physical input width. No supplied clock
or assumed fast scalar arithmetic occurs in this batch. -/
theorem multiplyBatch_cost {L : ℕ} (pairs : List (List Bool×List Bool))
    (hwidth : ∀ pair∈pairs,pair.1.length≤L ∧ pair.2.length≤L) :
    (multiplyBatch pairs).clock≤pairs.length*(24*(L+1)^2+3)+1 := by
  induction pairs with
  | nil => simp only [multiplyBatch,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons pair tail ih =>
    have hp := hwidth pair (List.mem_cons_self)
    have hc := (bounded_mulBits hp.1 hp.2).1
    have ht := ih (fun p h => hwidth p (List.mem_cons_of_mem _ h))
    simp only [multiplyBatch,List.length_cons]
    nlinarith

/-- Retained output bit cells have a linear total width allowance even
though the multiplication clocks include every discarded intermediate. -/
theorem multiplyBatch_output_width {L : ℕ} (pairs : List (List Bool×List Bool))
    (hwidth : ∀ pair∈pairs,pair.1.length≤L ∧ pair.2.length≤L) :
    ((multiplyBatch pairs).products.map (fun report => report.bits.length)).sum≤3*L*pairs.length := by
  induction pairs with
  | nil => simp only [multiplyBatch,List.map_nil,List.sum_nil,List.length_nil,Nat.mul_zero,le_refl]
  | cons pair tail ih =>
    have hp := hwidth pair (List.mem_cons_self)
    have hc := (bounded_mulBits hp.1 hp.2).2
    have ht := ih (fun p h => hwidth p (List.mem_cons_of_mem _ h))
    simp only [multiplyBatch,List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

end RiemannGaussian.SemiprimeBitArithmetic
