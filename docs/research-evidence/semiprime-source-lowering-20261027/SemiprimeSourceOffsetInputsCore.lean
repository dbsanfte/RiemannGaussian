/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceOffsetProgramBudget
import RiemannGaussian.SemiprimeJetBits

/-! # Acquired original natural dimensions for offset initialization
Binary values are produced by actual Boolean additions. The universal-bank
cardinality is first constructed by paid unary cell replication, not a free
semantic exponent. Natural recursion/control remains an explicit interface.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeSourceOffsetInputsCore
open SemiprimeBitArithmetic SemiprimeBitPrimeScan SemiprimeRationalBits

/-- Actual emitted natural bits and their complete addition/cell ledger. -/
structure NatRun where
  /-- Little-endian magnitude. -/
  bits : List Bool
  /-- Physical Boolean additions and bit-list construction work. -/
  clock : ℕ

/-- Magnitude-linear acquisition from the ORIGINAL natural loop parameter. -/
def natBits : ℕ → NatRun
  | 0 => ⟨[],1⟩
  | n+1 =>
    let old := natBits n
    let out := addBits old.bits [true] false
    ⟨out.bits,old.clock+bitCost out+out.bits.length+3⟩

/-- No value oracle occurs in the emitted natural magnitude. -/
theorem natBits_value (n : ℕ) : bitValue (natBits n).bits=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [natBits,incrementBits_value,ih]

/-- Linear physical storage, including the adder's high zero padding. -/
theorem natBits_length (n : ℕ) : (natBits n).bits.length≤ n+1 := by
  induction n with
  | zero => simp [natBits]
  | succ n ih =>
    have hc := (addBits_counts (natBits n).bits [true] false).2.2.2.2
    simp only [List.length_cons,List.length_nil] at hc
    simp only [natBits]
    exact hc.trans (Nat.add_le_add_right (max_le ih (by omega)) 1)

/-- All Boolean addition, output allocation and retained reports are polynomial. -/
theorem natBits_clock (n : ℕ) : (natBits n).clock≤20*(n+1)^2 := by
  induction n with
  | zero => simp [natBits]
  | succ n ih =>
    have hw := natBits_length n
    have hc := addBits_cost (natBits n).bits [true] false
    have hl := (addBits_counts (natBits n).bits [true] false).2.2.2.2
    have hm : max (natBits n).bits.length [true].length≤ n+1 := max_le hw (by simp)
    have ho := natBits_length (n+1)
    simp only [natBits] at ho ⊢
    nlinarith

/-- Literal rational word for an original natural dimension, denominator one. -/
def encodeNat (n : ℕ) : RationalReport :=
  let out := natBits n
  ⟨⟨⟨false,out.bits⟩,[true]⟩,out.clock+4⟩

/-- Exact, valid, bounded original natural word. -/
theorem encodeNat_spec (n : ℕ) :
    (encodeNat n).word.value=(n:ℚ) ∧ (encodeNat n).word.Valid ∧ Width (encodeNat n).word (n+1) := by
  refine ⟨?_,by change 0<(1:ℕ);decide,?_,by change 1≤ n+1;omega⟩
  · simp [encodeNat,RationalWord.value,SemiprimeBitIndexClipping.SignedWord.value,natBits_value,bitValue,bitNat]
  · exact natBits_length n

/-- Exact actual encoding report bound, with no binary-encoding advice. -/
theorem encodeNat_clock (n : ℕ) : (encodeNat n).clock≤20*(n+1)^2+4 := by
  exact Nat.add_le_add_right (natBits_clock n) 4

/-- An explicitly materialized unary cardinality with paid traversal/copy work. -/
structure CellsRun where
  /-- Actual cardinality cells. -/
  cells : List Bool
  /-- All append/copy/length and finite recursion work. -/
  clock : ℕ

/-- Copy an actual finite block a literal number of times, paying each append. -/
def repeatCells (cells : List Bool) : ℕ → CellsRun
  | 0 => ⟨[],1⟩
  | n+1 => let old := repeatCells cells n
           ⟨cells++old.cells,old.clock+3*cells.length+3⟩

/-- The cardinality is acquired by physical cell replication. -/
theorem repeatCells_length (cells : List Bool) (n : ℕ) : (repeatCells cells n).cells.length=n*cells.length := by
  induction n with
  | zero => simp [repeatCells]
  | succ n ih => simp only [repeatCells,List.length_append,ih];ring

/-- Every copied block and append traversal contributes to the actual report. -/
theorem repeatCells_clock (cells : List Bool) (n : ℕ) :
    (repeatCells cells n).clock=1+n*(3*cells.length+3) := by
  induction n with
  | zero => simp [repeatCells]
  | succ n ih => simp only [repeatCells,ih];ring

/-- Acquire the universal-bank cardinality by original r,2Q loops, without Nat.pow. -/
def unaryPower (r : ℕ) : ℕ → CellsRun
  | 0 => ⟨[false],2⟩
  | k+1 =>
    let old := unaryPower r k
    let out := repeatCells old.cells r
    ⟨out.cells,old.clock+out.clock+old.cells.length+4⟩

/-- Semantic powers appear only in this specification of acquired cells. -/
theorem unaryPower_length (r k : ℕ) : (unaryPower r k).cells.length=r^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [unaryPower,repeatCells_length,ih,pow_succ];ring

/-- Closed original-resource work for every actual unary-power prefix. -/
theorem unaryPower_clock (r Q : ℕ) (hr : 0< r) :
    ∀ k≤2*Q,(unaryPower r k).clock≤2+k*(r*(3*r^(2*Q)+3)+r^(2*Q)+5) := by
  intro k hk
  induction k with
  | zero => simp [unaryPower]
  | succ k ih =>
    have hh := ih (by omega)
    have hl : (unaryPower r k).cells.length≤ r^(2*Q) := by
      rw [unaryPower_length]
      exact Nat.pow_le_pow_right hr (by omega)
    simp only [unaryPower,repeatCells_clock]
    nlinarith

end RiemannGaussian.SemiprimeSourceOffsetInputsCore
