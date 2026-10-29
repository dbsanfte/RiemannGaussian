/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitArithmetic

/-! # Executed compact little-endian counters
High-zero removal and arithmetic execute Boolean-list operations. Native recursive
control/report fields and immutable tail references remain machine-join interfaces.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceCompactBits
open SemiprimeBitArithmetic

/-- Actual acquired bits and retained bit/cell/control work. -/
structure Report where
  /-- Physical little-endian magnitude. -/
  bits : List Bool
  /-- Executed primitive and list-cell work. -/
  clock : ℕ

/-- No high zero remains; the empty list is the sole compact zero. -/
def Compact : List Bool → Prop
  | [] => True
  | b::bs => Compact bs ∧ (bs=[] → b=true)

/-- Actual right-recursive high-zero deletion. Each input cell and returned-tail
constructor is inspected; existing immutable suffix references are reused. -/
def trim : List Bool → Report
  | [] => ⟨[],1⟩
  | b::bs =>
    let tail := trim bs
    let bits := match tail.bits with
      | [] => if b then [true] else []
      | _::_ => b::tail.bits
    ⟨bits,tail.clock+6⟩

/-- Trimming never changes the represented natural. -/
theorem trim_value (bits : List Bool) : bitValue (trim bits).bits=bitValue bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    cases h : (trim bs).bits with
    | nil =>
      have hz : bitValue bs=0 := by simpa only [h,bitValue] using ih.symm
      cases b <;> simp [trim,h,bitValue,bitNat,hz]
    | cons c cs =>
      simp only [trim,h,bitValue] at ih ⊢
      omega

/-- Every output, including zero, is canonical. -/
theorem trim_compact (bits : List Bool) : Compact (trim bits).bits := by
  induction bits with
  | nil => trivial
  | cons b bs ih =>
    cases h : (trim bs).bits with
    | nil => cases b <;> simp [trim,h,Compact]
    | cons c cs =>
      simp only [trim,h]
      exact ⟨by simpa only [h] using ih,by simp⟩

/-- Every actual output list has at most the input number of cells. -/
theorem trim_length (bits : List Bool) : (trim bits).bits.length ≤ bits.length := by
  induction bits with
  | nil => exact le_rfl
  | cons b bs ih =>
    cases h : (trim bs).bits with
    | nil => cases b <;> simp [trim,h]
    | cons c cs => simp only [trim,h,List.length_cons] at ih ⊢;omega

/-- Complete retained scan/constructor clock is linear in actual input cells. -/
theorem trim_clock (bits : List Bool) : (trim bits).clock=6*bits.length+1 := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp only [trim,List.length_cons,ih];omega

/-- Nonempty compact words represent a positive natural. -/
theorem compact_pos (bits : List Bool) (hc : Compact bits) (hne : bits≠[]) : 0<bitValue bits := by
  induction bits with
  | nil => exact False.elim (hne rfl)
  | cons b bs ih =>
    cases bs with
    | nil =>
      have hb := hc.2 rfl
      simp only [hb,bitValue,bitNat,ite_true]
      omega
    | cons c cs =>
      have h := ih hc.1 (by simp)
      simp only [bitValue] at h ⊢
      omega

/-- Compact physical width is controlled by the numerical bound, not update count. -/
theorem compact_length_of_lt (bits : List Bool) (hc : Compact bits) (B : ℕ)
    (hv : bitValue bits<2^B) : bits.length ≤ B := by
  induction bits generalizing B with
  | nil => simp
  | cons b bs ih =>
    cases B with
    | zero =>
      have hp := compact_pos (b::bs) hc (by simp)
      simp only [pow_zero] at hv
      omega
    | succ B =>
      have ht : bitValue bs<2^B := by
        simp only [bitValue,pow_succ] at hv
        omega
      have h := ih hc.1 B ht
      simp only [List.length_cons]
      omega

/-- Intrinsic logarithmic width of every compact counter. -/
theorem compact_length_clog (bits : List Bool) (hc : Compact bits) :
    bits.length ≤ Nat.clog 2 (bitValue bits+1) := by
  apply compact_length_of_lt bits hc
  have hp := Nat.le_pow_clog (by decide : 1<(2:ℕ)) (bitValue bits+1)
  omega

/-- Actual Boolean addition followed by compact high-zero removal. -/
def add (a b : List Bool) : Report :=
  let raw := addBits a b false
  let out := trim raw.bits
  ⟨out.bits,bitCost raw+out.clock+5⟩

/-- Numeric addition correctness derives solely from the executed circuits. -/
theorem add_value (a b : List Bool) : bitValue (add a b).bits=bitValue a+bitValue b := by
  simp only [add,trim_value,addBits_correct,bitNat,Bool.false_eq_true,ite_false,Nat.add_zero]

/-- Every actual addition result is compact. -/
theorem add_compact (a b : List Bool) : Compact (add a b).bits := trim_compact _

/-- Linear actual input-width cost includes the untrimmed carry and trim scan. -/
theorem add_clock (a b : List Bool) (B : ℕ) (ha : a.length ≤ B) (hb : b.length ≤ B) :
    (add a b).clock ≤ 20*(B+1)+10 := by
  have hc := addBits_cost a b false
  have hl := (addBits_counts a b false).2.2.2.2
  have hm : max a.length b.length ≤ B := max_le ha hb
  simp only [add,trim_clock]
  omega

/-- Increment uses the literal physical one, not a natural count answer. -/
def increment (a : List Bool) : Report := add a [true]

/-- Exact counter increment. -/
theorem increment_value (a : List Bool) : bitValue (increment a).bits=bitValue a+1 := by
  simpa only [increment,bitValue,bitNat,ite_true] using add_value a [true]

/-- Every updated frequency counter is compact. -/
theorem increment_compact (a : List Bool) : Compact (increment a).bits := add_compact _ _

/-- Original tally bounds imply a logarithmic width without a supplied encoding. -/
theorem increment_length (a : List Bool) (M : ℕ) (ha : bitValue a ≤ M) :
    (increment a).bits.length ≤ Nat.clog 2 (M+2) := by
  apply compact_length_of_lt _ (increment_compact a)
  rw [increment_value]
  have hp := Nat.le_pow_clog (by decide : 1<(2:ℕ)) (M+2)
  omega

/-- Actual compact increment work from its existing physical width. -/
theorem increment_clock (a : List Bool) (B : ℕ) (hB : 1 ≤ B) (ha : a.length ≤ B) :
    (increment a).clock ≤ 20*(B+1)+10 :=
  add_clock a [true] B ha (by simpa using hB)

/-- Literal physical payload copy, including all cells. -/
def copy : List Bool → Report
  | [] => ⟨[],1⟩
  | b::bs => let tail := copy bs
             ⟨b::tail.bits,tail.clock+3⟩

/-- Copy preserves exact bits and padding. -/
theorem copy_bits (a : List Bool) : (copy a).bits=a := by
  induction a with
  | nil => rfl
  | cons b bs ih => simp only [copy,ih]

/-- Copy clock pays every physical cell. -/
theorem copy_clock (a : List Bool) : (copy a).clock=3*a.length+1 := by
  induction a with
  | nil => rfl
  | cons b bs ih => simp only [copy,List.length_cons,ih];omega

end RiemannGaussian.SemiprimeSourceCompactBits
