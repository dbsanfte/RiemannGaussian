/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetAxes

/-! # Actual unsigned coordinate arithmetic modulo2^p
Output truncation scans/copies physical bits, never decodes and reencodes them.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1JetScalarBits
open SemiprimeBitArithmetic
/-- Actual physical scalar output and retained bit/cell report. -/
abbrev Report := SemiprimeSourceCompactBits.Report

/-- Copy at most p low bits, with every visited cell charged. -/
def takeBits : ℕ→List Bool→Report
  | 0,_ => ⟨[],1⟩
  | _+1,[] => ⟨[],1⟩
  | p+1,b::bs =>
    let tail:=takeBits p bs
    ⟨b::tail.bits,tail.clock+3⟩

/-- The acquired output is exactly the low physical prefix. -/
theorem takeBits_bits (p : ℕ) (bits : List Bool) : (takeBits p bits).bits=bits.take p := by
  induction p generalizing bits with
  | zero => rfl
  | succ p ih => cases bits <;> simp [takeBits,ih]

/-- Truncation performs only the actual prefix scan. -/
theorem takeBits_clock (p : ℕ) (bits : List Bool) : (takeBits p bits).clock≤3*p+1 := by
  induction p generalizing bits with
  | zero => simp [takeBits]
  | succ p ih =>
    cases bits with
    | nil => simp [takeBits]
    | cons b bs =>
      have h:=ih bs
      simp only [takeBits]
      omega

/-- Exact low/high binary decomposition, independent of compactness. -/
theorem bitValue_split (p : ℕ) (bits : List Bool) :
    bitValue bits=bitValue (bits.take p)+2^p*bitValue (bits.drop p) := by
  induction p generalizing bits with
  | zero => simp [bitValue]
  | succ p ih =>
    cases bits with
    | nil => simp [bitValue]
    | cons b bs =>
      simp only [List.take_succ_cons,List.drop_succ_cons,bitValue,pow_succ]
      rw [ih bs]
      ring

/-- A low prefix has a genuine modulus-sized numerical bound. -/
theorem bitValue_take_lt (p : ℕ) (bits : List Bool) : bitValue (bits.take p)<2^p :=
  (bitValue_lt_width _).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) (List.length_take_le p bits))

/-- Taking low bits implements the exact residue, not a magnitude-linear reencoding. -/
theorem bitValue_take (p : ℕ) (bits : List Bool) : bitValue (bits.take p)=bitValue bits%2^p := by
  rw [bitValue_split p bits,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (bitValue_take_lt p bits)]

/-- Physical modular reduction followed by high-zero removal. -/
def reduce (p : ℕ) (bits : List Bool) : Report :=
  let low:=takeBits p bits
  let out:=SemiprimeSourceCompactBits.trim low.bits
  ⟨out.bits,low.clock+out.clock+3⟩

/-- Modular output has the canonical numerical value. -/
theorem reduce_value (p : ℕ) (bits : List Bool) : bitValue (reduce p bits).bits=bitValue bits%2^p := by
  simp only [reduce,SemiprimeSourceCompactBits.trim_value,takeBits_bits,bitValue_take]

/-- Physical reduction always yields a compact word. -/
theorem reduce_compact (p : ℕ) (bits : List Bool) :
    SemiprimeSourceCompactBits.Compact (reduce p bits).bits := SemiprimeSourceCompactBits.trim_compact _

/-- Actual output width is bounded by the target precision. -/
theorem reduce_length (p : ℕ) (bits : List Bool) : (reduce p bits).bits.length≤p := by
  exact (SemiprimeSourceCompactBits.trim_length _).trans (by rw [takeBits_bits];exact List.length_take_le p bits)

/-- No original or intermediate word-width premise controls reduction. -/
theorem reduce_clock (p : ℕ) (bits : List Bool) : (reduce p bits).clock≤9*p+5 := by
  have hl : (takeBits p bits).bits.length≤p := by rw [takeBits_bits];exact List.length_take_le p bits
  have ht:=takeBits_clock p bits
  have hc:=SemiprimeSourceCompactBits.trim_clock (takeBits p bits).bits
  simp only [reduce]
  omega

/-- Actual physical modular coordinate sum, retaining the original scalar circuit. -/
def add (p : ℕ) (a b : List Bool) : Report :=
  let out:=addBits a b false
  let reduced:=reduce p out.bits
  ⟨reduced.bits,bitCost out+reduced.clock+3⟩

/-- Actual physical modular coordinate product, retaining all shifted/addition work. -/
def mul (p : ℕ) (a b : List Bool) : Report :=
  let out:=mulBits a b
  let reduced:=reduce p out.bits
  ⟨reduced.bits,bitCost out+reduced.clock+3⟩

/-- Modular addition correctness without output advice. -/
theorem add_value (p : ℕ) (a b : List Bool) :
    bitValue (add p a b).bits=(bitValue a+bitValue b)%2^p := by
  simp only [add,reduce_value,addBits_correct,bitNat,Bool.false_eq_true,ite_false,Nat.add_zero]

/-- Modular product correctness without output advice. -/
theorem mul_value (p : ℕ) (a b : List Bool) :
    bitValue (mul p a b).bits=(bitValue a*bitValue b)%2^p := by
  simp only [mul,reduce_value,mulBits_correct]

/-- Every sum word has target width. -/
theorem add_length (p : ℕ) (a b : List Bool) : (add p a b).bits.length≤p := reduce_length _ _

/-- Every product word has target width. -/
theorem mul_length (p : ℕ) (a b : List Bool) : (mul p a b).bits.length≤p := reduce_length _ _

/-- Every modular sum is intrinsically compact. -/
theorem add_compact (p : ℕ) (a b : List Bool) :
    SemiprimeSourceCompactBits.Compact (add p a b).bits := reduce_compact _ _

/-- Every modular product is intrinsically compact. -/
theorem mul_compact (p : ℕ) (a b : List Bool) :
    SemiprimeSourceCompactBits.Compact (mul p a b).bits := reduce_compact _ _

/-- All addition/reduction work is retained with explicit input widths. -/
theorem add_clock (p : ℕ) (a b : List Bool) :
    (add p a b).clock≤11*max a.length b.length+9*p+12 := by
  have ha:=addBits_cost a b false
  have hr:=reduce_clock p (addBits a b false).bits
  simp only [add]
  omega

/-- All product/reduction work is retained with explicit input widths. -/
theorem mul_clock (p : ℕ) (a b : List Bool) :
    (mul p a b).clock≤12*a.length*(a.length+b.length+2)+9*p+9 := by
  have ha:=mulBits_cost a b
  have hr:=reduce_clock p (mulBits a b).bits
  simp only [mul]
  omega

/-- The acquired scalar sum denotes addition in the actual residue ring. -/
theorem add_zmod (p : ℕ) (a b : List Bool) :
    (bitValue (add p a b).bits : ZMod (2^p))=(bitValue a:ZMod (2^p))+(bitValue b:ZMod (2^p)) := by
  rw [add_value,ZMod.natCast_mod,Nat.cast_add]

/-- The acquired scalar product denotes multiplication in the actual residue ring. -/
theorem mul_zmod (p : ℕ) (a b : List Bool) :
    (bitValue (mul p a b).bits : ZMod (2^p))=(bitValue a:ZMod (2^p))*(bitValue b:ZMod (2^p)) := by
  rw [mul_value,ZMod.natCast_mod,Nat.cast_mul]

end RiemannGaussian.SemiprimeD1JetScalarBits
