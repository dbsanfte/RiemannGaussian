/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecision
/-! # Binary counter/shift/sum values for the actual precision source -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
namespace RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionArithmetic
open SemiprimeBitArithmetic
namespace I
export SemiprimeD1StackIncrement (wrapped wrapped_length wrapped_value)
end I
/-- Exact zero allocation is physical padding, never a unary numeric binary operand. -/
theorem zero_value (n : Nat) : bitValue (List.replicate n false)=0 :=by
  induction n with
  | zero=>rfl
  | succ n ih=>simp only [List.replicate_succ,bitValue,bitNat,Bool.false_eq_true,ite_false,Nat.zero_add,ih,Nat.mul_zero]
/-- Repeated REAL fixed-width increments retain their exact physical width. -/
theorem iterate_length (n : Nat) (xs : List Bool) : ((I.wrapped^[n]) xs).length=xs.length :=by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [Function.iterate_succ_apply',I.wrapped_length,ih]
/-- Exact modular semantics of repeated actual wrapped increments, including width0. -/
theorem iterate_value (n : Nat) (xs : List Bool) :
    bitValue ((I.wrapped^[n]) xs)=(bitValue xs+n)%2^xs.length :=by
  induction n with
  | zero=>simpa only [Function.iterate_zero_apply,Nat.add_zero] using (Nat.mod_eq_of_lt (bitValue_lt_width xs)).symm
  | succ n ih=>
    rw [Function.iterate_succ_apply',I.wrapped_value,iterate_length,ih,Nat.mod_add_mod]
    rw [Nat.add_assoc]
/-- The polynomial padding width is strictly above the number of metadata rounds. -/
theorem capacity (n : Nat) : n<2^n :=by
  induction n with
  | zero=>decide
  | succ n ih=>
    rw [pow_succ]
    have hp:0<(2:Nat)^n:=by positivity
    omega
/-- Exact output of n paid increments on a physically allocated n+1-bit zero word. -/
def counterWord (n : Nat) : List Bool :=(I.wrapped^[n]) (List.replicate (n+1) false)
/-- Bounded unary n is converted to a BINARY value n by actual increment rounds. -/
theorem counterWord_value (n : Nat) : bitValue (counterWord n)=n :=by
  rw [counterWord,iterate_value,zero_value,List.length_replicate,Nat.zero_add]
  exact Nat.mod_eq_of_lt (by have h:=capacity (n+1);omega)
/-- Paid binary counter width is polynomial in the original bounded unary metadata. -/
theorem counterWord_length (n : Nat) : (counterWord n).length=n+1 :=by
  rw [counterWord,iterate_length,List.length_replicate]
/-- Actual low-zero shifts; no numeric power is materialized as unary. -/
def shift (n : Nat) (xs : List Bool) : List Bool :=List.replicate n false++xs
/-- Physical shifts multiply the binary value by the exact power of two. -/
theorem shift_value (n : Nat) (xs : List Bool) : bitValue (shift n xs)=2^n*bitValue xs :=by
  induction n with
  | zero=>simp [shift]
  | succ n ih=>
    change bitValue (false::shift n xs)=2^(n+1)*bitValue xs
    simp only [bitValue,bitNat,Bool.false_eq_true,ite_false,Nat.zero_add,ih,pow_succ]
    ring
/-- Every binary shift writes exactly one physical cell. -/
theorem shift_length (n : Nat) (xs : List Bool) : (shift n xs).length=n+xs.length :=by simp [shift]
/-- Actual shifted h word implements8*h*D with D kept BINARY. -/
def heightTerm (h delta : Nat) : List Bool :=shift 3 (shift delta (counterWord h))
/-- Actual shifted bounded r word implements8*M*(a+1). -/
def productTerm (r : Nat) : List Bool :=shift 3 (counterWord r)
/-- Actual first binary ripple result, including all physical padding. -/
def partialWord (h delta : Nat) (p : List Bool) : List Bool :=(addBits (heightTerm h delta) p false).bits
/-- Actual second binary ripple result, without canonicalization or an advised answer word. -/
def precisionWord (h r delta : Nat) (p : List Bool) : List Bool :=
  (addBits (partialWord h delta p) (productTerm r) false).bits
/-- Both real binary adders compute exactly the original precision expression. -/
theorem precisionWord_value (h r delta : Nat) (p : List Bool) :
    bitValue (precisionWord h r delta p)=bitValue p+8*h*2^delta+8*r :=by
  simp only [precisionWord,partialWord,addBits_correct,bitNat,Bool.false_eq_true,ite_false,Nat.add_zero,
    heightTerm,productTerm,shift_value,counterWord_value]
  norm_num
  ring
/-- Exact physical length bound for the first actual adder result. -/
theorem partialWord_length (h delta : Nat) (p : List Bool) :
    (partialWord h delta p).length≤ h+delta+p.length+5 :=by
  have hb:=(addBits_counts (heightTerm h delta) p false).2.2.2.2
  have hl:(heightTerm h delta).length=3+(delta+(h+1)):=by rw [heightTerm,shift_length,shift_length,counterWord_length]
  change (partialWord h delta p).length≤ max (heightTerm h delta).length p.length+1 at hb
  omega
end RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionArithmetic
