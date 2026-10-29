/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitFermatArithmetic

/-! # Physical radix assembly of the original operand digits
The actual output is assembled by Boolean shifts and ripple additions. Natural
values and radix powers occur only in the correctness specification. The radix
is a physical offset template; each shift traverses and charges that template.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1RadixOperandBits
open SemiprimeBitArithmetic SemiprimeBitFermatArithmetic

/-- Actual assembled operand and its full physical shift/add report. -/
structure Run where
  /-- Literal little-endian output bits. -/
  bits : List Bool
  /-- Every shift-template read/copy, ripple addition and recursion tag. -/
  clock : ℕ

/-- Little-endian Horner assembly from original physical digit words. -/
def run (radix : List Bool) : List (List Bool) → Run
  | [] => ⟨[],1⟩
  | digit::digits =>
    let tail := run radix digits
    let shifted := shiftTemplateBits radix tail.bits
    let added := addBits digit shifted.bits false
    ⟨added.bits,tail.clock+bitCost shifted+bitCost added+7⟩

/-- Proof-only mathematical radix value of a literal list of digit words. -/
def value (base : ℕ) : List (List Bool) → ℕ
  | [] => 0
  | digit::digits => bitValue digit+base*value base digits

/-- No natural multiplication computes the runtime operand; the actual Boolean
result has exactly the original radix value. -/
theorem run_value (radix : List Bool) (digits : List (List Bool)) :
    bitValue (run radix digits).bits=value (2^radix.length) digits := by
  induction digits with
  | nil => rfl
  | cons digit digits ih =>
    change bitValue (addBits digit (shiftTemplateBits radix (run radix digits).bits).bits false).bits = _
    rw [addBits_correct,(shiftTemplateBits_exact radix (run radix digits).bits).1,ih]
    simp only [bitNat,Bool.false_eq_true,ite_false,Nat.add_zero,value]

/-- The physical output remains polynomial in supplied digit count and widths,
including carries and arbitrary zero padding. -/
theorem run_width (radix : List Bool) (digits : List (List Bool)) (W : ℕ)
    (hw : ∀ digit ∈ digits,digit.length ≤ W) :
    (run radix digits).bits.length ≤ digits.length*(radix.length+W+1) := by
  induction digits with
  | nil => simp only [run,List.length_nil,Nat.zero_mul,le_refl]
  | cons digit digits ih =>
    have hd := hw digit List.mem_cons_self
    have ht := ih (fun row hr => hw row (List.mem_cons_of_mem digit hr))
    have hs := (shiftTemplateBits_exact radix (run radix digits).bits).2.1
    have ha := (addBits_counts digit (shiftTemplateBits radix (run radix digits).bits).bits false).2.2.2.2
    change (addBits digit (shiftTemplateBits radix (run radix digits).bits).bits false).bits.length ≤ _
    simp only [List.length_cons]
    have hm : max digit.length (shiftTemplateBits radix (run radix digits).bits).bits.length ≤
        radix.length+W+digits.length*(radix.length+W+1) := by omega
    nlinarith

/-- Complete shift/add clock is one fixed polynomial in the literal original
digit widths and count, without an operand-value or cost advice premise. -/
theorem run_clock (radix : List Bool) (digits : List (List Bool)) (W : ℕ)
    (hw : ∀ digit ∈ digits,digit.length ≤ W) :
    (run radix digits).clock ≤ 20*(digits.length+1)^2*(radix.length+W+1) := by
  induction digits with
  | nil => simp only [run,List.length_nil];nlinarith
  | cons digit digits ih =>
    have hd := hw digit List.mem_cons_self
    have htail := fun row hr => hw row (List.mem_cons_of_mem digit hr)
    have ht := ih htail
    have hwidth := run_width radix digits W htail
    have hs := shiftTemplateBits_exact radix (run radix digits).bits
    have ha := addBits_cost digit (shiftTemplateBits radix (run radix digits).bits).bits false
    have hm : max digit.length (shiftTemplateBits radix (run radix digits).bits).bits.length ≤
        (digits.length+1)*(radix.length+W+1) := by
      apply max_le
      · nlinarith
      · rw [hs.2.1]
        nlinarith
    change (run radix digits).clock+bitCost (shiftTemplateBits radix (run radix digits).bits)+
      bitCost (addBits digit (shiftTemplateBits radix (run radix digits).bits).bits false)+7 ≤ _
    simp only [List.length_cons]
    nlinarith

/-- Reindexing the proof-only Horner value yields precisely the public decoder's
finite original radix sum. Runtime still uses only the Boolean recursion above. -/
theorem value_range (base n : ℕ) (digit : ℕ → List Bool) :
    value base ((List.range n).map digit) =
      ∑ i ∈ Finset.range n,bitValue (digit i)*base^i := by
  induction n generalizing digit with
  | zero => simp only [List.range_zero,List.map_nil,value,Finset.sum_range_zero]
  | succ n ih =>
    rw [List.range_succ_eq_map,List.map_cons,List.map_map,value,ih]
    rw [Finset.sum_range_succ']
    simp only [Function.comp_def,Nat.succ_eq_add_one,pow_zero,Nat.mul_one,pow_succ]
    rw [Finset.mul_sum]
    have he : (∑i∈Finset.range n,base*bitValue (digit (i+1))*base^i)=
        ∑i∈Finset.range n,bitValue (digit (i+1))*(base^i*base) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_rw [←mul_assoc]
    rw [he]
    simp only [mul_assoc]
    exact Nat.add_comm _ _

end RiemannGaussian.SemiprimeD1RadixOperandBits
