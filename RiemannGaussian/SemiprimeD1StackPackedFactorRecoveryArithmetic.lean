/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryEncoding
import RiemannGaussian.SemiprimeD1PackedMomentRecovery
/-! # Exact arithmetic of physically computed discriminants and half words
These are specification proofs about actual component output words, never
runtime arithmetic operands or clocks. The source consumes only N and V.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryArithmetic
open SemiprimeD1StackPackedFactorRecoveryEncoding SemiprimeBitArithmetic SemiprimeBitDivision
/-- Actual borrow is FALSE exactly on the required non-underflow branch. -/
theorem no_borrow (xs ys : List Bool) (h : bitValue ys≤bitValue xs) : (subBits xs ys false).borrow=false := by
  cases hb:(subBits xs ys false).borrow with
  | false=>rfl
  | true=>
    have ht:=(subBits_borrow_iff xs ys false).mp hb
    simp only [bitNat,Bool.false_eq_true,ite_false,Nat.add_zero] at ht
    omega
/-- The two literal FALSE pushes multiply by four without unary expansion. -/
theorem fourWord_value (n : List Bool) : bitValue (fourWord n)=4*bitValue n := by
  simp only [fourWord,bitValue,bitNat,Bool.false_eq_true,ite_false,Nat.zero_add]
  ring
/-- The actual subtraction is nonnegative on every pair of true ordered factors. -/
theorem discriminant_borrow (n s : List Bool) (p q : ℕ) (hn : bitValue n=p*q) (hs : bitValue s=p+q) :
    (discriminantReport n s).borrow=false := by
  apply no_borrow
  rw [fourWord_value,squareWord,mulBits_correct,hn,hs]
  nlinarith [sq_nonneg (p-q : ℤ)]
/-- The actual binary discriminant equals the integer prime-gap square. -/
theorem discriminant_value (n s : List Bool) (p q : ℕ) (hn : bitValue n=p*q)
    (hs : bitValue s=p+q) (hpq : p≤q) : bitValue (discriminant n s)=(q-p)^2 := by
  have hb:=discriminant_borrow n s p q hn hs
  rw [discriminant,discriminantReport,subBits_difference hb,squareWord,mulBits_correct,fourWord_value,hn,hs]
  simpa only [pow_two] using SemiprimeD1PackedMomentRecovery.discriminant p q hpq
/-- The ENTIRE frozen source's actual root output is exactly the ordered factor gap. -/
theorem rootWord_value (n s : List Bool) (p q : ℕ) (hn : bitValue n=p*q)
    (hs : bitValue s=p+q) (hpq : p≤q) : bitValue (rootWord n s)=q-p := by
  rw [rootWord,SemiprimeD1StackBinarySquareRootArithmetic.output_value,discriminant_value n s p q hn hs hpq,Nat.sqrt_eq']
/-- A physical least-significant-bit pop divides the represented binary value by two. -/
theorem tail_value (xs : List Bool) : bitValue xs.tail=bitValue xs/2 := by
  cases xs with
  | nil=>rfl
  | cons b xs=>cases b <;> simp only [List.tail_cons,bitValue,bitNat,Bool.false_eq_true,ite_false,ite_true] <;> omega
/-- Positive even numerator words really contain a FALSE digit; EOF is never substituted. -/
theorem even_head (xs : List Bool) (p : ℕ) (hp : 0<p) (hv : bitValue xs=2*p) :
    ∃tail, xs=false::tail := by
  cases xs with
  | nil=>simp only [bitValue] at hv;omega
  | cons b xs=>
    cases b with
    | false=>exact ⟨xs,rfl⟩
    | true=>simp only [bitValue,bitNat,ite_true] at hv;omega
/-- Real low-bit pop and real high-zero compaction retain the exact half integer. -/
theorem halfWord_exact (xs : List Bool) (p : ℕ) (hv : bitValue xs=2*p) : bitValue (halfWord xs)=p := by
  rw [halfWord_value,tail_value,hv,Nat.mul_div_right _ (by decide : 0<2)]
/-- The lower numerator has an actual FALSE borrow, positive even value and exact lower half. -/
theorem minus_exact (s root : List Bool) (p q : ℕ) (hp : 0<p) (hpq : p≤q)
    (hs : bitValue s=p+q) (hr : bitValue root=q-p) :
    (minusReport s root).borrow=false ∧ (∃tail,(minusReport s root).result.bits=false::tail) ∧
      bitValue (halfWord (minusReport s root).result.bits)=p := by
  have hb : (minusReport s root).borrow=false := no_borrow s root (by omega)
  have hv : bitValue (minusReport s root).result.bits=2*p := by
    rw [minusReport,subBits_difference hb,hs,hr]
    omega
  exact ⟨hb,even_head _ p hp hv,halfWord_exact _ p hv⟩
/-- The upper numerator has an actual FALSE parity digit and exact upper half. -/
theorem plus_exact (s root : List Bool) (p q : ℕ) (hq : 0<q) (hpq : p≤q)
    (hs : bitValue s=p+q) (hr : bitValue root=q-p) :
    (∃tail,plusWord s root=false::tail) ∧ bitValue (halfWord (plusWord s root))=q := by
  have hv : bitValue (plusWord s root)=2*q := by
    rw [plusWord,addBits_correct]
    simp only [bitNat,Bool.false_eq_true,ite_false,Nat.add_zero]
    omega
  exact ⟨even_head _ q hq hv,halfWord_exact _ q hv⟩
end RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryArithmetic
