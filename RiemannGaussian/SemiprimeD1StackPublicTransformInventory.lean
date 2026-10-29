/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformMachine
/-! # Original-derived physical transform cache inventory -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformInventory
open SemiprimeD1StackPublicTransformMetadata SemiprimeD1StackPublicTransformWords
open SemiprimeD1StackPublicTransformLoopState SemiprimeMacroParameters
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Actual normalization bytes have no larger width than acquired M, without
any original-value or output-width advice. -/
theorem normalizer_length (bits : List Bool) (second inverse : Bool) :
    (normalizer bits second inverse).length ≤ (cached bits).length := by
  have hR : 0<transformLength bits.length := by unfold transformLength;positivity
  have hE : transformExponent bits.length+1 ≤ transformLength bits.length :=
    Nat.succ_le_of_lt (Nat.lt_two_pow_self : transformExponent bits.length<2^transformExponent bits.length)
  cases second <;> cases inverse
  · change 1 ≤ (SemiprimeD1StackFermatWords.modulusWord (transformLength bits.length)).length
    rw [SemiprimeD1StackFermatWords.modulus_length _ hR];omega
  · change 1 ≤ (SemiprimeD1StackFermatWords.modulusWord (transformLength bits.length)).length
    rw [SemiprimeD1StackFermatWords.modulus_length _ hR];omega
  · change 1 ≤ (SemiprimeD1StackFermatWords.modulusWord (transformLength bits.length)).length
    rw [SemiprimeD1StackFermatWords.modulus_length _ hR];omega
  · change (SemiprimeD1StackFermatWords.normalizerWord (transformLength bits.length) (transformExponent bits.length)).length ≤
      (SemiprimeD1StackFermatWords.modulusWord (transformLength bits.length)).length
    rw [SemiprimeD1StackFermatWords.normalizer_length _ _ hE,SemiprimeD1StackFermatWords.modulus_length _ hR]
    omega
/-- Both actual acquired axis-count caches are linearly bounded in input length. -/
theorem size_le (bits : List Bool) (second : Bool) : size bits second ≤ 64*bits.length+1 := by
  have hf : 1 ≤ firstAxis bits.length := by
    have h : 0<firstAxis bits.length := by unfold firstAxis;positivity
    omega
  have ht : 1 ≤ secondAxis bits.length := by
    have h : 0<secondAxis bits.length := by rw [secondAxis_eq_power];positivity
    omega
  have h1:=Nat.mul_le_mul_left (firstAxis bits.length) ht
  have h2:=Nat.mul_le_mul_right (secondAxis bits.length) hf
  simp only [Nat.mul_one,Nat.one_mul,axes_product] at h1 h2
  have h3:=(SemiprimeD1StackTransformArithmetic.prefix_powers bits.length (transformExponent bits.length) le_rfl).1
  change transformLength bits.length ≤ 64*bits.length+1 at h3
  cases second <;> simp only [size,Bool.false_eq_true,ite_false,ite_true] <;> omega
/-- Complete actual cache inventory; a derived function, never supplied data. -/
def inputSize (bits raw : List Bool) (second inverse : Bool) : ℕ :=
  bits.length+raw.length+(cached bits).length+(baseCode bits inverse).length+
    (normalizer bits second inverse).length+size bits second+size bits (!second)+2
/-- Every named scalar cache is dominated by this actual original inventory. -/
theorem caps (bits raw : List Bool) (second inverse : Bool) :
    bits.length ≤ inputSize bits raw second inverse ∧ raw.length ≤ inputSize bits raw second inverse ∧
    (cached bits).length ≤ inputSize bits raw second inverse ∧
    (baseCode bits inverse).length ≤ inputSize bits raw second inverse ∧
    (normalizer bits second inverse).length ≤ inputSize bits raw second inverse ∧
    size bits second ≤ inputSize bits raw second inverse ∧ size bits (!second) ≤ inputSize bits raw second inverse ∧
    2 ≤ inputSize bits raw second inverse := by unfold inputSize;omega
/-- No hidden acquired magnitude: complete caches are polynomial in literal
binary-input and raw-assignment lengths before the entire family. -/
theorem inputSize_le (bits raw : List Bool) (second inverse : Bool) :
    inputSize bits raw second inverse ≤ 2000*(bits.length+raw.length+1) := by
  have hm:=SemiprimeD1StackPublicScaleBounds.cached_length bits
  have hb:=SemiprimeD1StackPublicScaleBounds.base_length bits inverse
  change (cached bits).length ≤ _ at hm
  change (baseCode bits inverse).length ≤ 11*(cached bits).length+14 at hb
  have hn:=normalizer_length bits second inverse
  have h1:=size_le bits second
  have h2:=size_le bits (!second)
  unfold inputSize
  omega
/-- Literal encoded vector length includes every marker/high-zero word cell. -/
theorem vector_length (width : List Bool) (n : ℕ) (raw : List Bool) :
    (vectorBits (SemiprimeD1StackWordVectorSpec.blocks width n raw)).length=n*(2*width.length+2)+1 := by
  rw [←SemiprimeD1StackDigitBankSpec.entries_vectorBits,List.length_append,
    SemiprimeD1StackWordVectorSpec.entries_length,List.length_cons,List.length_nil]
/-- Both actual vector caches share the derived original width/count budget. -/
theorem vector_caps (bits raw : List Bool) (second inverse : Bool) :
    (vectorBits (inputs (rootData bits) raw second)).length ≤ 5*(inputSize bits raw second inverse)^2 ∧
    (vectorBits (outputs (rootData bits) raw second)).length ≤ 5*(inputSize bits raw second inverse)^2 := by
  obtain ⟨_,_,hm,_,_,hn,_,hS⟩:=caps bits raw second inverse
  have hc : (countWord (rootData bits) second).length=size bits second := by
    change (count bits second).length=_
    rw [count_unary,SemiprimeD1StackUnaryDivmod.unary,List.length_replicate]
  have hbound : size bits second*(2*(cached bits).length+2)+1 ≤ 5*(inputSize bits raw second inverse)^2 := by
    have h:=Nat.mul_le_mul hn (show 2*(cached bits).length+2 ≤ 2*inputSize bits raw second inverse+2 by omega)
    nlinarith
  constructor <;> (first | change (vectorBits (SemiprimeD1StackWordVectorSpec.blocks _ _ _)).length ≤ _)
  all_goals rw [vector_length,hc];exact hbound
end RiemannGaussian.SemiprimeD1StackPublicTransformInventory
