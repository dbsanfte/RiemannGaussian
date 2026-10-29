/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicCarryExecution
import RiemannGaussian.SemiprimeD1StackRootSourceOriginal
/-! # Integer semantics of the acquired public carry computation -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicCarryOriginal
open SemiprimeD1StackPublicCarry SemiprimeD1StackPublicCarryState
open SemiprimeD1StackPublicCarryExecution SemiprimeBitArithmetic SemiprimeMacroParameters
/-- Every computed branch bit is characterized by the actual integer operands.
This theorem assumes neither guards nor their answers. -/
theorem answer_true (context : T.Stack→List Bool) (raw : List Bool) :
    answer context raw=true ↔
      bitValue (coefficient context raw)<bitValue (width context) ∧
      bitValue (previous context raw)<bitValue (boundWord context) ∧
      bitValue (next context raw)<bitValue (boundWord context) ∧
      bitValue (coefficient context raw)+bitValue (previous context raw)=
        bitValue (target context)+2^(radix context).length*bitValue (next context raw) := by
  simp only [answer,Bool.and_eq_true,guardAnswer,guardBound,word,Fin.reduceEq,
    ite_true,ite_false,SemiprimeD1StackWordLessExecution.answer_true,
    equationAnswer,SemiprimeD1StackCarryEquationExecution.answer,
    SemiprimeMacroEntryBitPrimitives.carryEquationBits_correct]
/-- Actual acquired modulus width, without a supplied size answer. -/
theorem acquired_width_length (bits index : List Bool) :
    (width (actualContext bits index)).length=SemiprimeMacroParameters.transformLength bits.length+1 := by
  exact SemiprimeD1StackRootSourceOriginal.modulus_length bits
/-- Actual radix cache has the original physically acquired template length. -/
theorem acquired_radix_length (bits index : List Bool) :
    (radix (actualContext bits index)).length=SemiprimeMacroParameters.radixBits bits.length := by
  change (List.replicate (SemiprimeMacroParameters.radixBits bits.length) true).length=_
  exact List.length_replicate
/-- The actual low-bit-replaced modulus word represents the strict carry bound. -/
theorem acquired_bound_value (bits index : List Bool) :
    bitValue (boundWord (actualContext bits index))=2^SemiprimeMacroParameters.transformLength bits.length := by
  let n:=SemiprimeMacroParameters.transformLength bits.length
  have hn : 0<n := by unfold n SemiprimeMacroParameters.transformLength;positivity
  change bitValue (false::(List.replicate (n-1) false++[true]))=2^n
  rw [bitValue,SemiprimeD1StackFermatWords.zeros_value]
  simp only [bitNat,Bool.false_eq_true,ite_false,Nat.zero_add]
  have he : n-1+1=n := by omega
  simp only [bitValue,bitNat,ite_true,Nat.mul_zero,Nat.add_zero,Nat.mul_one]
  rw [Nat.mul_comm,←Nat.pow_succ]
  congr 1
/-- Actual modulus value, acquired by the original binary preprocessing. -/
theorem acquired_modulus_value (bits index : List Bool) :
    bitValue (width (actualContext bits index))=2^SemiprimeMacroParameters.transformLength bits.length+1 := by
  change bitValue (SemiprimeD1StackFermatWords.modulusWord (SemiprimeMacroParameters.transformLength bits.length))=_
  exact SemiprimeD1StackFermatWords.modulus_value _ (by unfold SemiprimeMacroParameters.transformLength;positivity)
/-- Original public carry semantics after ACTUAL target acquisition, for every
raw assignment (including incomplete/padded ones). No guard truth is assumed. -/
theorem acquired_carry (bits raw index : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) :
    answer (actualContext bits index) raw=
      (SemiprimeMacroEntryBitCheck.carryRun (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN)
        (target (actualContext bits index)) (coefficient (actualContext bits index) raw)
        (previous (actualContext bits index) raw) (next (actualContext bits index) raw)).accepted := by
  apply Bool.eq_iff_iff.mpr
  rw [answer_true,SemiprimeMacroEntryBitCheck.carryRun_correct,
    acquired_modulus_value,acquired_bound_value,acquired_radix_length]
  have hw:=SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc
  rw [hw]
  simp only [SemiprimePublicFactorCount.publicConfig,SemiprimeMacroParameters.axes_product]
/-- An old target WORD need not have identical zero padding: the physical
INTEGER verdict depends on its value, not its byte representation. -/
theorem acquired_target_carry (bits raw index : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (k : Fin (SemiprimeMacroParameters.firstAxis (bitLength (bitValue bits))*
      SemiprimeMacroParameters.secondAxis (bitLength (bitValue bits)))) (hi : index.length=k.val) :
    answer (actualContext bits index) raw=
      (SemiprimeMacroEntryBitCheck.carryRun (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN)
        ((SemiprimeMacroEntryBitCheck.configTargets (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN)).words k)
        (coefficient (actualContext bits index) raw) (previous (actualContext bits index) raw)
        (next (actualContext bits index) raw)).accepted := by
  rw [acquired_carry bits raw index hc hN]
  apply Bool.eq_iff_iff.mpr
  rw [SemiprimeMacroEntryBitCheck.carryRun_correct,SemiprimeMacroEntryBitCheck.carryRun_correct]
  have ht:=SemiprimeD1StackPublicTargetExecution.target_original bits index hc hN
  change bitValue (target (actualContext bits index))=_ at ht
  have hv : bitValue ((SemiprimeMacroEntryBitCheck.configTargets
      (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN)).words k)=
      targetDigit (bitLength (bitValue bits)) (bitValue bits) k.val :=
    (SemiprimeMacroEntryBitCheck.configTargets (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN)).value k
  rw [ht,hi,hv]
end RiemannGaussian.SemiprimeD1StackPublicCarryOriginal
