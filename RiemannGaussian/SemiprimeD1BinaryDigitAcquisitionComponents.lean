/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BinaryDigitAcquisition

/-! # Real metadata and inter-stage copy executions
Every bank operand comes from a complete executed original-input metadata trace
and real Copy instructions. Mathematical store views are never runtime suppliers.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1BinaryDigitAcquisitionComponents
open SemiprimeD1BinaryDigitAcquisition SemiprimeD1StackProcedureTrace

/-- Proof-side view of the physically acquired width word. -/
def radix (bits : List Bool) : List Bool := (SemiprimeD1StackTransformExecution.result bits) .radix

/-- Metadata return store with every bank/copy cell still empty. -/
def afterMetadata (bits : List Bool) : Stack→List Bool :=
  store (SemiprimeD1StackTransformExecution.result bits) (fun _=>[]) []

/-- After the real retained-input copy, still before acquiring bank width. -/
def afterInputCopy (bits : List Bool) : Stack→List Bool :=
  store (SemiprimeD1StackTransformExecution.result bits)
    (SemiprimeD1StackDigitBank.store bits [] [] [] [] []) []

/-- After BOTH real copies the bank's physical initial arguments exist. -/
def afterRadixCopy (bits : List Bool) : Stack→List Bool :=
  store (SemiprimeD1StackTransformExecution.result bits)
    (SemiprimeD1StackDigitBank.store bits [] (radix bits) [] [] []) []

/-- The acquired marker count is exactly the original public radix formula. -/
theorem radix_length (bits : List Bool) : (radix bits).length=SemiprimeMacroParameters.radixBits bits.length := by
  change (List.replicate (SemiprimeMacroParameters.radixBits bits.length) true).length=_
  exact List.length_replicate

/-- Physical positive input width gives positive acquired radix, with no supplied
stop/width answer. Source code derives it by its literal bootstrap and loops. -/
theorem radix_nonempty (bits : List Bool) (hb : bits≠[]) : radix bits≠[] := by
  have hn : 0 < bits.length := List.length_pos_iff.mpr hb
  apply List.ne_nil_of_length_pos
  rw [radix_length]
  exact SemiprimeMacroParameters.radixBits_pos hn

/-- The WHOLE original-input metadata supplier executes inside the actual caller. -/
theorem metadata_call (bits : List Bool) :
    Runs program (SemiprimeD1StackTransformArithmetic.totalTime bits.length+1)
      (mainLabel .start) (SemiprimeD1BinaryDigitAcquisition.input bits)
      (mainLabel .copyInput) (afterMetadata bits) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program metaStack metaLabel Sum.inl_injective
    Meta.program (.inl .start) (fun _=>rfl) (mainLabel .start) (mainLabel .copyInput) rfl
    (SemiprimeD1StackTransformArithmetic.totalTime bits.length)
    (Meta.initial bits) (SemiprimeD1StackTransformExecution.done bits)
    (SemiprimeD1BinaryDigitAcquisition.input bits) (afterMetadata bits)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackTransformExecution.acquire_run bits
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact False.elim (hk k rfl)
      · rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact False.elim (hk k rfl)
      · rfl

/-- Original binary N is copied by actual instructions, never preloaded into the bank. -/
theorem input_copy (bits : List Bool) :
    Runs program (5*bits.length+4) (mainLabel .copyInput) (afterMetadata bits)
      (mainLabel .copyRadix) (afterInputCopy bits) := by
  apply included_call program (copyStack false) (copyLabel false) (copyStack_injective false)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) (mainLabel .copyInput) (mainLabel .copyRadix) rfl
    (5*bits.length+3) (SemiprimeD1StackCopy.state 0 none bits [] []) (SemiprimeD1StackCopy.done bits bits)
    (afterMetadata bits) (afterInputCopy bits)
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words bits [] none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk
      have hi:=hk 1
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · rcases k with k|k
          · cases k <;> rfl
          · fin_cases k <;>
              simp_all [copyStack,copyTarget,bankStack,SemiprimeD1StackDigitBank.original,
                afterMetadata,afterInputCopy,store,SemiprimeD1StackDigitBank.store]
        · rfl

/-- The bank radix cache is acquired by another actual inter-stage copy. -/
theorem radix_copy (bits : List Bool) :
    Runs program (5*(radix bits).length+4) (mainLabel .copyRadix) (afterInputCopy bits)
      (mainLabel .bankCall) (afterRadixCopy bits) := by
  apply included_call program (copyStack true) (copyLabel true) (copyStack_injective true)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) (mainLabel .copyRadix) (mainLabel .bankCall) rfl
    (5*(radix bits).length+3) (SemiprimeD1StackCopy.state 0 none (radix bits) [] [])
    (SemiprimeD1StackCopy.done (radix bits) (radix bits)) (afterInputCopy bits) (afterRadixCopy bits)
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words (radix bits) [] none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk
      have hi:=hk 1
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · rcases k with k|k
          · cases k <;>
              simp_all [copyStack,copyTarget,bankStack,afterInputCopy,afterRadixCopy,store,
                SemiprimeD1StackDigitBank.store,SemiprimeD1StackDigitBlock.store]
          · rfl
        · rfl

end RiemannGaussian.SemiprimeD1BinaryDigitAcquisitionComponents
