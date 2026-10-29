/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicCarryTable
import RiemannGaussian.SemiprimeD1StackStaticTableSpec
import RiemannGaussian.SemiprimeD1StackPublicInputTableTrace
/-! # Concrete complete trace contract from the frozen actual input checker
There is no unknown checker/acquisition supplier in this instance. The entire
literal51-role source executes for every leaf, with its own proved bit clock.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicCarryTableTrace
open SemiprimeD1StackPublicCarryTable SemiprimeD1StackStaticTableSpec
/-- Postcondition of actual original-N/index arithmetic, never a runtime operand. -/
def answer (bits indexWord raw : List Bool) : Bool :=
  SemiprimeD1StackPublicCarryState.answer (SemiprimeD1StackPublicCarryExecution.actualContext bits indexWord) raw
/-- The frozen actual checker's full original-input quadratic bit allowance. -/
def budget (bits indexWord : List Bool) (width : Nat) : Nat :=
  1000000000000*(bits.length+width+indexWord.length+2)^2
/-- Physical template copy and raw reversal match the SAME frozen source input. -/
theorem initial_eq (bits raw indexWord : List Bool) :
    checkerInitial static (inputTemplate bits indexWord) raw=P.initial bits raw indexWord := by
  apply congrArg (fun d=>(⟨some .start,none,none,d,[]⟩:SemiprimeD1StackCalls.State P.Stack P.Label))
    (template_raw_update bits raw indexWord)
/-- The concrete compiler's checker contract is DISCHARGED by the frozen real
source_run_bounded, including all original target/guard/integer carry arithmetic cases. -/
theorem actual_trace (bits indexWord : List Bool) (hb : bits≠[]) :
    CheckerTrace static (inputTemplate bits indexWord) (answer bits indexWord) (budget bits indexWord) := by
  intro raw
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackPublicCarryBounds.source_run_bounded bits raw indexWord hb
  refine ⟨t,ht,SemiprimeD1StackPublicCarryExecution.done bits raw indexWord,rfl,rfl,?_,rfl⟩
  rw [initial_eq]
  exact hr
/-- Only the original binary N and actual physical query-index markers are
initialized; target/modulus/radix/guards/words/verdict remain genuinely unacquired. -/
theorem template_only (bits indexWord : List Bool) (k : P.Stack) :
    inputTemplate bits indexWord k=if k=P.inputRole then bits else if k=P.index then indexWord else [] := by
  rcases k with k|k
  · rcases k with k|k
    · change SemiprimeD1BinaryPublicAcquisition.input bits k=
        if (Sum.inl (Sum.inl k):P.Stack)=P.inputRole then bits
        else if (Sum.inl (Sum.inl k):P.Stack)=P.index then indexWord else []
      rw [SemiprimeD1StackPublicInputTableTrace.public_input_only]
      simp only [SemiprimeD1StackPublicCarry.inputRole,P.index,Sum.inl.injEq,Sum.inl_ne_inr,ite_false]
    · cases k <;> rfl
  · cases k <;> rfl
/-- Every initialized template field is paid by original N and actual index markers. -/
theorem template_cell_le (bits indexWord : List Bool) (k : P.Stack) :
    (inputTemplate bits indexWord k).length≤ bits.length+indexWord.length := by
  rw [template_only]
  split
  · exact Nat.le_add_right _ _
  · split
    · exact Nat.le_add_left _ _
    · exact Nat.zero_le _
end RiemannGaussian.SemiprimeD1StackPublicCarryTableTrace
