/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOrdinalBank
import RiemannGaussian.SemiprimeD1StackProcedureFragments
/-! # Actual Copy, logger, binary Increment and final Reverse calls -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackOrdinalBankCalls
open SemiprimeD1StackOrdinalBank
open SemiprimeD1StackProcedureFragments (Runs included_call)
open SemiprimeSourceHistogramKeyBits (frame)

/-- First actual tally copy drives zero allocation; its source cache is retained. -/
theorem copy_zero (tally : List Bool) :
    Runs program (5*tally.length+4) (.inl .start) (data [] [] [] [] [] tally [] [] [])
      (.inl .makeZero) (data [] [] [] [] [] tally [] tally []) := by
  apply included_call program (copyStack true) (copyLabel true) (copyStack_injective true)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) (.inl .start) (.inl .makeZero) rfl (5*tally.length+3)
    (SemiprimeD1StackCopy.state 0 none tally [] []) (SemiprimeD1StackCopy.done tally tally)
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words tally [] none
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk
      cases k with
      | inl k => rfl
      | inr k =>
        cases k with
        | count => rfl
        | remaining => rfl
        | zeroRemaining => exact False.elim (hk 1 rfl)
        | copyScratch => rfl

/-- A second actual tally copy supplies exactly the finite round markers. -/
theorem copy_remaining (tally word : List Bool) :
    Runs program (5*tally.length+4) (.inl .copyRemaining) (data word [] [] [] [] tally [] [] [])
      (.inl .loop) (data word [] [] [] [] tally tally [] []) := by
  apply included_call program (copyStack false) (copyLabel false) (copyStack_injective false)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) (.inl .copyRemaining) (.inl .loop) rfl (5*tally.length+3)
    (SemiprimeD1StackCopy.state 0 none tally [] []) (SemiprimeD1StackCopy.done tally tally)
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words tally [] none
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk
      cases k with
      | inl k => rfl
      | inr k =>
        cases k with
        | count => rfl
        | remaining => exact False.elim (hk 1 rfl)
        | zeroRemaining => rfl
        | copyScratch => rfl

/-- The actual fixed logger restores the binary word and emits its full padded
framed bytes into the chronological reverse log; it is not a body callback. -/
theorem body_call (word history output tally todo : List Bool) :
    ∃ m≤6*(2*word.length+3)+1,
      Runs program m (.inl .bodyCall) (data word [] [] history output tally todo [] [])
        (.inl .incrementCall) (data word [] [] ((true::frame word []).reverse++history) output tally todo [] []) := by
  obtain ⟨m,hm,hr⟩:=SemiprimeD1StackAssignmentBody.body_run word history
  refine ⟨m+1,by omega,?_⟩
  apply included_call program bodyStack bodyLabel bodyStack_injective Body.code Body.entry (fun _=>rfl)
    (.inl .bodyCall) (.inl .incrementCall) rfl m
    (⟨some Body.entry,none,SemiprimeD1StackAssignmentBody.contents word [] history⟩:
      SemiprimeD1StackBytecode.State Body.Stack Body.Label)
    (⟨none,none,SemiprimeD1StackAssignmentBody.contents word [] ((true::frame word []).reverse++history)⟩:
      SemiprimeD1StackBytecode.State Body.Stack Body.Label)
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k; cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; cases k <;> rfl
    · intro k hk
      cases k with
      | inr k => rfl
      | inl k =>
        cases k with
        | word => rfl
        | scratch => rfl
        | next => rfl
        | history => exact False.elim (hk .history rfl)
        | output => rfl

/-- The literal real binary Increment computes overflow and wrapped data once;
neither its value nor its transition count is supplied as an answer. -/
theorem increment_call (word history output tally todo : List Bool) :
    ∃ m≤5*(2*word.length+3)+1,
      Runs program m (.inl .incrementCall) (data word [] [] history output tally todo [] [])
        (.inl .popOverflow) (data [] [] (SemiprimeD1StackIncrement.overflow word::SemiprimeD1StackIncrement.wrapped word)
          history output tally todo [] []) := by
  obtain ⟨m,hm,hr⟩:=SemiprimeD1StackIncrementBytecode.increment_run word []
  refine ⟨m+1,by omega,?_⟩
  apply included_call program incrementStack incrementLabel incrementStack_injective Inc.code Inc.entry (fun _=>rfl)
    (.inl .incrementCall) (.inl .popOverflow) rfl m
    (⟨some Inc.entry,none,SemiprimeD1TensorTapeFieldMachine.contents word [] []⟩:
      SemiprimeD1StackBytecode.State SemiprimeD1TensorTapeFieldMachine.Stack Inc.Label)
    (⟨none,none,SemiprimeD1TensorTapeFieldMachine.contents [] []
      (SemiprimeD1StackIncrement.overflow word::SemiprimeD1StackIncrement.wrapped word)⟩:
      SemiprimeD1StackBytecode.State SemiprimeD1TensorTapeFieldMachine.Stack Inc.Label)
  · rfl
  · rfl
  · simpa only [List.append_nil] using hr
  · constructor
    · intro k; cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; cases k <;> rfl
    · intro k hk
      cases k with
      | inr k => rfl
      | inl k =>
        cases k with
        | word => exact False.elim (hk .input rfl)
        | scratch => rfl
        | next => exact False.elim (hk .output rfl)
        | history => rfl
        | output => rfl

/-- One final real reversal consumes the entire log and writes exact original
order, preserving every cached tally and preexisting output tail. -/
theorem reverse_call (history output tally : List Bool) :
    Runs program (2*history.length+3) (.inl .reverse) (data [] [] [] history output tally [] [] [])
      (.inl .done) (data [] [] [] [] (history.reverse++output) tally [] [] []) := by
  apply included_call program reverseStack reverseLabel reverseStack_injective SemiprimeD1StackReverseWord.code 0
    (fun _=>rfl) (.inl .reverse) (.inl .done) rfl (2*history.length+2)
    (SemiprimeD1StackReverseWord.state none history output)
    (SemiprimeD1StackReverseWord.done (history.reverse++output))
  · rfl
  · rfl
  · exact SemiprimeD1StackReverseWord.reverse_run history output none
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; fin_cases k <;> rfl
    · intro k hk
      cases k with
      | inr k => rfl
      | inl k =>
        cases k with
        | word => rfl
        | scratch => rfl
        | next => rfl
        | history => exact False.elim (hk 0 rfl)
        | output => exact False.elim (hk 1 rfl)

end RiemannGaussian.SemiprimeD1StackOrdinalBankCalls
