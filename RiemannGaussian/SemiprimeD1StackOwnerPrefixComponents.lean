/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerPrefix
/-! # Literal parser/copy/binary-equality calls in the owner-prefix source -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1StackOwnerPrefixComponents
open SemiprimeD1StackOwnerPrefix SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)

/-- Real framed-key parse pays every tag, key bit, restoration and validity bit. -/
theorem field_call (low high : Bool) (query key tail : List Bool) :
    Runs program (8*key.length+7) (.parse low high)
      (data query (frame key tail) [] [] [] [] []) (.parsed low high)
      (data query tail key [] [] [true] []) := by
  apply included_call program fieldStack (Label.field low high) field_injective F.code
    (F.active .tagPop (none,false)) (fun _=>rfl) (.parse low high) (.parsed low high) rfl
    (8*key.length+6) (SemiprimeD1TensorTapeFieldBytecode.initial (frame key tail) [])
    (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] key) (fun _=>[true])⟩:
      SemiprimeD1StackBytecode.State F.Stack F.Label)
  · rfl
  · rfl
  · exact SemiprimeD1TensorTapeFieldBytecode.framed_run key tail []
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k hk;rfl
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · cases k <;> first | rfl | exact (hk (.inl .output) rfl).elim
      · cases k <;> first | rfl | exact (hk (.inl .input) rfl).elim | exact (hk (.inr ()) rfl).elim

/-- Actual preserving query copy: no equality operand is supplied by a getter. -/
theorem copy_call (low high : Bool) (query reader key : List Bool) :
    Runs program (5*query.length+4) (.copyKey low high) (data query reader key [] [] [] [])
      (.compare low high) (data query reader key query [] [] []) := by
  apply included_call program copyStack (Label.copy low high) copy_injective SemiprimeD1StackCopy.code 0
    (fun _=>rfl) (.copyKey low high) (.compare low high) rfl (5*query.length+3)
    (SemiprimeD1StackCopy.state 0 none query [] []) (SemiprimeD1StackCopy.done query query)
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words query [] none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · cases k <;> first | rfl | exact (hk 1 rfl).elim
      · cases k <;> rfl

/-- Literal binary numeric equality physically consumes both actual key words.
Padding differences remain valid; original wire identity is proved separately. -/
theorem equal_call (low high : Bool) (query reader key : List Bool) :
    Runs program (SemiprimeD1StackWordEqualExecution.executionTime key query+1) (.compare low high)
      (data query reader key query [] [] []) (.matched low high)
      (data query reader [] [] [decide (SemiprimeBitArithmetic.bitValue key=SemiprimeBitArithmetic.bitValue query)] [] []) := by
  apply included_call program Sum.inl (Label.equal low high) Sum.inl_injective E.code .loop
    (fun _=>rfl) (.compare low high) (.matched low high) rfl _
    (SemiprimeD1StackWordEqual.state (some .loop) none key query [])
    (SemiprimeD1StackWordEqual.state none none [] []
      [decide (SemiprimeBitArithmetic.bitValue key=SemiprimeBitArithmetic.bitValue query)])
  · rfl
  · rfl
  · exact SemiprimeD1StackWordEqualExecution.source_run key query none
  · constructor
    · intro k;rfl
    · intro k hk;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackOwnerPrefixComponents
