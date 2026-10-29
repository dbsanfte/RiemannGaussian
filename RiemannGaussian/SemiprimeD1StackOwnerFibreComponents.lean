/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerFibre
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1StackOwnerFibreComponents
open SemiprimeD1StackOwnerFibre SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Real key parser, including framing/scratch restoration and validity byte. -/
theorem key_call (query key tail raw:List Bool) :
    Runs program (8*key.length+7) .parseKey
      (data query (frame key tail) [] [] [] [] [] raw [] []) .parsedKey
      (data query tail key [] [] [true] [] raw [] []) := by
  apply included_call program (fieldStack none) (Label.field none) (field_injective none) F.code
    (F.active .tagPop (none,false)) (fun _=>rfl) .parseKey .parsedKey rfl
    (8*key.length+6) (SemiprimeD1TensorTapeFieldBytecode.initial (frame key tail) [])
    (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] key) (fun _=>[true])⟩:
      SemiprimeD1StackBytecode.State F.Stack F.Label)
  · rfl
  · rfl
  · exact SemiprimeD1TensorTapeFieldBytecode.framed_run key tail []
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · cases k <;> first | rfl | exact (hk (.inl .output) rfl).elim
      · cases k <;> first | rfl | exact (hk (.inl .input) rfl).elim | exact (hk (.inr ()) rfl).elim
/-- The actual scope-ID word is physically parsed, on both comparison branches. -/
theorem value_call (same:Bool) (query value tail raw:List Bool) :
    Runs program (8*value.length+7) (.parseValue same)
      (data query (frame value tail) [] [] [] [] [] raw [] []) (.parsedValue same)
      (data query tail [] [] [] [true] value raw [] []) := by
  apply included_call program (fieldStack (some same)) (Label.field (some same))
    (field_injective (some same)) F.code (F.active .tagPop (none,false)) (fun _=>rfl)
    (.parseValue same) (.parsedValue same) rfl (8*value.length+6)
    (SemiprimeD1TensorTapeFieldBytecode.initial (frame value tail) [])
    (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] value) (fun _=>[true])⟩:
      SemiprimeD1StackBytecode.State F.Stack F.Label)
  · rfl
  · rfl
  · exact SemiprimeD1TensorTapeFieldBytecode.framed_run value tail []
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> cases same <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;rcases k with k|k <;> cases k <;> cases same <;> rfl
    · intro k hk
      rcases k with k|k
      · cases k <;> rfl
      · cases k <;> cases same <;> first | rfl | exact (hk (.inl .input) rfl).elim | exact (hk (.inl .output) rfl).elim | exact (hk (.inr ()) rfl).elim
/-- Every comparison receives an actual preserving copy of the acquired query. -/
theorem copy_call (query reader key raw:List Bool) :
    Runs program (5*query.length+4) .copyKey (data query reader key [] [] [] [] raw [] [])
      .compare (data query reader key query [] [] [] raw [] []) := by
  apply included_call program copyStack Label.copy copy_injective SemiprimeD1StackCopy.code 0
    (fun _=>rfl) .copyKey .compare rfl (5*query.length+3)
    (SemiprimeD1StackCopy.state 0 none query [] []) (SemiprimeD1StackCopy.done query query)
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words query [] none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · cases k <;> first | rfl | exact (hk 1 rfl).elim
      · cases k <;> rfl
/-- The owner-fibre filter executes the actual numeric WordEqual bytecode. -/
theorem equal_call (query reader key raw:List Bool) :
    Runs program (SemiprimeD1StackWordEqualExecution.executionTime key query+1) .compare
      (data query reader key query [] [] [] raw [] []) .matched
      (data query reader [] [] [decide (SemiprimeBitArithmetic.bitValue key=SemiprimeBitArithmetic.bitValue query)] [] [] raw [] []) := by
  apply included_call program Sum.inl Label.equal Sum.inl_injective E.code .loop
    (fun _=>rfl) .compare .matched rfl _
    (SemiprimeD1StackWordEqual.state (some .loop) none key query [])
    (SemiprimeD1StackWordEqual.state none none [] []
      [decide (SemiprimeBitArithmetic.bitValue key=SemiprimeBitArithmetic.bitValue query)])
  · rfl
  · rfl
  · exact SemiprimeD1StackWordEqualExecution.source_run key query none
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackOwnerFibreComponents
