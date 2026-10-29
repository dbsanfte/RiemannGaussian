/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordView
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Actual field, preserving tag-copy and complete Boolean-record calls -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordPrimitives
open SemiprimeD1StackBooleanDescriptorRecord SemiprimeD1StackBooleanDescriptorRecordView
open SemiprimeD1StackProcedureFragments (Runs included_call)
open SemiprimeSourceHistogramKeyBits (frame)
/-- Actual framed-field call, retaining all unrelated physical bytes. -/
theorem field_call (part : Fin 5) (d : Stack→List Bool) (word tail : List Bool)
    (hr:d (aux .reader)=frame word tail) (hc:d (cache part)=[])
    (hs:d (aux .fieldScratch)=[]) (hv:d (aux .valid)=[]) :
    Runs program (8*word.length+7) (.local (.field part)) d (.local (.valid part))
      (Function.update (Function.update (Function.update d (aux .reader) tail) (cache part) word) (aux .valid) [true]) := by
  apply included_call program (fieldStack part) (Label.field part) (field_injective part) F.code
    (F.active .tagPop (none,false)) (fun _=>rfl) (.local (.field part)) (.local (.valid part)) rfl
    (8*word.length+6) (SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) [])
    (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩:
      SemiprimeD1StackBytecode.State F.Stack F.Label)
  · rfl
  · rfl
  · exact SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []
  · constructor
    · intro k
      cases k with
      | inl k=>cases k with
        | input=>exact hr
        | scratch=>exact hs
        | output=>exact hc
      | inr k=>cases k;exact hv
    · intro k _;rfl
  · constructor
    · intro k
      cases k with
      | inl k=>cases k with
        | input=>
          change Function.update (Function.update (Function.update d (aux .reader) tail)
            (cache part) word) (aux .valid) [true] (aux .reader)=tail
          rw [Function.update_of_ne (by decide : aux .reader≠aux .valid),
            Function.update_of_ne (by simp [aux,cache] : aux .reader≠cache part),Function.update_self]
        | scratch=>
          change Function.update (Function.update (Function.update d (aux .reader) tail)
            (cache part) word) (aux .valid) [true] (aux .fieldScratch)=[]
          rw [Function.update_of_ne (by decide : aux .fieldScratch≠aux .valid),
            Function.update_of_ne (by simp [aux,cache] : aux .fieldScratch≠cache part),
            Function.update_of_ne (by decide : aux .fieldScratch≠aux .reader),hs]
        | output=>
          change Function.update (Function.update (Function.update d (aux .reader) tail)
            (cache part) word) (aux .valid) [true] (cache part)=word
          rw [Function.update_of_ne (by simp [aux,cache] : cache part≠aux .valid),Function.update_self]
      | inr k=>cases k;exact Function.update_self _ _ _
    · intro k hk
      have h0:k≠aux .reader:=by intro he;exact hk (.inl .input) he.symm
      have h1:k≠cache part:=by intro he;exact hk (.inl .output) he.symm
      have h2:k≠aux .valid:=by intro he;exact hk (.inr ()) he.symm
      simp only [Function.update_of_ne h0,Function.update_of_ne h1,Function.update_of_ne h2]
/-- The copied physical constructor tag is preserved in cache0 and consumed separately. -/
theorem copy_tag (base : R.Stack→List Bool) (words : Fin 5→List Bool) (reader : List Bool) :
    Runs program (5*(words 0).length+4) (.local .copyTag) (clean base words reader)
      (.local (.decode 0)) (data base words reader [] (words 0)) := by
  apply included_call program copyStack Label.copy copy_injective SemiprimeD1StackCopy.code 0
    (fun _=>rfl) (.local .copyTag) (.local (.decode 0)) rfl (5*(words 0).length+3)
    (SemiprimeD1StackCopy.state 0 none (words 0) [] [])
    (SemiprimeD1StackCopy.done (words 0) (words 0++[]))
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words (words 0) [] none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k
      fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.done,SemiprimeD1StackCopy.payload] <;> rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · cases k with
          | reader | fieldScratch | valid | copyScratch=>rfl
          | tagReader=>exact (hk 1 rfl).elim
/-- A real nested call executes the entire paid table, scope conversion and logger program. -/
theorem record_call (mode : SemiprimeD1StackBooleanEntry.Mode) (scope : List (List Bool))
    (hist out reader : List Bool) (words : Fin 5→List Bool) :
    ∃t ≤ SemiprimeD1StackBooleanRecordExecution.timeBound mode scope,
      Runs program (t+1) (.local (.record mode))
        (clean (recordInput (SemiprimeD1TensorTapeCodec.vectorBits scope) hist out) words reader)
        (.local .done) (clean (R.done mode scope hist out).data words reader) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackBooleanRecordExecution.source_run mode scope hist out
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Sum.inl Label.record Sum.inl_injective
    R.program (.inl (.start mode)) (fun _=>rfl) (.local (.record mode)) (.local .done) rfl t
    (R.initial mode (SemiprimeD1TensorTapeCodec.vectorBits scope) hist out) (R.done mode scope hist out)
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rcases k with k|k
        · rfl
        · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordPrimitives
