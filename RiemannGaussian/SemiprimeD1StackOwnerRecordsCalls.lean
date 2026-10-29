/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerRecordsView
import RiemannGaussian.SemiprimeD1StackProcedureInclusion
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerRecordsCalls
open SemiprimeD1StackOwnerRecords SemiprimeD1StackOwnerRecordsView
open SemiprimeD1StackProcedureTrace (Runs included_call)
open SemiprimeD1StackPortOwnerRecipeCalls (update_rel)
open SemiprimeSourceHistogramKeyBits (frame)
namespace Rel
export SemiprimeD1StackMultiplierLink (DataRel)
end Rel
theorem copy_injective :∀part:Bool,Function.Injective (copyStack part):=by decide
theorem copy_call (part:Bool) (store:Stack→List Bool) (pc next:Label)
    (hc:program pc=.call (.copy part 0) next) (hs:store (aux .copyScratch)=[]) :
    Runs program (5*(store (copyStack part 0)).length+4) pc store next
      (Function.update store (copyStack part 1) (store (copyStack part 0)++store (copyStack part 1))) := by
  let word:=store (copyStack part 0)
  let tail:=store (copyStack part 1)
  let before:=SemiprimeD1StackCopy.state 0 none word tail []
  let after:=SemiprimeD1StackCopy.done word (word++tail)
  have hi:Rel.DataRel (copyStack part) store before.store store:=by
    constructor
    · intro k;fin_cases k <;> simp [before,SemiprimeD1StackCopy.state,SemiprimeD1StackCopy.payload,copyStack,word,tail,hs]
    · intro k _;rfl
  apply included_call program (copyStack part) (Label.copy part) (copy_injective part)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc _ before after
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words word tail none
  · exact hi
  · have he:Function.update before.store (1:Fin 3) (word++tail)=after.store:=by funext k;fin_cases k <;> rfl
    simpa only [he] using update_rel (copyStack part) (copy_injective part) store before.store store hi 1 (word++tail)
theorem field_injective :∀scopes:Bool,Function.Injective (fieldStack scopes):=by decide
/-- Physically parse the actual next M-bank payload directly into the real owner filter query. -/
theorem field_call (scopes:Bool) (store:Stack→List Bool) (word tail:List Bool)
    (hi:store (aux .reader)=frame word tail) (ho:store ((if scopes then bank else key))=[])
    (hs:store (aux .fieldScratch)=[]) (hv:store (aux .valid)=[]) :
    Runs program (8*word.length+7) (.local (.field scopes)) store (.local (.valid scopes))
      (Function.update (Function.update (Function.update store (aux .reader) tail)
        ((if scopes then bank else key)) word) (aux .valid) [true]) := by
  let before:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let after:SemiprimeD1StackBytecode.State F.Stack F.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:Rel.DataRel (fieldStack scopes) store before.store store:=by
    constructor
    · intro k;rcases k with k|k
      · cases k <;> simp [fieldStack,before,SemiprimeD1TensorTapeFieldBytecode.initial,
          SemiprimeD1TensorTapeFieldMachine.contents,hi,ho,hs]
      · cases k;exact hv
    · intro k _;rfl
  apply included_call program (fieldStack scopes) (Label.field scopes) (field_injective scopes) F.code
    (F.active .tagPop (none,false)) (fun _=>rfl) (.local (.field scopes)) (.local (.valid scopes))
    rfl (8*word.length+6) before after
  · rfl
  · rfl
  · exact SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []
  · exact hin
  · have h0:=update_rel (fieldStack scopes) (field_injective scopes) store before.store store hin (.inl .input) tail
    have h1:=update_rel (fieldStack scopes) (field_injective scopes) store _ _ h0 (.inl .output) word
    have h2:=update_rel (fieldStack scopes) (field_injective scopes) store _ _ h1 (.inr ()) [true]
    have he:Function.update (Function.update (Function.update before.store (.inl .input) tail)
        (.inl .output) word) (.inr ()) [true]=after.store:=by
      funext k;rcases k with k|k <;> cases k <;> rfl
    simpa only [he,fieldStack] using h2

end RiemannGaussian.SemiprimeD1StackOwnerRecordsCalls
