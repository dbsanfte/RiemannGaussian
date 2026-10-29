/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueCalls
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueEmit
open SemiprimeD1StackOwnerFibreCatalogue SemiprimeD1StackOwnerFibreCatalogueSource
open SemiprimeD1StackOwnerFibreCatalogueView
open SemiprimeD1StackProcedureTrace (Runs included_call runs_trans one_base)
open SemiprimeD1StackPortOwnerRecipeCalls (update_rel)
open SemiprimeSourceHistogramKeyBits (frame)
namespace Rel
export SemiprimeD1StackMultiplierLink (DataRel)
end Rel
/-- Actual owner/scope frame operands are distinct for both static emission sites. -/
theorem emit_injective : ∀scope:Bool,Function.Injective (frameStack scope) := by decide
/-- All actual field/final reversals use two distinct physical roles. -/
theorem reverse_injective : ∀finish:Bool,Function.Injective (reverseStack finish) := by decide
/-- Actual computed original owner ID, then actually filtered complete ordered scope-ID vector. -/
def emitSource (scope:Bool) : Stack :=fibreStack (.inr (if scope then .output else .query))
/-- Static actual caller position after materializing a field. -/
def next (scope:Bool) : Label :=if scope then .local (.clearFibre 0) else .local (.emitField true)
/-- Actual owner/scope framing from physically reached words. -/
theorem frame_call (scope:Bool) (store:Stack→List Bool) (hs:store (aux .frameScratch)=[]) :
    Runs program (6*(store (emitSource scope)).length+5) (.local (.emitField scope)) store
      (.local (.emitReverse scope)) (Function.update store (aux .frameBuffer)
        (frame (store (emitSource scope)) (store (aux .frameBuffer)))) := by
  let word:=store (emitSource scope)
  let tail:=store (aux .frameBuffer)
  let before:=SemiprimeD1StackFrame.state 0 none word tail []
  let after:=SemiprimeD1StackFrame.done word (frame word tail)
  have hi:Rel.DataRel (frameStack scope) store before.store store:=by
    constructor
    · intro k;fin_cases k <;> simp [before,SemiprimeD1StackFrame.state,SemiprimeD1StackFrame.payload,frameStack,emitSource,word,tail,hs]
    · intro k _;rfl
  apply included_call program (frameStack scope) (Label.frame scope) (emit_injective scope)
    SemiprimeD1StackFrame.code 0 (fun _=>rfl) (.local (.emitField scope)) (.local (.emitReverse scope)) rfl _ before after
  · rfl
  · rfl
  · exact SemiprimeD1StackFrame.frame_words word tail none
  · exact hi
  · have he:Function.update before.store (1:Fin 3) (frame word tail)=after.store:=by
      funext k;fin_cases k <;> rfl
    simpa only [he,frameStack,show ¬(1:Fin 3)=0 by decide,ite_false,ite_true] using
      update_rel (frameStack scope) (emit_injective scope) store before.store store hi 1 (frame word tail)
/-- Actual reverse transfers every newly framed owner/scope bit to the retained collector. -/
theorem reverse_call (scope:Bool) (store:Stack→List Bool) :
    Runs program (2*(store (aux .frameBuffer)).length+3) (.local (.emitReverse scope)) store (next scope)
      (Function.update (Function.update store (aux .frameBuffer) []) (aux .reversed)
        ((store (aux .frameBuffer)).reverse++store (aux .reversed))) := by
  let word:=store (aux .frameBuffer)
  let tail:=store (aux .reversed)
  let before:=SemiprimeD1StackReverseWord.state none word tail
  let after:=SemiprimeD1StackReverseWord.done (word.reverse++tail)
  have hi:Rel.DataRel (reverseStack false) store before.store store:=⟨fun k=>by fin_cases k <;> rfl,fun _ _=>rfl⟩
  apply included_call program (reverseStack false) (Label.reverse false) (reverse_injective false)
    SemiprimeD1StackReverseWord.code 0 (fun _=>rfl) (.local (.emitReverse scope)) (next scope) rfl _ before after
  · rfl
  · rfl
  · exact SemiprimeD1StackReverseWord.reverse_run word tail none
  · exact hi
  · have h0:=update_rel (reverseStack false) (reverse_injective false) store before.store store hi 0 []
    have h1:=update_rel (reverseStack false) (reverse_injective false) store _ _ h0 1 (word.reverse++tail)
    have he:Function.update (Function.update before.store (0:Fin 2) []) 1 (word.reverse++tail)=after.store:=by
      funext k;fin_cases k <;> rfl
    simpa [he,reverseStack,word,tail] using h1
/-- Actual frame+reverse pair clears its actual buffer and pays all copied owner/scope bytes. -/
theorem field_run (s:R.Stack→List Bool) (f:V.Stack→List Bool) (a:Aux→List Bool) (scope:Bool) (hb:a .frameBuffer=[]) (hs:a .frameScratch=[]) :
    Runs program (10*(data s f a (emitSource scope)).length+10) (.local (.emitField scope))
      (data s f a) (next scope) (data s f (Function.update a .reversed
        ((frame (data s f a (emitSource scope)) []).reverse++a .reversed))) := by
  let word:=data s f a (emitSource scope)
  let a':=Function.update a .frameBuffer (frame word [])
  have hf:=frame_call scope (data s f a) hs
  have he:Function.update (data s f a) (aux .frameBuffer)
      (frame (data s f a (emitSource scope)) (data s f a (aux .frameBuffer)))=data s f a':=by
    simp only [data_aux,hb,update_aux,a',word]
  rw [he] at hf
  have hr:=reverse_call scope (data s f a')
  have hbuf:data s f a' (aux .frameBuffer)=frame word []:=by
    change a' .frameBuffer=_;exact Function.update_same _ _ _
  have hcol:data s f a' (aux .reversed)=a .reversed:=by
    change a' .reversed=_;exact Function.update_of_ne (by decide : Aux.reversed≠.frameBuffer) _ _
  rw [hbuf,hcol] at hr
  have hout:Function.update (Function.update (data s f a') (aux .frameBuffer) []) (aux .reversed)
      ((frame word []).reverse++a .reversed)=data s f (Function.update a .reversed ((frame word []).reverse++a .reversed)):=by
    simp only [a',update_aux,Function.update_idem]
    rw [←hb,Function.update_eq_self]
  rw [hout] at hr
  have h:=runs_trans program _ _ _ _ _ _ _ _ hf hr
  simpa only [SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil,word,show
    (6*(data s f a (emitSource scope)).length+5)+(2*(2*(data s f a (emitSource scope)).length+0+1)+3)=
    10*(data s f a (emitSource scope)).length+10 by omega] using h
/-- Exact owner/fibre row in the standard two-field catalogue grammar. -/
def row (owner scope:List Bool) : List Bool :=true::frame owner (frame scope [])
/-- Full physical owner/scope row emission with actual tag, both field copies and both transfers. -/
theorem row_run (s:R.Stack→List Bool) (f:V.Stack→List Bool) (a:Aux→List Bool) (hb:a .frameBuffer=[]) (hs:a .frameScratch=[]) :
    Runs program (10*(f (.inr .query)).length+10*(f (.inr .output)).length+21) (.local .emitTag) (data s f a)
      (.local (.clearFibre 0)) (data s f (Function.update a .reversed
        ((row (f (.inr .query)) (f (.inr .output))).reverse++a .reversed))) := by
  let owner:=f (.inr .query)
  let a0:=Function.update a .reversed (true::a .reversed)
  let a1:=Function.update a0 .reversed ((frame owner []).reverse++a0 .reversed)
  have hpush:Runs program 1 (.local .emitTag) (data s f a) (.local (.emitField false)) (data s f a0):=by
    apply one_base program _ _ (.push (aux .reversed) true (.local (.emitField false))) _ _ rfl rfl
    exact update_aux _ _ _ _ _
  have ho:=field_run s f a0 false
    (by simpa only [a0,Function.update_of_ne (by decide : Aux.frameBuffer≠.reversed)] using hb)
    (by simpa only [a0,Function.update_of_ne (by decide : Aux.frameScratch≠.reversed)] using hs)
  change Runs program (10*owner.length+10) (.local (.emitField false)) (data s f a0)
    (.local (.emitField true)) (data s f a1) at ho
  have hi:=field_run s f a1 true
    (by simpa only [a1,a0,Function.update_of_ne (by decide : Aux.frameBuffer≠.reversed)] using hb)
    (by simpa only [a1,a0,Function.update_of_ne (by decide : Aux.frameScratch≠.reversed)] using hs)
  change Runs program (10*(f (.inr .output)).length+10) (.local (.emitField true)) (data s f a1)
    (.local (.clearFibre 0)) (data s f (Function.update a1 .reversed ((frame (f (.inr .output)) []).reverse++a1 .reversed))) at hi
  have hout:Function.update a1 .reversed ((frame (f (.inr .output)) []).reverse++a1 .reversed)=
      Function.update a .reversed ((row owner (f (.inr .output))).reverse++a .reversed):=by
    simp only [a1,a0,Function.update_same,Function.update_idem,row,←List.append_assoc]
    rw [show frame owner (frame (f (.inr .output)) [])=frame owner []++frame (f (.inr .output)) [] by
      rw [SemiprimeD1StackOwnerEqualityKey.frame_append];rfl]
    simp only [List.reverse_cons,List.reverse_append,List.append_assoc,List.singleton_append]
  rw [hout] at hi
  have h:=runs_trans program _ _ _ _ _ _ _ _ hpush (runs_trans program _ _ _ _ _ _ _ _ ho hi)
  simpa only [owner,show 1+(10*(f (.inr .query)).length+10+(10*(f (.inr .output)).length+10))=
    10*(f (.inr .query)).length+10*(f (.inr .output)).length+21 by omega] using h
end RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueEmit
