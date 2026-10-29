/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRoutingLookup
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRoutingEmit
open SemiprimeD1StackPortOwnerRouting SemiprimeD1StackPortOwnerRoutingAcquisition
open SemiprimeD1StackPortOwnerRoutingView
open SemiprimeD1StackProcedureTrace (Runs included_call runs_trans one_base)
open SemiprimeD1StackPortOwnerRecipeCalls (update_rel)
open SemiprimeSourceHistogramKeyBits (frame)
namespace Rel
export SemiprimeD1StackMultiplierLink (DataRel)
end Rel
/-- Actual owner/scope frame operands are distinct for both static emission sites. -/
theorem emit_injective : ∀scope:Bool,Function.Injective (emitStack scope) := by decide
/-- All actual field/final reversals use two distinct physical roles. -/
theorem reverse_injective : ∀finish:Bool,Function.Injective (reverseStack finish) := by decide
/-- Actual computed original owner ID, then unchanged actual occurrence scope ID. -/
def emitSource (scope:Bool) : Stack :=if scope then cache 0 else lookupStack (.inr .output)
/-- Static actual caller position after materializing a field. -/
def next (scope:Bool) : Label :=if scope then .local (.clearLookup 0) else .local (.emitField true)
/-- Actual owner/scope framing from physically reached words. -/
theorem frame_call (scope:Bool) (store:Stack→List Bool) (hs:store (aux .frameScratch)=[]) :
    Runs program (6*(store (emitSource scope)).length+5) (.local (.emitField scope)) store
      (.local (.emitReverse scope)) (Function.update store (aux .frameBuffer)
        (frame (store (emitSource scope)) (store (aux .frameBuffer)))) := by
  let word:=store (emitSource scope)
  let tail:=store (aux .frameBuffer)
  let before:=SemiprimeD1StackFrame.state 0 none word tail []
  let after:=SemiprimeD1StackFrame.done word (frame word tail)
  have hi:Rel.DataRel (emitStack scope) store before.store store:=by
    constructor
    · intro k;fin_cases k <;> simp [before,SemiprimeD1StackFrame.state,SemiprimeD1StackFrame.payload,emitStack,emitSource,word,tail,hs]
    · intro k _;rfl
  apply included_call program (emitStack scope) (Label.emit scope) (emit_injective scope)
    SemiprimeD1StackFrame.code 0 (fun _=>rfl) (.local (.emitField scope)) (.local (.emitReverse scope)) rfl _ before after
  · rfl
  · rfl
  · exact SemiprimeD1StackFrame.frame_words word tail none
  · exact hi
  · have he:Function.update before.store (1:Fin 3) (frame word tail)=after.store:=by
      funext k;fin_cases k <;> rfl
    simpa only [he,emitStack,show ¬(1:Fin 3)=0 by decide,ite_false,ite_true] using
      update_rel (emitStack scope) (emit_injective scope) store before.store store hi 1 (frame word tail)
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
theorem field_run (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (l:Lookup.Stack→List Bool)
    (w:Fin 9→List Bool) (a:Aux→List Bool) (scope:Bool) (hb:a .frameBuffer=[]) (hs:a .frameScratch=[]) :
    Runs program (10*(data m s l w a (emitSource scope)).length+10) (.local (.emitField scope))
      (data m s l w a) (next scope) (data m s l w (Function.update a .reversed
        ((frame (data m s l w a (emitSource scope)) []).reverse++a .reversed))) := by
  let word:=data m s l w a (emitSource scope)
  let a':=Function.update a .frameBuffer (frame word [])
  have hf:=frame_call scope (data m s l w a) hs
  have he:Function.update (data m s l w a) (aux .frameBuffer)
      (frame (data m s l w a (emitSource scope)) (data m s l w a (aux .frameBuffer)))=data m s l w a':=by
    simp only [data_aux,hb,update_aux,a',word]
  rw [he] at hf
  have hr:=reverse_call scope (data m s l w a')
  have hbuf:data m s l w a' (aux .frameBuffer)=frame word []:=by
    change a' .frameBuffer=_;exact Function.update_same _ _ _
  have hcol:data m s l w a' (aux .reversed)=a .reversed:=by
    change a' .reversed=_;exact Function.update_of_ne (by decide : Aux.reversed≠.frameBuffer) _ _
  rw [hbuf,hcol] at hr
  have hout:Function.update (Function.update (data m s l w a') (aux .frameBuffer) []) (aux .reversed)
      ((frame word []).reverse++a .reversed)=data m s l w (Function.update a .reversed ((frame word []).reverse++a .reversed)):=by
    simp only [a',update_aux,Function.update_idem]
    rw [←hb,Function.update_eq_self]
  rw [hout] at hr
  have h:=runs_trans program _ _ _ _ _ _ _ _ hf hr
  simpa only [SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil,word,show
    (6*(data m s l w a (emitSource scope)).length+5)+(2*(2*(data m s l w a (emitSource scope)).length+0+1)+3)=
    10*(data m s l w a (emitSource scope)).length+10 by omega] using h
/-- Exact routed owner/scope row in the already-verified fibre parser grammar. -/
def row (owner scope:List Bool) : List Bool :=true::frame owner (frame scope [])
/-- Full physical owner/scope row emission with actual tag, both field copies and both transfers. -/
theorem row_run (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (l:Lookup.Stack→List Bool)
    (w:Fin 9→List Bool) (a:Aux→List Bool) (hb:a .frameBuffer=[]) (hs:a .frameScratch=[]) :
    Runs program (10*(l (.inr .output)).length+10*(w 0).length+21) (.local .emitTag) (data m s l w a)
      (.local (.clearLookup 0)) (data m s l w (Function.update a .reversed
        ((row (l (.inr .output)) (w 0)).reverse++a .reversed))) := by
  let owner:=l (.inr .output)
  let a0:=Function.update a .reversed (true::a .reversed)
  let a1:=Function.update a0 .reversed ((frame owner []).reverse++a0 .reversed)
  have hpush:Runs program 1 (.local .emitTag) (data m s l w a) (.local (.emitField false)) (data m s l w a0):=by
    apply one_base program _ _ (.push (aux .reversed) true (.local (.emitField false))) _ _ rfl rfl
    exact update_aux _ _ _ _ _ _ _
  have ho:=field_run m s l w a0 false
    (by simpa only [a0,Function.update_of_ne (by decide : Aux.frameBuffer≠.reversed)] using hb)
    (by simpa only [a0,Function.update_of_ne (by decide : Aux.frameScratch≠.reversed)] using hs)
  change Runs program (10*owner.length+10) (.local (.emitField false)) (data m s l w a0)
    (.local (.emitField true)) (data m s l w a1) at ho
  have hi:=field_run m s l w a1 true
    (by simpa only [a1,a0,Function.update_of_ne (by decide : Aux.frameBuffer≠.reversed)] using hb)
    (by simpa only [a1,a0,Function.update_of_ne (by decide : Aux.frameScratch≠.reversed)] using hs)
  change Runs program (10*(w 0).length+10) (.local (.emitField true)) (data m s l w a1)
    (.local (.clearLookup 0)) (data m s l w (Function.update a1 .reversed ((frame (w 0) []).reverse++a1 .reversed))) at hi
  have hout:Function.update a1 .reversed ((frame (w 0) []).reverse++a1 .reversed)=
      Function.update a .reversed ((row owner (w 0)).reverse++a .reversed):=by
    simp only [a1,a0,Function.update_same,Function.update_idem,row,←List.append_assoc]
    rw [show frame owner (frame (w 0) [])=frame owner []++frame (w 0) [] by
      rw [SemiprimeD1StackOwnerEqualityKey.frame_append];rfl]
    simp only [List.reverse_cons,List.reverse_append,List.append_assoc,List.singleton_append]
  rw [hout] at hi
  have h:=runs_trans program _ _ _ _ _ _ _ _ hpush (runs_trans program _ _ _ _ _ _ _ _ ho hi)
  simpa only [owner,show 1+(10*(l (.inr .output)).length+10+(10*(w 0).length+10))=
    10*(l (.inr .output)).length+10*(w 0).length+21 by omega] using h
end RiemannGaussian.SemiprimeD1StackPortOwnerRoutingEmit
