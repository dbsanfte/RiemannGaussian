/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRoutingView
import RiemannGaussian.SemiprimeD1PortOwnerRoutingSpec
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRoutingKey
open SemiprimeD1StackPortOwnerRouting SemiprimeD1StackPortOwnerRoutingAcquisition
open SemiprimeD1StackPortOwnerRoutingView
open SemiprimeD1StackProcedureTrace (Runs included_call runs_trans one_base)
open SemiprimeD1StackPortOwnerRecipeCalls (update_rel)
open SemiprimeSourceHistogramKeyBits (frame)
namespace Rel
export SemiprimeD1StackMultiplierLink (DataRel)
end Rel
/-- Every key field copy uses an actual parsed field, actual query output and distinct scratch. -/
theorem key_injective (part:Fin 6) : Function.Injective (keyStack part) := by fin_cases part <;> decide
/-- Static actual continuation after one real query-field frame. -/
def next (part:Fin 6) : Label :=
  if h:part.val<5 then .local (.key ⟨part.val+1,by omega⟩) else .local .copyMap
/-- One real Frame call prepends an actually parsed slot/descriptor word to the actual query. -/
theorem key_call (part:Fin 6) (store:Stack→List Bool) (hs:store (aux .frameScratch)=[]) :
    Runs program (6*(store (cache ⟨8-part.val,by omega⟩)).length+5) (.local (.key part)) store (next part)
      (Function.update store (lookupStack (.inr .query))
        (frame (store (cache ⟨8-part.val,by omega⟩)) (store (lookupStack (.inr .query))))) := by
  let word:=store (cache ⟨8-part.val,by omega⟩)
  let tail:=store (lookupStack (.inr .query))
  let before:=SemiprimeD1StackFrame.state 0 none word tail []
  let after:=SemiprimeD1StackFrame.done word (frame word tail)
  have hi:Rel.DataRel (keyStack part) store before.store store:=by
    constructor
    · intro k;fin_cases k <;> simp [before,SemiprimeD1StackFrame.state,SemiprimeD1StackFrame.payload,keyStack,word,tail,hs]
    · intro k _;rfl
  apply included_call program (keyStack part) (Label.key part) (key_injective part)
    SemiprimeD1StackFrame.code 0 (fun _=>rfl) (.local (.key part)) (next part) rfl _ before after
  · rfl
  · rfl
  · exact SemiprimeD1StackFrame.frame_words word tail none
  · exact hi
  · have he:Function.update before.store (1:Fin 3) (frame word tail)=after.store:=by
      funext k;fin_cases k <;> rfl
    simpa only [he,keyStack,show ¬(1:Fin 3)=0 by decide,ite_false,ite_true] using
      update_rel (keyStack part) (key_injective part) store before.store store hi 1 (frame word tail)
/-- Physically accumulated query suffix, with the actual sentinel pushed before any frame. -/
def suffix (w:Fin 9→List Bool) (n:Nat) : List Bool :=
  if n=0 then [true] else if n=1 then frame (w 8) [true]
  else if n=2 then frame (w 7) (frame (w 8) [true])
  else if n=3 then frame (w 6) (frame (w 7) (frame (w 8) [true]))
  else if n=4 then frame (w 5) (frame (w 6) (frame (w 7) (frame (w 8) [true])))
  else if n=5 then frame (w 4) (frame (w 5) (frame (w 6) (frame (w 7) (frame (w 8) [true]))))
  else SemiprimeD1PortOwnerRoutingSpec.query w
/-- Exact real query-store boundary, with all other lookup roles still empty. -/
def store (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (w:Fin 9→List Bool)
    (a:Aux→List Bool) (n:Nat) : Stack→List Bool :=
  data m s (Function.update (fun _=>[]) (.inr .query) (suffix w n)) w a
/-- Each static key frame prepends the next original field; no semantic decoder is executed. -/
theorem suffix_step (w:Fin 9→List Bool) (part:Fin 6) :
    frame (w ⟨8-part.val,by omega⟩) (suffix w part.val)=suffix w (part.val+1) := by
  fin_cases part <;> rfl
/-- Real Frame call at every query construction boundary. -/
theorem field_run (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (w:Fin 9→List Bool)
    (a:Aux→List Bool) (hs:a .frameScratch=[]) (part:Fin 6) :
    Runs program (6*(w ⟨8-part.val,by omega⟩).length+5) (.local (.key part))
      (store m s w a part.val) (next part) (store m s w a (part.val+1)) := by
  have h:=key_call part (store m s w a part.val) hs
  have hw:store m s w a part.val (cache ⟨8-part.val,by omega⟩)=w ⟨8-part.val,by omega⟩:=rfl
  have ho:store m s w a part.val (lookupStack (.inr .query))=suffix w part.val:=by
    change (Function.update (fun _:Lookup.Stack=>[]) (.inr .query:Lookup.Stack) (suffix w part.val)) (.inr .query)=_
    exact Function.update_same _ _ _
  rw [hw,ho,suffix_step] at h
  simpa only [store,update_lookup,Function.update_idem] using h
/-- Actual byte mass of only the six physically framed endpoint matching fields. -/
def mass (w:Fin 9→List Bool) : Nat :=(w 3).length+(w 4).length+(w 5).length+(w 6).length+(w 7).length+(w 8).length
/-- All six actual field frames build the compact endpoint key exactly. -/
theorem fields_run (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (w:Fin 9→List Bool)
    (a:Aux→List Bool) (hs:a .frameScratch=[]) :
    Runs program (6*mass w+30) (.local (.key 0)) (store m s w a 0)
      (.local .copyMap) (store m s w a 6) := by
  have h:=runs_trans program _ _ _ _ _ _ _ _ (field_run m s w a hs 0)
    (runs_trans program _ _ _ _ _ _ _ _ (field_run m s w a hs 1)
      (runs_trans program _ _ _ _ _ _ _ _ (field_run m s w a hs 2)
        (runs_trans program _ _ _ _ _ _ _ _ (field_run m s w a hs 3)
          (runs_trans program _ _ _ _ _ _ _ _ (field_run m s w a hs 4) (field_run m s w a hs 5)))))
  have ht:(6*(w 8).length+5)+((6*(w 7).length+5)+((6*(w 6).length+5)+
      ((6*(w 5).length+5)+((6*(w 4).length+5)+(6*(w 3).length+5)))))=6*mass w+30:=by unfold mass;omega
  change Runs program ((6*(w 8).length+5)+((6*(w 7).length+5)+((6*(w 6).length+5)+
      ((6*(w 5).length+5)+((6*(w 4).length+5)+(6*(w 3).length+5))))))
    (.local (.key 0)) (store m s w a 0) (.local .copyMap) (store m s w a 6) at h
  rw [ht] at h
  exact h

/-- The sentinel is PHYSICALLY pushed; neither a query word nor its compactness is advised. -/
theorem key_run (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (w:Fin 9→List Bool)
    (a:Aux→List Bool) (hs:a .frameScratch=[]) :
    Runs program (6*mass w+31) (.local .sentinel) (data m s (fun _=>[]) w a)
      (.local .copyMap) (store m s w a 6) := by
  have hpush:Runs program 1 (.local .sentinel) (data m s (fun _=>[]) w a)
      (.local (.key 0)) (store m s w a 0):=by
    apply one_base program _ _ (.push (lookupStack (.inr .query)) true (.local (.key 0))) _ _ rfl rfl
    exact update_lookup _ _ _ _ _ _ _
  have h:=runs_trans program _ _ _ _ _ _ _ _ hpush (fields_run m s w a hs)
  simpa only [show 1+(6*mass w+30)=6*mass w+31 by omega] using h
end RiemannGaussian.SemiprimeD1StackPortOwnerRoutingKey
