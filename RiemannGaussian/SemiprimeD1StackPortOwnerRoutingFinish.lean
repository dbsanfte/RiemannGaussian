/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRoutingEmit
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRoutingFinish
open SemiprimeD1StackPortOwnerRouting SemiprimeD1StackPortOwnerRoutingAcquisition
open SemiprimeD1StackPortOwnerRoutingView
open SemiprimeD1StackPortOwnerRoutingEmit (reverse_injective)
open SemiprimeD1StackPortOwnerRecipeCalls (update_rel)
open SemiprimeD1StackProcedureTrace (Runs runs_trans one_base included_call)
namespace Rel
export SemiprimeD1StackMultiplierLink (DataRel)
end Rel
/-- Complete actual final store, retaining BOTH actual source banks and materialized routed scope tape. -/
def result (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (output:List Bool) : Stack→List Bool :=
  data m s (fun _=>[]) (fun _=>[]) (Function.update (rowAux [] []) .output output)
/-- Real final reversal consumes the actual collector and writes all physical forward output bytes. -/
theorem reverse_final (store:Stack→List Bool) (ho:store (aux .output)=[]) :
    Runs program (2*(store (aux .reversed)).length+3) (.local .finalReverse) store (.local .halt)
      (Function.update (Function.update store (aux .reversed) []) (aux .output) (store (aux .reversed)).reverse) := by
  let word:=store (aux .reversed)
  let before:=SemiprimeD1StackReverseWord.state none word []
  let after:=SemiprimeD1StackReverseWord.done word.reverse
  have hi:Rel.DataRel (reverseStack true) store before.store store:=by
    constructor
    · intro k;fin_cases k
      · rfl
      · exact ho
    · intro k _;rfl
  apply included_call program (reverseStack true) (Label.reverse true) (reverse_injective true)
    SemiprimeD1StackReverseWord.code 0 (fun _=>rfl) (.local .finalReverse) (.local .halt) rfl _ before after
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackReverseWord.reverse_run word [] none
  · exact hi
  · have h0:=update_rel (reverseStack true) (reverse_injective true) store before.store store hi 0 []
    have h1:=update_rel (reverseStack true) (reverse_injective true) store _ _ h0 1 word.reverse
    have he:Function.update (Function.update before.store (0:Fin 2) []) 1 word.reverse=after.store:=by
      funext k;fin_cases k <;> rfl
    simpa [he,reverseStack,word] using h1
/-- Actual whole-reader EOF, literal false-vector terminator push and physical output reversal. -/
theorem finish_run (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (raw:List Bool) :
    Runs program (2*raw.length+7) (.local .parse) (data m s (fun _=>[]) (fun _=>[]) (rowAux [] raw))
      (.local .halt) (result m s (raw.reverse++[false])) := by
  let before:=data m s (fun _=>[]) (fun _=>[]) (rowAux [] raw)
  let tagged:=data m s (fun _=>[]) (fun _=>[]) (Function.update (rowAux [] raw) .reversed (false::raw))
  have hp:Runs program 1 (.local .parse) before (.local .finalTag) before:=by
    apply one_base program _ _ (.peek (aux .reader) (.local .finalTag) (.local (.field 0)) (.local (.field 0))) _ _ rfl rfl rfl
  have ht:Runs program 1 (.local .finalTag) before (.local .finalReverse) tagged:=by
    apply one_base program _ _ (.push (aux .reversed) false (.local .finalReverse)) _ _ rfl rfl
    exact update_aux _ _ _ _ _ _ _
  have hr:=reverse_final tagged (by rfl)
  have hw:tagged (aux .reversed)=false::raw:=by
    change (Function.update (rowAux [] raw) Aux.reversed (false::raw)) Aux.reversed=_
    exact Function.update_same _ _ _
  rw [hw] at hr
  have he:Function.update (Function.update tagged (aux .reversed) []) (aux .output) (false::raw).reverse=
      result m s (raw.reverse++[false]):=by
    simp only [tagged,update_aux,Function.update_idem,List.reverse_cons,result]
    congr 2
    funext k;cases k <;> rfl
  rw [he] at hr
  have h:=runs_trans program _ _ _ _ _ _ _ _ hp (runs_trans program _ _ _ _ _ _ _ _ ht hr)
  simpa only [List.length_cons,show 1+(1+(2*(raw.length+1)+3))=2*raw.length+7 by omega,before] using h
end RiemannGaussian.SemiprimeD1StackPortOwnerRoutingFinish
