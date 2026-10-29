/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueCalls
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackOwnerCatalogueEmit
open SemiprimeD1StackOwnerCatalogue SemiprimeD1StackOwnerCatalogueSource
open SemiprimeD1StackOwnerCatalogueFields
open SemiprimeD1StackProcedureTrace (Runs included_call runs_trans one_base)
open SemiprimeD1StackPortOwnerRecipeCalls (update_rel)
open SemiprimeSourceHistogramKeyBits (frame)
namespace Rel
export SemiprimeD1StackMultiplierLink (DataRel)
end Rel
/-- Every endpoint and owner payload framer uses three distinct actual roles. -/
theorem pair_injective : ∀host value:Bool,Function.Injective (pairStack host value) := by decide
/-- Both collector-reversal calls have two distinct actual roles. -/
theorem reverse_injective : ∀finish:Bool,Function.Injective (reverseStack finish) := by decide
/-- Static payload source: computed key first, same actual acquired owner word second. -/
def pairSource (host value:Bool) : Stack := if value then cache 6 else keySource host
/-- Static caller continuation after an actual field reversal. -/
def reverseNext (host value:Bool) : Label :=
  if value then (if host then .local (.clearRecipe 0) else .local (.emitTag true))
  else .local (.emitField host true)
/-- A computed key or acquired owner-ID word is physically framed. -/
theorem pair_call (host value:Bool) (store:Stack→List Bool) (hs:store (aux .frameScratch)=[]) :
    Runs program (6*(store (pairSource host value)).length+5)
      (.local (.emitField host value)) store (.local (.emitReverse host value))
      (Function.update store (aux .frameBuffer)
        (frame (store (pairSource host value)) (store (aux .frameBuffer)))) := by
  let word:=store (pairSource host value)
  let tail:=store (aux .frameBuffer)
  let before:=SemiprimeD1StackFrame.state 0 none word tail []
  let after:=SemiprimeD1StackFrame.done word (frame word tail)
  have hi:Rel.DataRel (pairStack host value) store before.store store:=by
    constructor
    · intro k;fin_cases k <;> simp [before,SemiprimeD1StackFrame.state,SemiprimeD1StackFrame.payload,
        pairStack,pairSource,word,tail,hs]
    · intro k _;rfl
  apply included_call program (pairStack host value) (Label.pair host value) (pair_injective host value)
    SemiprimeD1StackFrame.code 0 (fun _=>rfl) (.local (.emitField host value))
    (.local (.emitReverse host value)) rfl _ before after
  · rfl
  · rfl
  · exact SemiprimeD1StackFrame.frame_words word tail none
  · exact hi
  · have he:Function.update before.store (1:Fin 3) (frame word tail)=after.store:=by
      funext k;fin_cases k <;> rfl
    simpa only [he,pairStack,show ¬(1:Fin 3)=0 by decide,ite_false,ite_true] using
      update_rel (pairStack host value) (pair_injective host value) store before.store store hi 1 (frame word tail)
/-- An actual field frame is transferred into the actual reversed record collector. -/
theorem reverse_field (host value:Bool) (store:Stack→List Bool) :
    Runs program (2*(store (aux .frameBuffer)).length+3)
      (.local (.emitReverse host value)) store (reverseNext host value)
      (Function.update (Function.update store (aux .frameBuffer) []) (aux .reversed)
        ((store (aux .frameBuffer)).reverse++store (aux .reversed))) := by
  let word:=store (aux .frameBuffer)
  let tail:=store (aux .reversed)
  let before:=SemiprimeD1StackReverseWord.state none word tail
  let after:=SemiprimeD1StackReverseWord.done (word.reverse++tail)
  have hi:Rel.DataRel (reverseStack false) store before.store store:=by
    constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  apply included_call program (reverseStack false) (Label.reverse false) (reverse_injective false)
    SemiprimeD1StackReverseWord.code 0 (fun _=>rfl) (.local (.emitReverse host value))
    (reverseNext host value) rfl _ before after
  · rfl
  · rfl
  · exact SemiprimeD1StackReverseWord.reverse_run word tail none
  · exact hi
  · have h0:=update_rel (reverseStack false) (reverse_injective false) store before.store store hi 0 []
    have h1:=update_rel (reverseStack false) (reverse_injective false) store _ _ h0 1 (word.reverse++tail)
    have he:Function.update (Function.update before.store (0:Fin 2) []) 1 (word.reverse++tail)=after.store:=by
      funext k;fin_cases k <;> rfl
    simpa [he,reverseStack,word,tail] using h1
/-- One actual frame and reversal leave their real buffer empty and prepend its actual bytes. -/
theorem emit_field (s:S.Stack→List Bool) (w:RecipeWork→List Bool) (f:Fin 7→List Bool)
    (a:Aux→List Bool) (host value:Bool) (hb:a .frameBuffer=[]) (hs:a .frameScratch=[]) :
    Runs program (10*(data s w f a (pairSource host value)).length+10)
      (.local (.emitField host value)) (data s w f a) (reverseNext host value)
      (data s w f (Function.update a .reversed
        ((frame (data s w f a (pairSource host value)) []).reverse++a .reversed))) := by
  let word:=data s w f a (pairSource host value)
  let a':=Function.update a .frameBuffer (frame word [])
  have hp:=pair_call host value (data s w f a) hs
  have hout:Function.update (data s w f a) (aux .frameBuffer)
      (frame (data s w f a (pairSource host value)) (data s w f a (aux .frameBuffer)))=
      data s w f a':=by simp only [data_aux,hb,update_aux,a',word]
  rw [hout] at hp
  have hr:=reverse_field host value (data s w f a')
  have hframe:data s w f a' (aux .frameBuffer)=frame word []:=by
    change a' .frameBuffer=frame word []
    exact Function.update_same _ _ _
  have hreverse:data s w f a' (aux .reversed)=a .reversed:=by
    change a' .reversed=a .reversed
    exact Function.update_of_ne (by decide : Aux.reversed≠.frameBuffer) _ _
  rw [hframe,hreverse] at hr
  have hclean:Function.update (Function.update (data s w f a') (aux .frameBuffer) [])
      (aux .reversed) ((frame word []).reverse++a .reversed)=
      data s w f (Function.update a .reversed ((frame word []).reverse++a .reversed)):=by
    simp only [a',update_aux,Function.update_idem]
    rw [←hb,Function.update_eq_self]
  rw [hclean] at hr
  have ht:=runs_trans program _ _ _ _ _ _ _ _ hp hr
  simpa only [SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil,word,
    show 6*(data s w f a (pairSource host value)).length+5+
      (2*(2*(data s w f a (pairSource host value)).length+0+1)+3)=
      10*(data s w f a (pairSource host value)).length+10 by omega] using ht
/-- Updating the actual output collector cannot overwrite either endpoint key or its owner ID. -/
theorem pairSource_reversed (s:S.Stack→List Bool) (w:RecipeWork→List Bool) (f:Fin 7→List Bool)
    (a:Aux→List Bool) (tail:List Bool) (host value:Bool) :
    data s w f (Function.update a .reversed tail) (pairSource host value)=
      data s w f a (pairSource host value) := by
  cases host
  · cases value <;> rfl
  · cases value
    · change (Function.update a .reversed tail) .equalityKey=a .equalityKey
      exact Function.update_of_ne (by decide : Aux.equalityKey≠.reversed) _ _
    · rfl

/-- Literal endpoint-map row, without its following map suffix. -/
def rowBytes (key owner:List Bool) : List Bool := true::frame key (frame owner [])
/-- Both actual field frames and real collector transfers, including the pushed row tag. -/
theorem emit_row (s:S.Stack→List Bool) (w:RecipeWork→List Bool) (f:Fin 7→List Bool)
    (a:Aux→List Bool) (host:Bool) (hb:a .frameBuffer=[]) (hs:a .frameScratch=[]) :
    Runs program (10*(data s w f a (keySource host)).length+10*(f 6).length+21)
      (.local (.emitTag host)) (data s w f a) (reverseNext host true)
      (data s w f (Function.update a .reversed
        ((rowBytes (data s w f a (keySource host)) (f 6)).reverse++a .reversed))) := by
  let key:=data s w f a (keySource host)
  let a0:=Function.update a .reversed (true::a .reversed)
  let a1:=Function.update a0 .reversed ((frame key []).reverse++a0 .reversed)
  have htag:Runs program 1 (.local (.emitTag host)) (data s w f a)
      (.local (.emitField host false)) (data s w f a0):=by
    apply one_base program _ _ (.push (aux .reversed) true (.local (.emitField host false))) _ _ rfl rfl
    exact update_aux _ _ _ _ _ _
  have hkey:=emit_field s w f a0 host false
    (by simpa only [a0,Function.update_of_ne (by decide : Aux.frameBuffer≠.reversed)] using hb)
    (by simpa only [a0,Function.update_of_ne (by decide : Aux.frameScratch≠.reversed)] using hs)
  rw [show data s w f a0 (pairSource host false)=key by
    simpa only [a0,pairSource,Bool.false_eq_true,ite_false,key] using pairSource_reversed s w f a _ host false] at hkey
  change Runs program (10*key.length+10) (.local (.emitField host false)) (data s w f a0)
    (.local (.emitField host true)) (data s w f a1) at hkey
  have howner:=emit_field s w f a1 host true
    (by simpa only [a1,a0,Function.update_of_ne (by decide : Aux.frameBuffer≠.reversed)] using hb)
    (by simpa only [a1,a0,Function.update_of_ne (by decide : Aux.frameScratch≠.reversed)] using hs)
  have hword:data s w f a1 (pairSource host true)=f 6:=rfl
  rw [hword] at howner
  have hout:Function.update a1 .reversed ((frame (f 6) []).reverse++a1 .reversed)=
      Function.update a .reversed ((rowBytes key (f 6)).reverse++a .reversed):=by
    simp only [a1,a0,Function.update_same,Function.update_idem,rowBytes,←List.append_assoc]
    rw [show frame key (frame (f 6) [])=frame key []++frame (f 6) [] by
      rw [SemiprimeD1StackOwnerEqualityKey.frame_append];rfl]
    simp only [List.reverse_cons,List.reverse_append,List.append_assoc,List.singleton_append]
  rw [hout] at howner
  have ht:=runs_trans program _ _ _ _ _ _ _ _ htag (runs_trans program _ _ _ _ _ _ _ _ hkey howner)
  simpa only [key,show 1+(10*(data s w f a (keySource host)).length+10+
    (10*(f 6).length+10))=10*(data s w f a (keySource host)).length+10*(f 6).length+21 by omega] using ht
/-- Both physical endpoints of the same original wire carry the SAME acquired owner-ID word. -/
theorem emit_both (s:S.Stack→List Bool) (w:RecipeWork→List Bool) (f:Fin 7→List Bool)
    (a:Aux→List Bool) (hb:a .frameBuffer=[]) (hs:a .frameScratch=[]) :
    Runs program (10*(data s w f a (keySource false)).length+10*(a .equalityKey).length+
      20*(f 6).length+42) (.local (.emitTag false)) (data s w f a)
      (.local (.clearRecipe 0))
      (data s w f (Function.update a .reversed
        ((rowBytes (data s w f a (keySource false)) (f 6)++rowBytes (a .equalityKey) (f 6)).reverse++a .reversed))) := by
  let arith:=data s w f a (keySource false)
  let a':=Function.update a .reversed ((rowBytes arith (f 6)).reverse++a .reversed)
  have hf:=emit_row s w f a false hb hs
  change Runs program _ _ _ (.local (.emitTag true)) (data s w f a') at hf
  have ht:=emit_row s w f a' true
    (by simpa only [a',Function.update_of_ne (by decide : Aux.frameBuffer≠.reversed)] using hb)
    (by simpa only [a',Function.update_of_ne (by decide : Aux.frameScratch≠.reversed)] using hs)
  have he:data s w f a' (keySource true)=a .equalityKey:=by
    change a' .equalityKey=a .equalityKey
    exact Function.update_of_ne (by decide : Aux.equalityKey≠.reversed) _ _
  rw [he] at ht
  have hout:Function.update a' .reversed ((rowBytes (a .equalityKey) (f 6)).reverse++a' .reversed)=
      Function.update a .reversed
        ((rowBytes arith (f 6)++rowBytes (a .equalityKey) (f 6)).reverse++a .reversed):=by
    simp only [a',Function.update_same,Function.update_idem,List.reverse_append,List.append_assoc]
  rw [hout] at ht
  have h:=runs_trans program _ _ _ _ _ _ _ _ hf ht
  simpa only [arith,reverseNext,ite_true,show
    (10*(data s w f a (keySource false)).length+10*(f 6).length+21)+
    (10*(a .equalityKey).length+10*(f 6).length+21)=
    10*(data s w f a (keySource false)).length+10*(a .equalityKey).length+20*(f 6).length+42 by omega] using h
end RiemannGaussian.SemiprimeD1StackOwnerCatalogueEmit
