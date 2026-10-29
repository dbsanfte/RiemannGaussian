/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueCacheClear
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackOwnerCatalogueRow
open SemiprimeD1StackOwnerCatalogue SemiprimeD1StackOwnerCatalogueSource
open SemiprimeD1StackOwnerCatalogueFields SemiprimeD1StackOwnerCatalogueParse
open SemiprimeD1StackOwnerCatalogueRecord SemiprimeD1StackOwnerCatalogueCalls
open SemiprimeD1StackOwnerCatalogueEmit SemiprimeD1StackOwnerCatalogueClear
open SemiprimeD1StackOwnerCatalogueCacheClear
open SemiprimeD1StackProcedureTrace (Runs runs_trans)
namespace P
export SemiprimeD1StackPortOwnerRecipeSpec (Counters words)
export SemiprimeD1StackPortOwnerRecipe (Tag)
export SemiprimeD1StackPortOwnerRecipeDecision (tagCode)
end P
/-- Exact actual recipe-work payload after its real complete call. -/
def recipeWork (c:P.Counters) (tag:P.Tag) : RecipeWork→List Bool :=
  fun k=>(SemiprimeD1StackPortOwnerRecipeExecution.done c tag).data (.inr k)
/-- Physically computed arithmetic output bytes, used only to describe the execution result. -/
def arithmeticBytes (c:P.Counters) (tag:P.Tag) : List Bool := recipeWork c tag (.inr .output)
/-- Equality key consists of the actually framed record and the actually copied true sentinel. -/
def equalityBytes (p:Fin 7→List Bool) : List Bool := edgeRest p 0 []++[true]
/-- Actual rows emitted for both endpoints, retaining the SAME next acquired ID word. -/
def emitted (p:Fin 7→List Bool) (c:P.Counters) (tag:P.Tag) : List Bool :=
  rowBytes (arithmeticBytes c tag) (p 6)++rowBytes (equalityBytes p) (p 6)
/-- Actual cleanup payloads: seven parsed words, rebuilt record and sentinel-copy key. -/
def rowPacket (p:Fin 7→List Bool) : Packet :=
  fun i=>if h:i.val<7 then p ⟨i.val,h⟩ else if i=7 then edgeRest p 0 [] else equalityBytes p
/-- Sum of the SAME physical row parser, builder, arithmetic, emitter and cleanup source bounds. -/
def budget (p:Fin 7→List Bool) (c:P.Counters) (tag:P.Tag) : Nat :=
  (1+edgeTime p 6+(8*(p 6).length+9))+recordTime p 6+
  (5*(edgeRest p 0 []).length+7)+(SemiprimeD1StackPortOwnerRecipeExecution.budget c tag+1)+
  (10*(arithmeticBytes c tag).length+10*(equalityBytes p).length+20*(p 6).length+42)+
  workTime (recipeWork c tag) 47+cacheTime (rowPacket p) 9
/-- All actual recipe inputs avoid private outer builder/collector scratch. -/
theorem input_aux (s:S.Stack→List Bool) (f:Fin 7→List Bool) (a b:Aux→List Bool) (i:R.Input) :
    data s (fun _=>[]) f a (recipeStack (.inl i))=
      data s (fun _=>[]) f b (recipeStack (.inl i)) := by cases i <;> rfl
/-- A complete SAME-source iteration: parse one real edge and next ID, compute both keys,
emit both rows, physically erase all 56 row/work roles and return to the edge-tape loop.
The counter interpretation is proof-only; every runtime operand comes from acquired tapes. -/
theorem row_run (s:S.Stack→List Bool) (p:Fin 7→List Bool) (c:P.Counters) (tag:P.Tag)
    (ht:c.tag=(P.tagCode tag).val) (hd:0<c.digits) (edges ids collector:List Bool)
    (hi:∀i:R.Input,data s (fun _=>[]) p (rowAux edges ids collector) (recipeStack (.inl i))=P.words c i) :
    ∃time≤budget p c tag,Runs program time (.local .parse)
      (data s (fun _=>[]) (parsed p 0) (parseAux p 0 edges ids collector))
      (.local .parse) (data s (fun _=>[]) (fun _=>[])
        (rowAux edges ids ((emitted p c tag).reverse++collector))) := by
  let a0:=rowAux edges ids collector
  let a1:=Function.update a0 .record (edgeRest p 0 [])
  let a2:=Function.update a1 .equalityKey (equalityBytes p)
  let a3:=Function.update a2 .reversed ((emitted p c tag).reverse++collector)
  have hread:=row_read s (fun _=>[]) p edges ids collector
  have hrecord:=record_run s (fun _=>[]) p edges ids collector
  change Runs program _ _ _ _ (data s (fun _=>[]) p a1) at hrecord
  have heq:=equality_call (data s (fun _=>[]) p a1)
    (by change a1 .equalityKey=[];exact Function.update_of_ne (by decide) _ _)
    (by change a1 .equalityScratch=[];exact Function.update_of_ne (by decide) _ _)
  have hrec:data s (fun _=>[]) p a1 (aux .record)=edgeRest p 0 []:=by
    change a1 .record=_;exact Function.update_same _ _ _
  rw [hrec,update_aux] at heq
  change Runs program _ _ _ _ (data s (fun _=>[]) p a2) at heq
  obtain ⟨t,htime,hrecipe⟩:=recipe_call s p a2 c tag ht hd (fun i=>by
    rw [input_aux s p a2 a0 i];exact hi i)
  change Runs program _ _ _ _ (data s (recipeWork c tag) p a2) at hrecipe
  have hem:=emit_both s (recipeWork c tag) p a2
    (by simp only [a2,a1,Function.update_of_ne (by decide : Aux.frameBuffer≠.equalityKey),
      Function.update_of_ne (by decide : Aux.frameBuffer≠.record)];rfl)
    (by simp only [a2,a1,Function.update_of_ne (by decide : Aux.frameScratch≠.equalityKey),
      Function.update_of_ne (by decide : Aux.frameScratch≠.record)];rfl)
  have hkey:data s (recipeWork c tag) p a2 (keySource false)=arithmeticBytes c tag:=rfl
  have hekey:a2 .equalityKey=equalityBytes p:=Function.update_same _ _ _
  have hcol:a2 .reversed=collector:=by
    simp only [a2,a1,Function.update_of_ne (by decide : Aux.reversed≠.equalityKey),
      Function.update_of_ne (by decide : Aux.reversed≠.record)];rfl
  rw [hkey,hekey,hcol] at hem
  change Runs program _ _ _ _ (data s (recipeWork c tag) p a3) at hem
  have hw:=work_run s (recipeWork c tag) p a3
  have hp:data s (fun _=>[]) p a3=
      packet s (rowPacket p) edges ids ((emitted p c tag).reverse++collector):=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · change p k=rowPacket p ⟨k.val,by omega⟩
          simp only [rowPacket,k.isLt,dite_eq_left]
        · cases k <;> simp only [packet,data,a3,a2,a1,a0,rowPacket,equalityBytes] <;> rfl
  rw [hp] at hw
  have hc:=cache_run s (rowPacket p) edges ids ((emitted p c tag).reverse++collector)
  have h:=runs_trans program _ _ _ _ _ _ _ _ hread
    (runs_trans program _ _ _ _ _ _ _ _ hrecord
      (runs_trans program _ _ _ _ _ _ _ _ heq
        (runs_trans program _ _ _ _ _ _ _ _ hrecipe
          (runs_trans program _ _ _ _ _ _ _ _ hem (runs_trans program _ _ _ _ _ _ _ _ hw hc)))))
  refine ⟨_,?_,h⟩
  unfold budget
  omega
end RiemannGaussian.SemiprimeD1StackOwnerCatalogueRow
