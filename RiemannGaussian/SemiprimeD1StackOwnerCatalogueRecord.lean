/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueParse
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackOwnerCatalogueRecord
open SemiprimeD1StackOwnerCatalogue SemiprimeD1StackOwnerCatalogueSource
open SemiprimeD1StackOwnerCatalogueFields SemiprimeD1StackOwnerCatalogueParse
open SemiprimeD1StackProcedureTrace (Runs included_call runs_trans)
open SemiprimeD1StackPortOwnerRecipeCalls (update_rel)
open SemiprimeSourceHistogramKeyBits (frame)
namespace Rel
export SemiprimeD1StackMultiplierLink (DataRel)
end Rel
/-- Every one of the six actual record framers uses three distinct physical roles. -/
theorem record_injective (part:Fin 6) : Function.Injective (recordStack part) := by
  fin_cases part <;> decide
/-- Actual next record-framing position. -/
def recordNext (part:Fin 6) : Label :=
  if h:part.val<5 then .local (.record ⟨part.val+1,by omega⟩) else .local .equality
/-- One original field is physically framed onto the actual equality-record suffix. -/
theorem record_call (part:Fin 6) (store:Stack→List Bool)
    (hs:store (aux .frameScratch)=[]) :
    Runs program (6*(store (cache ⟨5-part.val,by omega⟩)).length+5)
      (.local (.record part)) store (recordNext part)
      (Function.update store (aux .record)
        (frame (store (cache ⟨5-part.val,by omega⟩)) (store (aux .record)))) := by
  let word:=store (cache ⟨5-part.val,by omega⟩)
  let tail:=store (aux .record)
  let before:=SemiprimeD1StackFrame.state 0 none word tail []
  let after:=SemiprimeD1StackFrame.done word (frame word tail)
  have hi:Rel.DataRel (recordStack part) store before.store store:=by
    constructor
    · intro k;fin_cases k <;> simp [before,SemiprimeD1StackFrame.state,SemiprimeD1StackFrame.payload,
        recordStack,word,tail,hs]
    · intro k _;rfl
  apply included_call program (recordStack part) (Label.record part) (record_injective part)
    SemiprimeD1StackFrame.code 0 (fun _=>rfl) (.local (.record part)) (recordNext part) rfl _ before after
  · rfl
  · rfl
  · exact SemiprimeD1StackFrame.frame_words word tail none
  · exact hi
  · have he:Function.update before.store (1:Fin 3) (frame word tail)=after.store:=by
      funext k;fin_cases k <;> rfl
    simpa only [he,recordStack,show ¬(1:Fin 3)=0 by decide,ite_false,ite_true] using
      update_rel (recordStack part) (record_injective part) store before.store store hi 1 (frame word tail)
/-- The actual built equality-record suffix after n real framing calls. -/
def recordTail (p:Fin 7→List Bool) (n:Nat) : List Bool := edgeRest p (6-n) []
/-- Framing from the last parsed coordinate to the first produces the original record order. -/
theorem recordTail_step (p:Fin 7→List Bool) (n:Nat) (hn:n<6) :
    frame (p ⟨5-n,by omega⟩) (recordTail p n)=recordTail p (n+1) := by
  have h:=edgeRest_step p (5-n) (by omega) []
  have ha:5-n+1=6-n:=by omega
  have hb:6-(n+1)=5-n:=by omega
  simpa only [recordTail,ha,hb] using h.symm
/-- The physical record is empty before its first frame. -/
theorem recordTail_zero (p:Fin 7→List Bool) : recordTail p 0=[]:=edgeRest_end p []
/-- Six physical frames reconstruct precisely the acquired original six-field record. -/
theorem recordTail_six (p:Fin 7→List Bool) : recordTail p 6=edgeRest p 0 []:=rfl
/-- Actual outer store after n equality-record frames. -/
def recordStore (s:S.Stack→List Bool) (w:RecipeWork→List Bool) (p:Fin 7→List Bool)
    (n:Nat) (edges ids collector:List Bool) : Stack→List Bool :=
  data s w p (Function.update (rowAux edges ids collector) .record (recordTail p n))
/-- Static current record call, followed by equality-key acquisition after call six. -/
def recordPC (n:Nat) : Label :=
  if h:n<6 then .local (.record ⟨n,h⟩) else .local .equality
/-- Actual cost of n physical record-frame calls, in their physical last-first order. -/
def recordTime (p:Fin 7→List Bool) : Nat→Nat
  | 0=>0
  | n+1=>recordTime p n+(6*(p ⟨(5-n)%7,Nat.mod_lt _ (by omega)⟩).length+5)
/-- Each real call prepends the next physically parsed field and clears its real scratch. -/
theorem record_step (s:S.Stack→List Bool) (w:RecipeWork→List Bool) (p:Fin 7→List Bool)
    (n:Nat) (hn:n<6) (edges ids collector:List Bool) :
    Runs program (6*(p ⟨5-n,by omega⟩).length+5) (recordPC n)
      (recordStore s w p n edges ids collector) (recordPC (n+1))
      (recordStore s w p (n+1) edges ids collector) := by
  let part:Fin 6:=⟨n,hn⟩
  have hs:recordStore s w p n edges ids collector (aux .frameScratch)=[]:=by
    simp only [recordStore,data_aux,Function.update_of_ne (by decide : Aux.frameScratch≠.record),rowAux]
  have hr:=record_call part (recordStore s w p n edges ids collector) hs
  have hout:Function.update (recordStore s w p n edges ids collector) (aux .record)
      (frame ((recordStore s w p n edges ids collector) (cache ⟨5-part.val,by omega⟩))
        ((recordStore s w p n edges ids collector) (aux .record)))=
      recordStore s w p (n+1) edges ids collector:=by
    simp only [recordStore,data_cache,data_aux,Function.update_same,update_aux,Function.update_idem]
    rw [recordTail_step p n hn]
  have hp:recordNext part=recordPC (n+1):=by
    unfold recordNext recordPC
    by_cases h:n<5
    · simp only [part,h,dite_eq_left,show n+1<6 by omega]
    · have he:n=5:=by omega
      subst n;rfl
  rw [hout,hp] at hr
  simpa only [recordPC,dite_eq_left hn,recordStore,data_cache,part] using hr
/-- The six literal calls rebuild the exact equality endpoint record from acquired words. -/
theorem record_prefix (s:S.Stack→List Bool) (w:RecipeWork→List Bool) (p:Fin 7→List Bool)
    (n:Nat) (hn:n≤6) (edges ids collector:List Bool) :
    Runs program (recordTime p n) (recordPC 0) (recordStore s w p 0 edges ids collector)
      (recordPC n) (recordStore s w p n edges ids collector) := by
  induction n with
  | zero=>exact SemiprimeD1StackProcedureTrace.runs_refl program _ _
  | succ n ih=>
    have hlt:n<6:=by omega
    have hm:(5-n)%7=5-n:=Nat.mod_eq_of_lt (by omega)
    have ht:=runs_trans program _ _ _ _ _ _ _ _ (ih (by omega))
      (record_step s w p n hlt edges ids collector)
    simpa only [recordTime,hm] using ht
/-- The exact acquired record is rebuilt by six actual calls, ready for sentinel-copy. -/
theorem record_run (s:S.Stack→List Bool) (w:RecipeWork→List Bool) (p:Fin 7→List Bool)
    (edges ids collector:List Bool) :
    Runs program (recordTime p 6) (.local (.record 0)) (data s w p (rowAux edges ids collector))
      (.local .equality) (data s w p (Function.update (rowAux edges ids collector)
        .record (edgeRest p 0 []))) := by
  have h:=record_prefix s w p 6 (by omega) edges ids collector
  have hzero:recordStore s w p 0 edges ids collector=data s w p (rowAux edges ids collector):=by
    simp only [recordStore,recordTail_zero]
    rw [show ([]:List Bool)=rowAux edges ids collector .record by rfl,Function.update_eq_self]
  rw [hzero] at h
  have hp0:recordPC 0=.local (.record 0):=by simp [recordPC]
  have hp6:recordPC 6=.local .equality:=by simp [recordPC]
  rw [hp0,hp6] at h
  simpa only [recordStore,recordTail_six] using h

/-- Actual six-call frame time is linear in a bound on the acquired payload lengths. -/
theorem recordTime_bound (p:Fin 7→List Bool) (cap n:Nat) (hp:∀i,(p i).length≤cap) :
    recordTime p n≤n*(6*cap+5) := by
  induction n with
  | zero=>simp only [recordTime,Nat.zero_mul,Nat.le_refl]
  | succ n ih=>
    have h:=hp ⟨(5-n)%7,Nat.mod_lt _ (by omega)⟩
    simp only [recordTime]
    nlinarith
end RiemannGaussian.SemiprimeD1StackOwnerCatalogueRecord
