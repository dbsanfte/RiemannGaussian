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
namespace RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueRead
open SemiprimeD1StackOwnerFibreCatalogue SemiprimeD1StackOwnerFibreCatalogueSource
open SemiprimeD1StackOwnerFibreCatalogueView SemiprimeD1StackOwnerFibreCatalogueCalls
open SemiprimeD1StackProcedureTrace (Runs runs_trans one_base)
open SemiprimeSourceHistogramKeyBits (frame)
/-- Actual empty-reader filter state after its query was physically parsed from the acquired bank. -/
def queried (query:List Bool) :V.Stack→List Bool:=
  (SemiprimeD1StackOwnerFibre.initial query []).data
/-- Only the next actual owner query is present; every real filter work role remains empty. -/
theorem query_update (query:List Bool) :
    Function.update (fun _:V.Stack=>[]) (.inr .query) query=queried query:=by
  funext k;rcases k with k|k <;> cases k <;> rfl
/-- Actual real field-parser result, with its actual validity byte consumed. -/
theorem field_read (s:R.Stack→List Bool) (query count ids raw:List Bool) :
    Runs program (8*query.length+8) (.local .field)
      (data s (fun _=>[]) (rowAux count (frame query ids) raw)) (.local .copyPairs)
      (data s (queried query) (rowAux count ids raw)) := by
  let a:=rowAux count ids raw
  have hf:=field_call (data s (fun _=>[]) (rowAux count (frame query ids) raw)) query ids rfl rfl rfl rfl
  have hi:Function.update (rowAux count (frame query ids) raw) .readerIds ids=a:=by
    funext k;cases k <;> rfl
  simp only [update_aux,update_fibre,query_update,hi] at hf
  have hv:Runs program 1 (.local .valid) (data s (queried query) (Function.update a .valid [true]))
      (.local .copyPairs) (data s (queried query) a):=by
    apply one_base program _ _ (.pop (aux .valid) (.local .abort) (.local .abort) (.local .copyPairs)) _ _ rfl
    · simp only [SemiprimeD1StackBytecode.execute,data_aux,Function.update_same,
        SemiprimeD1StackBytecode.choose,List.head?_cons]
    · simp only [SemiprimeD1StackBytecode.execute,data_aux,Function.update_same,update_aux,
        Function.update_idem,List.tail_cons]
      have he:Function.update a .valid []=a:=by
        change Function.update a .valid (a .valid)=a
        exact Function.update_eq_self _ _
      rw [he]
  have h:=runs_trans program _ _ _ _ _ _ _ _ hf hv
  simpa only [show (8*query.length+7)+1=8*query.length+8 by omega,a] using h
/-- Consume ONE actual E-tally bit and ONE actual vector tag; E and M remain separate domains. -/
theorem headers (s:R.Stack→List Bool) (query count ids raw:List Bool) :
    Runs program 2 (.local .loop) (data s (fun _=>[]) (rowAux (true::count) (true::frame query ids) raw))
      (.local .field) (data s (fun _=>[]) (rowAux count (frame query ids) raw)) := by
  let a0:=rowAux (true::count) (true::frame query ids) raw
  let a1:=rowAux count (true::frame query ids) raw
  let a2:=rowAux count (frame query ids) raw
  have hc:Runs program 1 (.local .loop) (data s (fun _=>[]) a0) (.local .bankTag) (data s (fun _=>[]) a1):=by
    apply one_base program _ _ (.pop (aux .ownerCount) (.local .finalTag) (.local .abort) (.local .bankTag)) _ _ rfl rfl
    simp only [SemiprimeD1StackBytecode.execute,data_aux,update_aux]
    congr 1
    funext k;cases k <;> rfl
  have ht:Runs program 1 (.local .bankTag) (data s (fun _=>[]) a1) (.local .field) (data s (fun _=>[]) a2):=by
    apply one_base program _ _ (.pop (aux .readerIds) (.local .abort) (.local .abort) (.local .field)) _ _ rfl rfl
    simp only [SemiprimeD1StackBytecode.execute,data_aux,update_aux]
    congr 1
    funext k;cases k <;> rfl
  exact runs_trans program _ _ _ _ _ _ _ _ hc ht
/-- Physically acquire the next original owner query from the actual M bank under the actual E counter. -/
theorem query_read (s:R.Stack→List Bool) (query count ids raw:List Bool) :
    Runs program (8*query.length+10) (.local .loop)
      (data s (fun _=>[]) (rowAux (true::count) (true::frame query ids) raw)) (.local .copyPairs)
      (data s (queried query) (rowAux count ids raw)) := by
  have h:=runs_trans program _ _ _ _ _ _ _ _ (headers s query count ids raw) (field_read s query count ids raw)
  simpa only [show 2+(8*query.length+8)=8*query.length+10 by omega] using h
/-- Complete actual routed pair tape is copied into the real filter reader for THIS owner. -/
theorem pairs_copy (s:R.Stack→List Bool) (a:Aux→List Bool) (query:List Bool) (hs:a .copyScratch=[]) :
    Runs program (5*(s (SemiprimeD1StackPortOwnerRouting.aux .output)).length+4) (.local .copyPairs)
      (data s (queried query) a) (.local .filter)
      (data s (SemiprimeD1StackOwnerFibre.initial query (s (SemiprimeD1StackPortOwnerRouting.aux .output))).data a) := by
  have h:=copy_call 2 (data s (queried query) a) (.local .copyPairs) (.local .filter) rfl hs
  change Runs program _ _ _ _ (Function.update _ (fibreStack (.inr .reader))
    (s (SemiprimeD1StackPortOwnerRouting.aux .output)++[])) at h
  rw [List.append_nil,update_fibre] at h
  have he:Function.update (queried query) (.inr .reader) (s (SemiprimeD1StackPortOwnerRouting.aux .output))=
      (SemiprimeD1StackOwnerFibre.initial query (s (SemiprimeD1StackPortOwnerRouting.aux .output))).data:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  rw [he] at h
  exact h
/-- SAME-source actual routed-tape copy followed by real numeric owner-fibre filtering. -/
theorem copy_filter_run (s:R.Stack→List Bool) (a:Aux→List Bool) (query:List Bool) (hs:a .copyScratch=[])
    (rows:List (List Bool×List Bool))
    (hm:s (SemiprimeD1StackPortOwnerRouting.aux .output)=SemiprimeD1StackOwnerFibre.records rows []) :
    ∃time≤5*(SemiprimeD1StackOwnerFibre.records rows []).length+
      SemiprimeD1StackOwnerFibreBounds.runBound query rows+5,
      Runs program time (.local .copyPairs) (data s (queried query) a) (.local .emitTag)
        (data s (SemiprimeD1StackOwnerFibre.done query rows []).data a) := by
  have hc:=pairs_copy s a query hs
  rw [hm] at hc
  have hf:=filter_call s a query rows
  have h:=runs_trans program _ _ _ _ _ _ _ _ hc hf
  refine ⟨_,?_,h⟩
  have ht:=SemiprimeD1StackOwnerFibreBounds.time_le query rows
  omega
end RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueRead
