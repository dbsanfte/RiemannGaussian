/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueRow
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueLoop
open SemiprimeD1StackOwnerFibreCatalogue SemiprimeD1StackOwnerFibreCatalogueSource
open SemiprimeD1StackOwnerFibreCatalogueView
open SemiprimeD1StackProcedureTrace (Runs runs_trans)
open SemiprimeSourceHistogramKeyBits (frame)
/-- Exact acquired owner-bank prefix followed by the ACTUAL untouched M-E suffix. -/
def idTape (queries:List (List Bool)) (tail:List Bool) :List Bool:=
  queries.foldr (fun q rest=>true::frame q rest) tail
/-- Physically emitted owner/fibre row bytes in original wire ordinal order. -/
def bytes (queries:List (List Bool)) (rows:List (List Bool×List Bool)) :List Bool:=
  queries.flatMap (fun q=>SemiprimeD1StackOwnerFibreCatalogueRow.row q rows)
/-- Sum of the SAME actual E-loop iteration clocks. -/
def budget (queries:List (List Bool)) (rows:List (List Bool×List Bool)) :Nat:=
  (queries.map (fun q=>SemiprimeD1StackOwnerFibreCatalogueRow.budget q rows)).sum
/-- COMPLETE real owner iterator. It uses the actual unary E counter and leaves the acquired
M-E bank suffix present; every owner query invokes the actual routed-tape filter and all14 drains. -/
theorem loop_run (s:R.Stack→List Bool) (rows:List (List Bool×List Bool))
    (hm:s (SemiprimeD1StackPortOwnerRouting.aux .output)=SemiprimeD1StackOwnerFibre.records rows [])
    (queries:List (List Bool)) (tail raw:List Bool) :
    ∃time≤budget queries rows,Runs program time (.local .loop)
      (data s (fun _=>[]) (rowAux (List.replicate queries.length true) (idTape queries tail) raw))
      (.local .loop) (data s (fun _=>[]) (rowAux [] tail ((bytes queries rows).reverse++raw))) := by
  induction queries generalizing raw with
  | nil=>refine ⟨0,by simp [budget],SemiprimeD1StackProcedureTrace.runs_refl program _ _⟩
  | cons q qs ih=>
    obtain ⟨a,ha,har⟩:=SemiprimeD1StackOwnerFibreCatalogueRow.row_run s rows hm q
      (List.replicate qs.length true) (idTape qs tail) raw
    obtain ⟨b,hb,hbr⟩:=ih ((SemiprimeD1StackOwnerFibreCatalogueRow.row q rows).reverse++raw)
    have h:=runs_trans program _ _ _ _ _ _ _ _ har hbr
    refine ⟨a+b,?_,?_⟩
    · simp only [budget,List.map_cons,List.sum_cons] at *;omega
    · simpa only [List.length_cons,List.replicate_succ,idTape,List.foldr_cons,bytes,List.flatMap_cons,
        List.reverse_append,List.append_assoc] using h
/-- Literal record frame appends its actual catalogue suffix. -/
theorem row_append (owner scopes tail:List Bool) :
    SemiprimeD1StackOwnerFibreCatalogueEmit.row owner scopes++tail=
      true::frame owner (frame scopes tail):=
  SemiprimeD1StackOwnerCatalogueOriginalMap.row_append owner scopes tail
/-- The actual owner/fibre output uses the old two-field record parser grammar. -/
theorem bytes_records (queries:List (List Bool)) (rows:List (List Bool×List Bool)) (tail:List Bool) :
    bytes queries rows++false::tail=SemiprimeD1StackOwnerLookup.records
      (queries.map (fun q=>(q,SemiprimeD1StackOwnerFibreCatalogueRow.scopes q rows))) tail:=by
  induction queries with
  | nil=>rfl
  | cons q qs ih=>
    change (SemiprimeD1StackOwnerFibreCatalogueRow.row q rows++bytes qs rows)++false::tail=_
    rw [List.append_assoc,ih]
    unfold SemiprimeD1StackOwnerFibreCatalogueRow.row
    rw [row_append]
    rfl
end RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueLoop
