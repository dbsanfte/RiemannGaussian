/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueRead
import RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueEmit
import RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueClear
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueRow
open SemiprimeD1StackOwnerFibreCatalogue SemiprimeD1StackOwnerFibreCatalogueSource
open SemiprimeD1StackOwnerFibreCatalogueView
open SemiprimeD1StackProcedureTrace (Runs runs_trans)
open SemiprimeSourceHistogramKeyBits (frame)
/-- Actual completely filtered scope vector, used only to state the physical execution result. -/
def scopes (query:List Bool) (rows:List (List Bool×List Bool)) :List Bool:=
  SemiprimeD1TensorTapeCodec.vectorBits (SemiprimeD1StackOwnerFibre.values query rows)
/-- Every role of the ACTUALLY halted real owner filter. -/
def filterDone (query:List Bool) (rows:List (List Bool×List Bool)) :V.Stack→List Bool:=
  (SemiprimeD1StackOwnerFibre.done query rows []).data
/-- Actual owner ID paired with its actual ordered scope vector bytes. -/
def row (query:List Bool) (rows:List (List Bool×List Bool)) :List Bool:=
  SemiprimeD1StackOwnerFibreCatalogueEmit.row query (scopes query rows)
/-- SAME actual E/ID header reads, query parser, full-tape copy/filter, emitter and fourteen payload drains. -/
def budget (query:List Bool) (rows:List (List Bool×List Bool)) :Nat:=
  (8*query.length+10)+(5*(SemiprimeD1StackOwnerFibre.records rows []).length+
    SemiprimeD1StackOwnerFibreBounds.runBound query rows+5)+
  (10*query.length+10*(scopes query rows).length+21)+
  SemiprimeD1StackOwnerFibreCatalogueClear.time (filterDone query rows) 14
/-- COMPLETE actual one-owner iteration: the E tally and M bank are physically read,
all routed occurrences are really scanned, and every real filter word is really erased. -/
theorem row_run (s:R.Stack→List Bool) (rows:List (List Bool×List Bool))
    (hm:s (SemiprimeD1StackPortOwnerRouting.aux .output)=SemiprimeD1StackOwnerFibre.records rows [])
    (query count ids raw:List Bool) :
    ∃time≤budget query rows,Runs program time (.local .loop)
      (data s (fun _=>[]) (rowAux (true::count) (true::frame query ids) raw)) (.local .loop)
      (data s (fun _=>[]) (rowAux count ids ((row query rows).reverse++raw))) := by
  let a:=rowAux count ids raw
  let a':=Function.update a .reversed ((row query rows).reverse++raw)
  have hr:=SemiprimeD1StackOwnerFibreCatalogueRead.query_read s query count ids raw
  obtain ⟨t,ht,hf⟩:=SemiprimeD1StackOwnerFibreCatalogueRead.copy_filter_run s a query rfl rows hm
  change Runs program t _ _ _ (data s (filterDone query rows) a) at hf
  have he:=SemiprimeD1StackOwnerFibreCatalogueEmit.row_run s (filterDone query rows) a rfl rfl
  have hq:filterDone query rows (.inr .query)=query:=rfl
  have hs:filterDone query rows (.inr .output)=scopes query rows:=rfl
  rw [hq,hs] at he
  change Runs program _ _ _ _ (data s (filterDone query rows) a') at he
  have hc:=SemiprimeD1StackOwnerFibreCatalogueClear.clear_run s (filterDone query rows) a'
  have ha:a'=rowAux count ids ((row query rows).reverse++raw):=by funext k;cases k <;> rfl
  rw [ha] at he hc
  have h:=runs_trans program _ _ _ _ _ _ _ _ hr (runs_trans program _ _ _ _ _ _ _ _ hf
    (runs_trans program _ _ _ _ _ _ _ _ he hc))
  refine ⟨_,?_,h⟩
  unfold budget
  omega
end RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueRow
