/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRoutingView
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRoutingSource
open SemiprimeD1StackPortOwnerRouting SemiprimeD1StackPortOwnerRoutingAcquisition
open SemiprimeD1StackPortOwnerRoutingView
open SemiprimeD1StackProcedureTrace (Runs runs_trans)
open SemiprimeBitArithmetic (bitValue)
/-- Actual scoped tape is copied into the real private reader; both source banks are retained. -/
theorem reader_copy (bits:List Bool) :
    Runs program (5*((SemiprimeD1StackPortScopeExecution.done bits).data
      (SemiprimeD1StackPortScopeRecords.aux .output)).length+4)
      (.local .copyPorts) (acquired bits) (.local .parse) (ready bits) := by
  have h:=copy_call 1 (acquired bits) (.local .copyPorts) (.local .parse) rfl rfl
  change Runs program _ _ _ _ (Function.update (acquired bits) (aux .reader)
    ((SemiprimeD1StackPortScopeExecution.done bits).data (SemiprimeD1StackPortScopeRecords.aux .output)++[])) at h
  rw [List.append_nil] at h
  have he:Function.update (acquired bits) (aux .reader)
      ((SemiprimeD1StackPortScopeExecution.done bits).data (SemiprimeD1StackPortScopeRecords.aux .output))=ready bits:=by
    unfold acquired fresh
    rw [update_aux]
    unfold ready
    congr 1
    funext k;cases k <;> rfl
  rw [he] at h
  exact h
/-- Sum of actual N copy, both actual acquisitions and actual whole scoped-tape reader copy. -/
def budget (bits:List Bool) : Nat :=5*bits.length+4+
  (SemiprimeD1StackOwnerCatalogueBounds.polynomial bits.length+1)+(10^111*(bits.length+1)^30+1)+
  (5*((SemiprimeD1StackPortScopeExecution.done bits).data (SemiprimeD1StackPortScopeRecords.aux .output)).length+4)
/-- Closed original binary-N prefix for the TWO real tapes required by factor-major owner routing. -/
theorem acquisition_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃time≤budget bits,Runs program time (.local .main) (input bits) (.local .parse) (ready bits) := by
  obtain ⟨time,ht,hr⟩:=sources_run bits hc hN
  have hc:=reader_copy bits
  have h:=runs_trans program _ _ _ _ _ _ _ _ hr hc
  refine ⟨_,?_,h⟩
  unfold budget
  omega
/-- The actually retained forward map is EXACTLY the original E-map expected by real lookup. -/
theorem acquired_map (bits:List Bool) (hN:0<bitValue bits) :
    ready bits sourceMap=SemiprimeD1StackOwnerLookup.records
      (SemiprimeD1StackOwnerLookupOriginal.Public.catalogue (bitValue bits) hN) [] := by
  change (SemiprimeD1StackOwnerCatalogueExecution.done bits).data (SemiprimeD1StackOwnerCatalogue.aux .output)=_
  exact SemiprimeD1StackOwnerCatalogueExecution.output_original bits hN
/-- Actual factor-major reader bytes equal ALL original typed incidences, with no supplied order premise. -/
theorem reader_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ready bits (aux .reader)=SemiprimeD1FactorScopePairEncoding.stream
      (SemiprimeD1FactorScopeIncidencesOriginal.indexedRows (bitValue bits)) [] := by
  change (SemiprimeD1StackPortScopeExecution.done bits).data (SemiprimeD1StackPortScopeRecords.aux .output)=_
  rw [scoped_output,rows,SemiprimeD1FactorScopeIncidencesOriginal.original_rows bits hc hN]
end RiemannGaussian.SemiprimeD1StackPortOwnerRoutingSource
