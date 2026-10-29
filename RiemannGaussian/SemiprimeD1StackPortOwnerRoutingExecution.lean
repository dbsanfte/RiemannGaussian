/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRoutingSource
import RiemannGaussian.SemiprimeD1StackPortOwnerRoutingLoop
import RiemannGaussian.SemiprimeD1StackPortOwnerRoutingFinish
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRoutingExecution
open SemiprimeD1StackPortOwnerRouting SemiprimeD1StackPortOwnerRoutingAcquisition
open SemiprimeD1StackPortOwnerRoutingView
open SemiprimeD1StackProcedureTrace (Runs runs_trans halt_run)
open SemiprimeBitArithmetic (bitValue)
/-- Actual original endpoint/owner map, used only to state the reached reader's semantics. -/
def map (bits:List Bool) (hN:0<bitValue bits) :=SemiprimeD1StackOwnerLookupOriginal.Public.catalogue (bitValue bits) hN
/-- Exact actual stopped routing state, preserving both physically acquired original source banks. -/
def done (bits:List Bool) (hN:0<bitValue bits) : C.State Stack Label :=
  ⟨none,none,none,SemiprimeD1StackPortOwnerRoutingFinish.result
    (SemiprimeD1StackOwnerCatalogueExecution.done bits).data (SemiprimeD1StackPortScopeExecution.done bits).data
    (SemiprimeD1StackPortOwnerRoutingLoop.bytes (map bits hN) (rows bits)++[false]),[]⟩
/-- SAME actual acquisitions, all occurrence routing iterations, final materialization and halt clocks. -/
def budget (bits:List Bool) (hN:0<bitValue bits) : Nat :=SemiprimeD1StackPortOwnerRoutingSource.budget bits+
  SemiprimeD1StackPortOwnerRoutingLoop.budget (map bits hN) (rows bits)+
  2*(SemiprimeD1StackPortOwnerRoutingLoop.bytes (map bits hN) (rows bits)).length+8
/-- Closed N-only routing source. Every original occurrence is routed by its actual parsed
slot/vertex key through the actual acquired E-map, preserving ALL original factor-major multiplicities. -/
theorem source_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃time≤budget bits hN,C.run program time (initial bits)=some (done bits hN) := by
  obtain ⟨a,ha,har⟩:=SemiprimeD1StackPortOwnerRoutingSource.acquisition_run bits hc hN
  let m:Map.Stack→List Bool:=(SemiprimeD1StackOwnerCatalogueExecution.done bits).data
  let s:Scope.Stack→List Bool:=(SemiprimeD1StackPortScopeExecution.done bits).data
  have hm:m (SemiprimeD1StackOwnerCatalogue.aux .output)=SemiprimeD1StackOwnerLookup.records (map bits hN) []:=
    SemiprimeD1StackOwnerCatalogueExecution.output_original bits hN
  obtain ⟨b,hb,hbr⟩:=SemiprimeD1StackPortOwnerRoutingLoop.loop_run m s (map bits hN) hm (rows bits) []
  have hr:ready bits=data m s (fun _=>[]) (fun _=>[])
      (rowAux (SemiprimeD1FactorScopePairEncoding.stream (rows bits) []) []):=by
    unfold ready
    rw [scoped_output]
  rw [hr] at har
  simp only [List.append_nil] at hbr
  have hf:=SemiprimeD1StackPortOwnerRoutingFinish.finish_run m s
    (SemiprimeD1StackPortOwnerRoutingLoop.bytes (map bits hN) (rows bits)).reverse
  simp only [List.length_reverse,List.reverse_reverse] at hf
  have ht:=runs_trans program _ _ _ _ _ _ _ _ har (runs_trans program _ _ _ _ _ _ _ _ hbr hf)
  obtain ⟨finish,hfinish,hout⟩:=ht [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (.local .halt) rfl (done bits hN).data [] finish hout
  refine ⟨a+(b+(2*(SemiprimeD1StackPortOwnerRoutingLoop.bytes (map bits hN) (rows bits)).length+7))+1,?_,?_⟩
  · unfold budget;omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
    rfl
/-- The ACTUAL N-only output is EXACTLY the original typed owner/scope pair tape used by owner-fibre filtering.
This discharges the prior prepared-routed-tape premise without E=M, wire-major order or permutation advice. -/
theorem output_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    (done bits hN).data (aux .output)=SemiprimeD1StackOwnerFibre.records
      (SemiprimeD1StackOwnerFibreOriginal.rows (bitValue bits) hN) [] := by
  change SemiprimeD1StackPortOwnerRoutingLoop.bytes (map bits hN) (rows bits)++[false]=_
  rw [SemiprimeD1StackPortOwnerRoutingLoop.bytes_records]
  unfold map
  rw [SemiprimeD1PortOwnerRoutingSpec.original_rows bits hc hN]
end RiemannGaussian.SemiprimeD1StackPortOwnerRoutingExecution
