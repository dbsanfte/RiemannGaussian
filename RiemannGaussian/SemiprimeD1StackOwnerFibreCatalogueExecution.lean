/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueOriginal
import RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueFinish
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueExecution
open SemiprimeD1StackOwnerFibreCatalogue SemiprimeD1StackOwnerFibreCatalogueSource
open SemiprimeD1StackOwnerFibreCatalogueView SemiprimeD1StackOwnerFibreCatalogueOriginal
open SemiprimeD1StackProcedureTrace (Runs runs_trans halt_run)
open SemiprimeBitArithmetic (bitValue)
/-- Exact actual final all-original-owner fibre catalogue state, with unused M-E bank suffix retained. -/
def done (bits:List Bool) (hN:0<bitValue bits) :C.State Stack Label:=
  ⟨none,none,none,SemiprimeD1StackOwnerFibreCatalogueFinish.result
    (SemiprimeD1StackPortOwnerRoutingExecution.done bits hN).data (unused (bitValue bits))
    (SemiprimeD1StackOwnerFibreCatalogueLoop.bytes (queries (bitValue bits)) (pairs bits hN)++[false]),[]⟩
/-- SAME N-only acquisition, ALL actual E iterations, final catalogue materialization and halt. -/
def budget (bits:List Bool) (hN:0<bitValue bits) :Nat:=SemiprimeD1StackOwnerFibreCatalogueSource.budget bits hN+
  SemiprimeD1StackOwnerFibreCatalogueLoop.budget (queries (bitValue bits)) (pairs bits hN)+
  2*(SemiprimeD1StackOwnerFibreCatalogueLoop.bytes (queries (bitValue bits)) (pairs bits hN)).length+8
/-- COMPLETE N-only ALL-original-owner fibre acquisition. The real E counter selects FIRST E actual
M-bank words; every fibre is physically filtered from the actually routed factor-major occurrence tape.
No owner enumeration, key, E/M count, port fibre, degree or permutation is supplied to this machine. -/
theorem source_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃time≤budget bits hN,C.run program time (initial bits)=some (done bits hN):=by
  let s:=(SemiprimeD1StackPortOwnerRoutingExecution.done bits hN).data
  obtain ⟨a,ha,har⟩:=acquisition_run bits hc hN
  rw [ready_original bits hN] at har
  have hm:s (SemiprimeD1StackPortOwnerRouting.aux .output)=SemiprimeD1StackOwnerFibre.records (pairs bits hN) []:=
    source_pairs bits hc hN
  obtain ⟨b,hb,hbr⟩:=SemiprimeD1StackOwnerFibreCatalogueLoop.loop_run s (pairs bits hN) hm
    (queries (bitValue bits)) (unused (bitValue bits)) []
  simp only [List.append_nil] at hbr
  have hf:=SemiprimeD1StackOwnerFibreCatalogueFinish.finish_run s (unused (bitValue bits))
    (SemiprimeD1StackOwnerFibreCatalogueLoop.bytes (queries (bitValue bits)) (pairs bits hN)).reverse
  simp only [List.length_reverse,List.reverse_reverse] at hf
  have ht:=runs_trans program _ _ _ _ _ _ _ _ har (runs_trans program _ _ _ _ _ _ _ _ hbr hf)
  obtain ⟨finish,hr,hout⟩:=ht [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (.local .halt) rfl (done bits hN).data [] finish hout
  refine ⟨a+(b+(2*(SemiprimeD1StackOwnerFibreCatalogueLoop.bytes (queries (bitValue bits)) (pairs bits hN)).length+7))+1,?_,?_⟩
  · unfold budget;omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,hh]
    rfl
/-- ACTUAL N-only output is the complete original ascending E-owner catalogue with exact ordered scope vectors. -/
theorem output_original (bits:List Bool) (hN:0<bitValue bits) :
    (done bits hN).data (aux .output)=SemiprimeD1StackOwnerLookup.records (ownerRows (bitValue bits) hN) []:=by
  change SemiprimeD1StackOwnerFibreCatalogueLoop.bytes (queries (bitValue bits)) (pairs bits hN)++[false]=_
  exact original_bytes (bitValue bits) hN
end RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueExecution
