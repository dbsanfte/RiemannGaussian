/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueOriginalMap
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueFinish
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackOwnerCatalogueExecution
open SemiprimePublicAcquiredExecution SemiprimeMacroParameters
open SemiprimeD1StackOwnerCatalogue SemiprimeD1StackOwnerCatalogueSource
open SemiprimeD1StackOwnerCatalogueParse SemiprimeD1StackOwnerCatalogueOriginalRow
open SemiprimeD1StackOwnerCatalogueOriginalIds SemiprimeD1StackOwnerCatalogueOriginalMap
open SemiprimeD1StackProcedureTrace (Runs runs_trans halt_run)
open SemiprimeBitArithmetic (bitValue)
/-- Exact actual final state of the N-only forward owner-map source. -/
def done (bits:List Bool) : C.State Stack Label :=
  ⟨none,none,none,SemiprimeD1StackOwnerCatalogueFinish.result
    (SemiprimeD1StackRootScopeBankExecution.result bits) (unused (bitValue bits))
    (SemiprimeD1StackOwnerCatalogueLoop.bytes (pairs (bitValue bits))++[false]),[]⟩
/-- Actual acquired source, both full reader copies, actual E iterations, whole reversal and halt. -/
def budget (bits:List Bool) : Nat := SemiprimeD1StackOwnerCatalogueSource.budget bits+
  SemiprimeD1StackOwnerCatalogueLoop.budget (pairs (bitValue bits))+
  2*(SemiprimeD1StackOwnerCatalogueLoop.bytes (pairs (bitValue bits))).length+8
/-- Source-clean view agrees with the loop's actual empty-cache view. -/
theorem clean_loop (s:S.Stack→List Bool) (edges ids:List Bool) :
    clean s edges ids=data s (fun _=>[]) (fun _=>[]) (rowAux edges ids []) := by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · cases k <;> rfl
/-- The actual N-only prefix supplies both real complete loop readers with no order/ID advice. -/
theorem ready_loop (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ready bits=data (SemiprimeD1StackRootScopeBankExecution.result bits) (fun _=>[]) (fun _=>[])
      (rowAux (SemiprimeD1StackOwnerCatalogueLoop.edgeTapeOf (pairs (bitValue bits)))
        (SemiprimeD1StackOwnerCatalogueLoop.idTapeOf (pairs (bitValue bits)) (unused (bitValue bits))) []) := by
  have he:edges bits=SemiprimeD1StackOwnerCatalogueLoop.edgeTapeOf (pairs (bitValue bits)):=by
    rw [original_edges]
    exact SemiprimeD1StackOwnerCatalogueOriginalMetadata.edges_original bits hc hN
  have hi:ids bits=SemiprimeD1StackOwnerCatalogueLoop.idTapeOf (pairs (bitValue bits)) (unused (bitValue bits)):=by
    rw [original_ids]
    exact SemiprimeD1StackOwnerCatalogueOriginalMetadata.id_reader_original bits
  unfold ready
  rw [he,hi,clean_loop]
/-- COMPLETE original-binary-N forward endpoint/owner catalogue acquisition.
All arithmetic keys, equality sentinels, owner words, joins, erasures and copies execute
inside THIS fixed finite source. No E-map, permutation, getter, answer or clock is supplied. -/
theorem source_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃time≤budget bits,C.run program time (initial bits)=some (done bits) := by
  let N:=bitValue bits
  let s:=SemiprimeD1StackRootScopeBankExecution.result bits
  obtain ⟨a,ha,har⟩:=acquisition_run bits hc hN
  rw [ready_loop bits hc hN] at har
  obtain ⟨b,hb,hbr⟩:=SemiprimeD1StackOwnerCatalogueLoop.loop_run
    (digitCount_bounds (bitLength_pos hN)).1 s (original_metadata bits hc hN) (pairs N) (unused N) []
  simp only [List.append_nil] at hbr
  have hf:=SemiprimeD1StackOwnerCatalogueFinish.finish_run s (unused N)
    (SemiprimeD1StackOwnerCatalogueLoop.bytes (pairs N)).reverse
  simp only [List.length_reverse,List.reverse_reverse] at hf
  have ht:=runs_trans program _ _ _ _ _ _ _ _ har (runs_trans program _ _ _ _ _ _ _ _ hbr hf)
  obtain ⟨finish,hr,hout⟩:=ht [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (.local .halt) rfl (done bits).data [] finish hout
  refine ⟨(a+(b+(2*(SemiprimeD1StackOwnerCatalogueLoop.bytes (pairs N)).length+7)))+1,?_,?_⟩
  · unfold budget
    dsimp only [N] at hb ⊢
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,hh]
    rfl
/-- The actually emitted complete N-only map is EXACTLY the original catalogue already used by lookup. -/
theorem output_original (bits:List Bool) (hN:0<bitValue bits) :
    (done bits).data (aux .output)=SemiprimeD1StackOwnerLookup.records
      (SemiprimeD1StackOwnerLookupOriginal.Public.catalogue (bitValue bits) hN) [] := by
  change SemiprimeD1StackOwnerCatalogueLoop.bytes (pairs (bitValue bits))++[false]=_
  exact original_bytes (bitValue bits) hN
end RiemannGaussian.SemiprimeD1StackOwnerCatalogueExecution
