/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerRecordsLog
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerRecordsAcquisition
open SemiprimeD1StackOwnerRecords SemiprimeD1StackOwnerRecordsView SemiprimeD1StackOwnerRecordsCalls
open SemiprimeD1StackOwnerRecordsLog
open SemiprimeD1StackProcedureTrace (Runs runs_trans one_base)
open SemiprimeBitArithmetic (bitValue)
/-- Proof-side ZERO fresh record store, including every alias shadow. -/
theorem payload_nil :payload [] [] [] [] []=fun _=>[]:=by funext k;fin_cases k <;> rfl
/-- Actual source cataloguing the whole original E-family is called exactly once. -/
theorem source_call (bits pre:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃time≤SemiprimeD1StackOwnerFibreCatalogueBounds.polynomial bits.length+1,
      Runs program time (.local .main) (initialPrefix bits pre).data (.local .copyCatalogue)
        (data (SemiprimeD1StackOwnerFibreCatalogueExecution.done bits hN).data
          (payload [] [] [] [] []) (rowAux [] pre)):=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackOwnerFibreCatalogueBounds.source_run_polynomial bits hc hN
  refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
  rw [payload_nil]
  apply SemiprimeD1StackProcedureInclusion.included_call program source Label.source Sum.inl_injective
    S.program (.local .main) (fun _=>rfl) (.local .main) (.local .copyCatalogue) rfl t
    (SemiprimeD1StackOwnerFibreCatalogue.initial bits)
    (SemiprimeD1StackOwnerFibreCatalogueExecution.done bits hN) _ _ rfl rfl rfl rfl hr
  · exact ⟨fun _=>rfl,fun _ _=>rfl⟩
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact False.elim (hk k rfl)
      · rfl
/-- Real preserving whole catalogue copy into the actual physical reader. -/
theorem catalogue_copy (s:S.Stack→List Bool) (pre:List Bool) :
    Runs program (5*(s (SemiprimeD1StackOwnerFibreCatalogue.aux .output)).length+4) (.local .copyCatalogue)
      (data s (payload [] [] [] [] []) (rowAux [] pre)) (.local .initialize)
      (data s (payload [] [] [] [] [])
        (rowAux (s (SemiprimeD1StackOwnerFibreCatalogue.aux .output)) pre)):=by
  have h:=copy_call false (data s (payload [] [] [] [] []) (rowAux [] pre))
    (.local .copyCatalogue) (.local .initialize) rfl rfl
  change Runs program _ _ _ _ (Function.update _ (aux .reader)
    (s (SemiprimeD1StackOwnerFibreCatalogue.aux .output)++[])) at h
  rw [List.append_nil,update_aux] at h
  have he:Function.update (rowAux [] pre) .reader (s (SemiprimeD1StackOwnerFibreCatalogue.aux .output))=
      rowAux (s (SemiprimeD1StackOwnerFibreCatalogue.aux .output)) pre:=by funext k;cases k <;> rfl
  rwa [he] at h
/-- Actual retained catalogue bytes, acquired from N and THEN copied, never supplied. -/
def catalogueBytes (bits:List Bool) (hN:0<bitValue bits) :List Bool:=
  (SemiprimeD1StackOwnerFibreCatalogueExecution.done bits hN).data (SemiprimeD1StackOwnerFibreCatalogue.aux .output)
/-- Exact reached loop store after actual N acquisition, catalogue copy and sentinel initialization. -/
def ready (bits:List Bool) (hN:0<bitValue bits) (pre:List Bool) :Stack→List Bool:=
  data (SemiprimeD1StackOwnerFibreCatalogueExecution.done bits hN).data
    (payload [] [] [] [] [false]) (rowAux (catalogueBytes bits hN) pre)
/-- Paid whole N-only source call, preserving catalogue copy and logger initialization allowance. -/
def acquisitionBudget (bits:List Bool) (hN:0<bitValue bits) :Nat:=
  SemiprimeD1StackOwnerFibreCatalogueBounds.polynomial bits.length+5*(catalogueBytes bits hN).length+8
/-- N-only full catalogue source, actual byte copy and real OUTPUT sentinel initialization. -/
theorem acquisition_run (bits pre:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃time≤acquisitionBudget bits hN,Runs program time (.local .main)
      (initialPrefix bits pre).data (.local .loop) (ready bits hN pre):=by
  obtain ⟨t,ht,h0⟩:=source_call bits pre hc hN
  have h1:=catalogue_copy (SemiprimeD1StackOwnerFibreCatalogueExecution.done bits hN).data pre
  have h2:=initialize_call (SemiprimeD1StackOwnerFibreCatalogueExecution.done bits hN).data
    (rowAux (catalogueBytes bits hN) pre)
  refine ⟨t+(5*(catalogueBytes bits hN).length+4)+3,?_,?_⟩
  · unfold acquisitionBudget;omega
  · exact runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
/-- The empty-prefix machine physically pushes its sole false byte before acquisition. -/
theorem empty_seed (bits:List Bool) :
    Runs program 1 (.local .empty) (initial bits).data (.local .main) (initialPrefix bits [false]).data:=by
  apply one_base program _ _ (.push (aux .prefixBytes) false (.local .main)) _ _ rfl rfl
  simp only [SemiprimeD1StackBytecode.execute,initial,initialPrefix,update_aux]
  congr 1;funext k;cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackOwnerRecordsAcquisition
