/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortScopePrimitives
import RiemannGaussian.SemiprimeD1PortScopeEncoding
/-! # Original-N source and physical cache copies for scope-tagged port records -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortScopeSource
open SemiprimeD1StackPortScopeRecords SemiprimeD1StackPortScopeComponents
open SemiprimeD1StackPortScopePrimitives
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Exact completed original-N port-and-ID source store, physically retained. -/
def base (bits:List Bool) : S.Stack→List Bool := SemiprimeD1StackPortOrdinalBankExecution.result bits
/-- Exact ordered original source records, a proof-side specification only. -/
def ports (bits:List Bool) := SemiprimeD1PortScopeEncoding.ports
  (SemiprimeD1StackPortCatalogueExecution.vertices bits) 0 0
/-- Exact physically counter-generated word sequence; never an argument to the caller. -/
def ids (bits:List Bool) : List (List Bool) := SemiprimeD1OrdinalBankSpec.words
  (SemiprimeD1StackPortOrdinalBankExecution.occurrences bits)
/-- Actual entry after the real nested original-N acquisition. -/
def afterSource (bits:List Bool) : Stack→List Bool := Sum.elim (base bits) (fun _=>[])
/-- Actual first copied reader, preserving all original source bytes. -/
def afterPorts (bits:List Bool) : Stack→List Bool :=
  Function.update (afterSource bits) (aux .readerPorts) (SemiprimeD1PortScopeEncoding.portTape (ports bits) [])
/-- Actual two copied readers, no input tape or index array supplied as advice. -/
def afterCopies (bits:List Bool) : Stack→List Bool :=
  Function.update (afterPorts bits) (aux .readerIds) (vectorBits (ids bits))
/-- Acquired port records and acquired ID count agree because BOTH came from the same executed tally. -/
theorem lengths (bits:List Bool) : (ports bits).length=(ids bits).length := by
  rw [ports,SemiprimeD1PortScopeEncoding.ports_length,ids,SemiprimeD1OrdinalBankSpec.length]
  rfl
/-- Actual retained source port bytes are in exact original factor-major order. -/
theorem source_ports (bits:List Bool) : afterSource bits sourcePorts=
    SemiprimeD1PortScopeEncoding.portTape (ports bits) [] := by
  change SemiprimeD1StackPortOrdinalBankExecution.result bits
    (S.portStack (SemiprimeD1StackPortCatalogue.aux .output))=_
  rw [SemiprimeD1StackPortOrdinalBankExecution.retained_port]
  change SemiprimeD1StackPortCatalogueTransduction.output
    (SemiprimeD1StackPortCatalogueExecution.vertices bits) 0 0 []=_
  exact (SemiprimeD1PortScopeEncoding.ports_tape _ _ _ _).symm
/-- Actual ID-bank bytes are produced by its physical counter, with no padded-word oracle. -/
theorem source_ids (bits:List Bool) : afterSource bits sourceIds=vectorBits (ids bits) :=
  SemiprimeD1StackPortOrdinalBankExecution.ids_value bits
/-- The actual whole source is called ONCE from binary N and keeps fresh work empty. -/
theorem source_call (bits:List Bool) (hb:bits≠[]) :
    ∃ time ≤ 10^104*(bits.length+1)^30+1,
      Runs program time (.local .main) (input bits) (.local .copyPorts) (afterSource bits) := by
  obtain ⟨m,hm,hr⟩:=SemiprimeD1StackPortOrdinalBankBounds.source_run_polynomial bits hb
  refine ⟨m+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program sourceStack Label.source sourceStack_injective
    S.program (.inl .start) (fun _=>rfl) (.local .main) (.local .copyPorts) rfl m
    (SemiprimeD1StackPortOrdinalBank.initial bits) (SemiprimeD1StackPortOrdinalBankExecution.done bits)
    (input bits) (afterSource bits)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      cases k with
      | inl k => exact False.elim (hk k rfl)
      | inr k => rfl
/-- Actual source-preserving copy of the WHOLE original port tape. -/
theorem ports_copy (bits:List Bool) :
    Runs program (5*(SemiprimeD1PortScopeEncoding.portTape (ports bits) []).length+4)
      (.local .copyPorts) (afterSource bits) (.local .copyIds) (afterPorts bits) := by
  have h:=copy_call false (afterSource bits) (.local .copyPorts) (.local .copyIds) rfl rfl
  change Runs program (5*(afterSource bits sourcePorts).length+4) _ _ _
    (Function.update (afterSource bits) (aux .readerPorts)
      (afterSource bits sourcePorts++afterSource bits (aux .readerPorts))) at h
  rw [source_ports,show afterSource bits (aux .readerPorts)=[] from rfl,List.append_nil] at h
  exact h
/-- Actual source-preserving copy of the WHOLE physical ID-vector; no per-port rescanning. -/
theorem ids_copy (bits:List Bool) :
    Runs program (5*(vectorBits (ids bits)).length+4)
      (.local .copyIds) (afterPorts bits) (.local .parse) (afterCopies bits) := by
  have h:=copy_call true (afterPorts bits) (.local .copyIds) (.local .parse) rfl rfl
  have hi:afterPorts bits sourceIds=vectorBits (ids bits):=by
    change Function.update (afterSource bits) (aux .readerPorts)
      (SemiprimeD1PortScopeEncoding.portTape (ports bits) []) sourceIds=_
    rw [Function.update_of_ne (by decide : sourceIds≠aux .readerPorts)]
    exact source_ids bits
  change Runs program (5*(afterPorts bits sourceIds).length+4) _ _ _
    (Function.update (afterPorts bits) (aux .readerIds)
      (afterPorts bits sourceIds++afterPorts bits (aux .readerIds))) at h
  rw [hi,show afterPorts bits (aux .readerIds)=[] from rfl,List.append_nil] at h
  exact h
end RiemannGaussian.SemiprimeD1StackPortScopeSource
