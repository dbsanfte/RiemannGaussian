/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordBounds
/-! # Original all-family Boolean descriptor dispatch and exact leaf records
All ten original tags8..17 are covered, with arbitrary typed coordinates.
Descriptor production and ordered binary scope acquisition remain caller work.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordOriginal
open SemiprimeD1StackBooleanDescriptorRecord SemiprimeD1StackBooleanDescriptorRecordEncoding
open SemiprimeD1StackBooleanDescriptorRecordExecution
open SemiprimeMacroGraph
namespace E
export SemiprimeD1EdgeCatalogueEncoding (vertex)
end E
namespace B
export SemiprimeD1StackBooleanRecordOriginal (Matches matches_or matches_input matches_equality vertex)
end B
namespace Log
export SemiprimeD1StackVertexRecordStreamExecution (history)
end Log
/-- Proof-only classification of the original Boolean vertices; the program
instead parses and consumes the actual five-field descriptor. -/
def originalMode {r t digits : Nat} : SubdividedVertex r t digits → Option SemiprimeD1StackBooleanEntry.Mode
  | .inl (.orGate _ _) => some .orGate
  | .inl (.inputCheck _) => some .inputCheck
  | .inr _ => some .equality
  | _ => none
/-- Every original Boolean vertex's actual tag selects exactly its correct
literal table, including all eight equality subfamilies and all coordinates. -/
theorem original_dispatch (N : Nat) (hN : 0<N) (v : SemiprimePublicAcquiredExecution.PublicVertex N)
    (mode : SemiprimeD1StackBooleanEntry.Mode) (hm:originalMode v=some mode) :
    ∃code : Fin 18,(E.vertex v 0)=List.replicate code.val true ∧
      dispatch code=.local (.record mode) ∧ B.Matches N hN mode v := by
  cases v with
  | inl v=>cases v with
    | input side i=>cases hm
    | first tr j=>cases hm
    | scale tr j k=>cases hm
    | second tr k=>cases hm
    | product i=>cases hm
    | carryInitial=>cases hm
    | carry i=>cases hm
    | carryTerminal=>cases hm
    | orGate side j=>
      have he:mode=.orGate:=Option.some.inj hm.symm
      subst mode
      exact ⟨8,rfl,rfl,B.matches_or N hN side j⟩
    | inputCheck side=>
      have he:mode=.inputCheck:=Option.some.inj hm.symm
      subst mode
      exact ⟨9,rfl,rfl,B.matches_input N hN side⟩
  | inr signal=>
    have he:mode=.equality:=Option.some.inj hm.symm
    subst mode
    have hmatch:=B.matches_equality N hN signal
    rcases signal with ⟨word,bit⟩|flag
    · cases word with
      | input side i=>exact ⟨10,rfl,rfl,hmatch⟩
      | first tr j k=>exact ⟨11,rfl,rfl,hmatch⟩
      | twiddle tr j k=>exact ⟨12,rfl,rfl,hmatch⟩
      | second tr k j=>exact ⟨13,rfl,rfl,hmatch⟩
      | product i=>exact ⟨14,rfl,rfl,hmatch⟩
      | carry i=>exact ⟨15,rfl,rfl,hmatch⟩
    · cases flag with
      | digit side i=>exact ⟨16,rfl,rfl,hmatch⟩
      | orOut side i=>exact ⟨17,rfl,rfl,hmatch⟩
/-- The caller's unread descriptor suffix survives exactly, with no free re-encoding. -/
theorem retained_suffix (mode : SemiprimeD1StackBooleanEntry.Mode) (w : Record) (tail : List Bool)
    (scope : List (List Bool)) (hist out : List Bool) :
    (done mode w tail scope hist out).data (aux .reader)=tail := rfl
/-- All five physically parsed fields survive, including the copied original tag. -/
theorem retained_field (mode : SemiprimeD1StackBooleanEntry.Mode) (w : Record) (tail : List Bool)
    (scope : List (List Bool)) (hist out : List Bool) (part : Fin 5) :
    (done mode w tail scope hist out).data (cache part)=w part := rfl
/-- The actual binary occurrence-ID bank survives the complete dispatched row acquisition. -/
theorem retained_scope (mode : SemiprimeD1StackBooleanEntry.Mode) (w : Record) (tail : List Bool)
    (scope : List (List Bool)) (hist out : List Bool) :
    (done mode w tail scope hist out).data (.inl SemiprimeD1StackBooleanRecord.original)=
      SemiprimeD1TensorTapeCodec.vectorBits scope := rfl
/-- Physical parser/tag dispatch and the exact old chronological leaf row hold
together for EVERY original Boolean descriptor, not a finite sample family. -/
theorem source_run_original (N : Nat) (hN : 0<N) (v : SemiprimePublicAcquiredExecution.PublicVertex N)
    (mode : SemiprimeD1StackBooleanEntry.Mode) (hm:originalMode v=some mode) (M : Nat) (ports : List Nat)
    (hp:∀i∈ports,i<M) (hlen:ports.length=subdividedArity v)
    (tail : List Bool) (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    ∃code : Fin 18,∃t ≤ timeBound code (E.vertex v) mode
        (ports.map (SemiprimeD1OrdinalBankSpec.idAt M)),
      C.run program t
        (initial (SemiprimeD1VertexCatalogueEncoding.vertex v tail)
          (SemiprimeD1TensorTapeCodec.vectorBits (ports.map (SemiprimeD1OrdinalBankSpec.idAt M)))
          (Log.history previous old) out)=
        some (done mode (E.vertex v) tail (ports.map (SemiprimeD1OrdinalBankSpec.idAt M))
          (Log.history previous old) out) ∧
      (done mode (E.vertex v) tail (ports.map (SemiprimeD1OrdinalBankSpec.idAt M))
        (Log.history previous old) out).data (.inl R.history)=
          Log.history (previous++[B.vertex N hN v ports hlen]) old := by
  obtain ⟨code,htag,hd,hmatches⟩:=original_dispatch N hN v mode hm
  obtain ⟨t,ht,hr⟩:=source_run code (E.vertex v) tail mode htag hd
    (ports.map (SemiprimeD1OrdinalBankSpec.idAt M)) (Log.history previous old) out
  refine ⟨code,t,ht,?_,?_⟩
  · simpa only [record_vertex] using hr
  · exact SemiprimeD1StackBooleanRecordOriginal.history_original N hN v mode hmatches M ports hp hlen previous old out
/-- Uniform actual original-row time bound with only linear descriptor overhead.
Original occurrence-ID padding and conversion costs are retained explicitly. -/
theorem original_timeBound (N : Nat) (hN : 0<N) (v : SemiprimePublicAcquiredExecution.PublicVertex N)
    (mode : SemiprimeD1StackBooleanEntry.Mode) (hm:originalMode v=some mode) (M : Nat) (ports : List Nat)
    (hp:∀i∈ports,i<M) :
    ∃code : Fin 18,timeBound code (E.vertex v) mode (ports.map (SemiprimeD1OrdinalBankSpec.idAt M)) ≤
      110*(ports.length+1)*(M+1)+7*(SemiprimeD1VertexCatalogueEncoding.vertex v []).length+222 := by
  obtain ⟨code,htag,_,_⟩:=original_dispatch N hN v mode hm
  have h:=SemiprimeD1StackBooleanDescriptorRecordBounds.timeBound_le_descriptor code (E.vertex v) mode
    (ports.map (SemiprimeD1OrdinalBankSpec.idAt M)) htag
  have hs:=SemiprimeD1StackBooleanRecordOriginal.selected_timeBound mode M ports hp
  rw [record_vertex] at h
  exact ⟨code,by omega⟩
end RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordOriginal
