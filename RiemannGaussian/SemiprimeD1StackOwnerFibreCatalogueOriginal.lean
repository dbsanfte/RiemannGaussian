/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueLoop
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueOriginal
open SemiprimeD1StackOwnerFibreCatalogue SemiprimeD1StackOwnerFibreCatalogueSource
open SemiprimeD1StackOwnerFibreCatalogueView
open SemiprimeD1StackOwnerFibreCatalogueLoop (idTape)
open SemiprimePublicAcquiredExecution
open SemiprimeD1OrdinalBankSpec (words idAt)
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace Owner
export SemiprimeD1StackOwnerLookupOriginal.Public (encode occurrences_eq encode_value)
end Owner
/-- ONLY the first actual E bank words are read as owner queries; the bank still has M=2E entries. -/
def queries (N:Nat) :List (List Bool):=(words (2*wireCount N)).take (wireCount N)
/-- ACTUAL remaining M-E bank suffix after all real original owners. -/
def unused (N:Nat) :List Bool:=vectorBits ((words (2*wireCount N)).drop (wireCount N))
/-- Exactly E actual words are read; no E=M identification is needed. -/
theorem queries_length (N:Nat) :(queries N).length=wireCount N:=by
  simp only [queries,List.length_take,SemiprimeD1OrdinalBankSpec.length];omega
/-- Prefix plus untouched suffix reconstructs the WHOLE physically acquired M bank. -/
theorem id_reader_original (N:Nat) :idTape (queries N) (unused N)=vectorBits (words (2*wireCount N)):=by
  unfold idTape queries unused
  rw [SemiprimeD1StackOwnerCatalogueOriginalIds.vector_append,List.take_append_drop]
/-- Source bank prefix is the original public E-wire encoding in ordinal order. -/
theorem queries_encoded (N:Nat) (hN:0<N) :
    queries N=List.ofFn (fun e:Fin (wireCount N)=>Owner.encode N e):=by
  apply List.ext_getElem
  · rw [queries_length,List.length_ofFn]
  · intro i hi hj
    have hiE:i<wireCount N:=by simpa only [queries_length] using hi
    have hiM:i<(words (2*wireCount N)).length:=by rw [SemiprimeD1OrdinalBankSpec.length];omega
    simp only [queries,List.getElem_take,List.getElem_ofFn,Owner.encode,Owner.occurrences_eq N hN]
    unfold idAt
    rw [List.getElem?_eq_getElem hiM,Option.getD_some]
/-- Complete original owner/fibre row family, as a proof description of real emitted fields. -/
def ownerRows (N:Nat) (hN:0<N) :List (List Bool×List Bool):=
  List.ofFn (fun e:Fin (wireCount N)=>(Owner.encode N e,
    SemiprimeD1StackOwnerFibreCatalogueRow.scopes (Owner.encode N e) (SemiprimeD1StackOwnerFibreOriginal.rows N hN)))
/-- Both fields at EVERY owner are EXACT original owner key and original ordered occurrence fibre.
The arbitrary original fixed prefix changes no scope order or fibre membership. -/
theorem owner_entry (N:Nat) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool)) (e:Fin (wireCount N)) :
    (ownerRows N hN)[e.val]'(by simp only [ownerRows,List.length_ofFn];exact e.isLt)=
      (Owner.encode N e,vectorBits ((SemiprimeD1RootTensorTables.ownerPorts N
        (SemiprimeD1RootTensorTables.acquirePositive N hN fixed).records e).map
          (SemiprimeD1StackOwnerFibreOriginal.scopeWord N))):=by
  simp only [ownerRows,List.getElem_ofFn,SemiprimeD1StackOwnerFibreCatalogueRow.scopes]
  rw [SemiprimeD1StackOwnerFibreOriginal.original_fibre N hN fixed e]
/-- Actual emitted catalogue bytes are EXACT all-original owner/fibre records. -/
theorem original_bytes (N:Nat) (hN:0<N) :
    SemiprimeD1StackOwnerFibreCatalogueLoop.bytes (queries N) (SemiprimeD1StackOwnerFibreOriginal.rows N hN)++[false]=
      SemiprimeD1StackOwnerLookup.records (ownerRows N hN) []:=by
  rw [SemiprimeD1StackOwnerFibreCatalogueLoop.bytes_records,queries_encoded N hN,List.map_ofFn]
  rfl
/-- Two different syntactic descriptions of the SAME actually fresh owner-loop work. -/
theorem clean_loop (s:R.Stack→List Bool) (count ids:List Bool) :clean s count ids=data s (fun _=>[]) (rowAux count ids []):=by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Complete N-only acquisition supplies EXACT original E-loop tally and actual whole M-bank reader. -/
theorem ready_original (bits:List Bool) (hN:0<SemiprimeBitArithmetic.bitValue bits) :
    ready bits hN=data (SemiprimeD1StackPortOwnerRoutingExecution.done bits hN).data (fun _=>[])
      (rowAux (List.replicate (queries (SemiprimeBitArithmetic.bitValue bits)).length true)
        (idTape (queries (SemiprimeBitArithmetic.bitValue bits)) (unused (SemiprimeBitArithmetic.bitValue bits))) []):=by
  unfold ready
  rw [queries_length,id_reader_original,clean_loop]
  have hc:countBytes bits hN=List.replicate (wireCount (SemiprimeBitArithmetic.bitValue bits)) true:=original_count bits hN
  have hi:idBytes bits hN=vectorBits (words (2*wireCount (SemiprimeBitArithmetic.bitValue bits))):=original_ids bits hN
  rw [hc,hi]
end RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueOriginal
