/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerRecordsFinish
import RiemannGaussian.SemiprimeD1StackOwnerRecordsAcquisition
import RiemannGaussian.SemiprimeD1StackOwnerRecordOriginal
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerRecordsOriginal
open SemiprimeD1StackOwnerRecords SemiprimeD1StackOwnerRecordsView
open SemiprimeD1StackOwnerRecordsLoop SemiprimeD1StackOwnerRecordsAcquisition
open SemiprimeBitArithmetic (bitValue)
open SemiprimePublicAcquiredExecution (wireCount)
namespace O
export SemiprimeD1StackOwnerRecordOriginal (words degree vertex row_original)
export SemiprimeD1StackOwnerLookupOriginal.Public (encode)
end O
/-- ALL actual original owner fibres in increasing E-owner order, proof description only. -/
def originalRows (N:Nat) (hN:0<N) :List Row:=
  List.ofFn (fun e:Fin (wireCount N)=>⟨(O.encode N e,O.words N hN e),O.degree N hN e⟩)
/-- Every catalogue row is derived from actual original routing/filtering, with no scope/count advice. -/
theorem encoded_original (N:Nat) (hN:0<N) :
    encoded (originalRows N hN)=SemiprimeD1StackOwnerLookup.records
      (SemiprimeD1StackOwnerFibreCatalogueOriginal.ownerRows N hN) []:=by
  unfold encoded originalRows SemiprimeD1StackOwnerFibreCatalogueOriginal.ownerRows
  rw [List.map_ofFn]
  rfl
/-- Exact original fixed-prefix bytes; the physical source retains duplicates and conflicts. -/
def prefixRows (N:Nat) (fixed:List (Fin (wireCount N)×Bool)) :List (List Bool×Bool):=
  fixed.map (fun x=>(O.encode N x.1,x.2))
/-- Original owner vertex family with the unchanged incidence enumeration. -/
def vertices (N:Nat) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool)) :List SemiprimeD1LeafCounter.Vertex:=
  List.ofFn (O.vertex N hN fixed)
/-- Generic old record framing, proved before specializing the original graph. -/
theorem flatten_records (vs:List SemiprimeD1LeafCounter.Vertex) :
    (vs.map (fun v=>L.row (SemiprimeD1StackVertexReadExecution.portTape v.ports)
      (SemiprimeD1TensorTapeCodec.tape v.table))).flatten++[false]=
      SemiprimeD1StackVertexProduct.records vs:=by
  induction vs with
  | nil=>rfl
  | cons v vs ih=>
    simp only [List.map_cons,List.flatten_cons,List.append_assoc,ih]
    exact SemiprimeD1StackVertexRecordStream.row_records v vs
/-- Exact complete old product-reader bytes, including EVERY owner and final terminator. -/
theorem bytes_original (N:Nat) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool)) :
    bytes (originalRows N hN) (prefixRows N fixed)++[false]=
      SemiprimeD1StackVertexProduct.records (vertices N hN fixed):=by
  let newRow (e:Fin (wireCount N)):=rowBytes
    ⟨(O.encode N e,O.words N hN e),O.degree N hN e⟩ (prefixRows N fixed)
  let oldRow (v:SemiprimeD1LeafCounter.Vertex):=L.row
    (SemiprimeD1StackVertexReadExecution.portTape v.ports) (SemiprimeD1TensorTapeCodec.tape v.table)
  have each (e:Fin (wireCount N)) :newRow e=oldRow (O.vertex N hN fixed e):=
    O.row_original N hN fixed e []
  have hm:List.ofFn newRow=List.ofFn (fun e=>oldRow (O.vertex N hN fixed e)):=congrArg List.ofFn (funext each)
  have hn:bytes (originalRows N hN) (prefixRows N fixed)=(List.ofFn newRow).flatten:=by
    unfold bytes originalRows
    rw [List.map_ofFn]
    rfl
  have ho:(List.ofFn (fun e=>oldRow (O.vertex N hN fixed e))).flatten=
      ((vertices N hN fixed).map oldRow).flatten:=by
    unfold vertices
    rw [List.map_ofFn]
    rfl
  calc
    _=(List.ofFn newRow).flatten++[false]:=congrArg (fun raw:List Bool=>raw++[false]) hn
    _=(List.ofFn (fun e=>oldRow (O.vertex N hN fixed e))).flatten++[false]:=
      congrArg (fun rows:List (List Bool)=>rows.flatten++[false]) hm
    _=((vertices N hN fixed).map oldRow).flatten++[false]:=congrArg (fun raw:List Bool=>raw++[false]) ho
    _=_:=flatten_records (vertices N hN fixed)
/-- The actual copied source catalogue is EXACT this derived all-owner row sequence. -/
theorem catalogue_original (bits:List Bool) (hN:0<bitValue bits) :
    catalogueBytes bits hN=encoded (originalRows (bitValue bits) hN):=by
  rw [encoded_original]
  exact SemiprimeD1StackOwnerFibreCatalogueExecution.output_original bits hN
/-- Original source acquisition reaches the literal loop invariant for ALL original E owners. -/
theorem ready_original (bits pre:List Bool) (hN:0<bitValue bits) :
    ready bits hN pre=data (SemiprimeD1StackOwnerFibreCatalogueExecution.done bits hN).data
      (payload [] [] [] [] [false]) (rowAux (encoded (originalRows (bitValue bits) hN)) pre):=by
  unfold ready
  rw [catalogue_original]
end RiemannGaussian.SemiprimeD1StackOwnerRecordsOriginal
