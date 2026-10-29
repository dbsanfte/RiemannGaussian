/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerRecordBounds
import RiemannGaussian.SemiprimeD1StackOwnerFibreOriginal
/-! # Actual owner row equals the original owner node in indexed occurrence order -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 32768
namespace RiemannGaussian.SemiprimeD1StackOwnerRecordOriginal
open SemiprimeD1StackOwnerRecord SemiprimeD1StackOwnerRecordExecution
open SemiprimePublicAcquiredExecution (wireCount)
open SemiprimeD1RootTensorTables (ownerNode ownerPorts acquirePositive Port)
namespace F
export SemiprimeD1StackOwnerFibreOriginal (enumeration scopeWord scopeWord_value rows original_fibre original_owner_table)
export SemiprimeD1StackOwnerFibre (values)
end F
namespace O
export SemiprimeD1StackOwnerLookupOriginal.Public (encode)
end O
/-- Proof description of ACTUAL binary scopes acquired by the N-only fibre source. -/
abbrev words (N : Nat) (hN : 0<N) (e : Fin (wireCount N)) : List (List Bool) :=
  F.values (O.encode N e) (F.rows N hN)
/-- The physical table bound is discharged by the actual original graph. -/
theorem degree (N : Nat) (hN : 0<N) (e : Fin (wireCount N)) : (words N hN e).length≤2 := by
  rw [words,F.original_fibre N hN [] e,List.length_map]
  exact SemiprimeD1RootTensorTablesBounds.owner_degree_le N hN [] e
/-- Generic dimension cast is proved with an opaque node variable, before specialization. -/
def mappedVertex {I:Type} (code:I→Nat) (node:SemiprimeD1RootTensorTables.Node I) :
    SemiprimeD1LeafCounter.Vertex:=
  ⟨node.ports.map code,cast (congrArg SemiprimeD1TensorTables.Table
    (List.length_map (as:=node.ports) code).symm) node.table⟩
theorem tape_cast {m n : Nat} (h : m=n) (t : SemiprimeD1TensorTables.Table m) :
    SemiprimeD1TensorTapeCodec.tape (cast (congrArg SemiprimeD1TensorTables.Table h) t)=
      SemiprimeD1TensorTapeCodec.tape t := by cases h;rfl
theorem mapped_table {I:Type} (code:I→Nat) (node:SemiprimeD1RootTensorTables.Node I) :
    SemiprimeD1TensorTapeCodec.tape (mappedVertex code node).table=SemiprimeD1TensorTapeCodec.tape node.table:=
  tape_cast (List.length_map (as:=node.ports) code).symm node.table
/-- Original owner node with ports named by the unchanged incidence enumeration. -/
def vertex (N : Nat) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (e : Fin (wireCount N)) : SemiprimeD1LeafCounter.Vertex :=
  mappedVertex (fun p:Port N=>((F.enumeration N).equivFin.symm p).val)
    (ownerNode N fixed (acquirePositive N hN fixed).records e)
/-- Actual binary-to-unary conversion yields EXACT original global port ordinals. -/
theorem ports_original (N : Nat) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (e : Fin (wireCount N)) : S.result (words N hN e)=
      SemiprimeD1StackVertexReadExecution.portTape (vertex N hN fixed e).ports := by
  rw [SemiprimeD1StackPortOrdinalStreamOriginal.result_portTape,words,F.original_fibre N hN fixed e,List.map_map]
  apply congrArg SemiprimeD1StackVertexReadExecution.portTape
  apply List.map_congr_left
  intro p _
  exact F.scopeWord_value N p
/-- Actual prefix scan and palette write the ENTIRE original owner tensor table. -/
theorem table_original (N : Nat) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (e : Fin (wireCount N)) (tail : List Bool) :
    table (O.encode N e) (fixed.map (fun x=>(O.encode N x.1,x.2))) tail (words N hN e) (degree N hN e)=
      SemiprimeD1TensorTapeCodec.tape (vertex N hN fixed e).table := by
  obtain ⟨hs,ht⟩:=F.original_owner_table N hN fixed e tail
  calc
    _=SemiprimeD1TensorTapeCodec.tape (ownerNode N fixed (acquirePositive N hN fixed).records e).table:=by
      simpa only [words,table] using ht
    _=_:=(mapped_table (fun p:Port N=>((F.enumeration N).equivFin.symm p).val)
      (ownerNode N fixed (acquirePositive N hN fixed).records e)).symm
/-- Physical framing/logging is EXACT frozen original owner-record framing. -/
theorem row_original (N : Nat) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (e : Fin (wireCount N)) (tail : List Bool) :
    R.row (S.result (words N hN e))
      (table (O.encode N e) (fixed.map (fun x=>(O.encode N x.1,x.2))) tail (words N hN e) (degree N hN e))=
      R.row (SemiprimeD1StackVertexReadExecution.portTape (vertex N hN fixed e).ports)
        (SemiprimeD1TensorTapeCodec.tape (vertex N hN fixed e).table) := by
  rw [ports_original N hN fixed e,table_original N hN fixed e tail]
/-- Complete actual source preserves previous rows and all duplicate/conflicting prefix assignments. -/
theorem source_run_original (N : Nat) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (e : Fin (wireCount N)) (tail hist out : List Bool) :
    ∃t≤timeBound (O.encode N e) (fixed.map (fun x=>(O.encode N x.1,x.2))) (words N hN e) (degree N hN e),
      C.run program t (initial (O.encode N e)
        (SemiprimeD1OwnerPrefixBits.records (fixed.map (fun x=>(O.encode N x.1,x.2))) tail)
        (SemiprimeD1TensorTapeCodec.vectorBits (words N hN e)) hist out)=
        some (done (O.encode N e) (fixed.map (fun x=>(O.encode N x.1,x.2))) tail
          (words N hN e) (degree N hN e) hist out) :=
  source_run _ _ _ _ _ _ _
end RiemannGaussian.SemiprimeD1StackOwnerRecordOriginal
