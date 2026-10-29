/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsTables
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsExecution
/-! # Marked root network with the EXACT old topology and ordered acquired tables
This is a mathematical specification of actual2011 output bytes. It invokes
no source acquisition clock and supplies no operand to the literal program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsNetwork
open SemiprimeD1TensorTables SemiprimeD1TensorTapeCodec
open SemiprimeD1StackMarkedRootRecordsEncoding SemiprimeD1StackMarkedRootRecordsAlignment
open SemiprimePublicAcquiredExecution (factorCount)
open SemiprimeBitArithmetic (bitValue)
namespace New
export SemiprimeD1StackMarkedPublicInputTableOriginal (reference)
end New
/-- Complete ordered marked factor vertex; original numeric port names are unchanged. -/
noncomputable def factor (N : Nat) (hN : 0 < N) (f : Fin (factorCount N)) : SemiprimeD1LeafCounter.Vertex :=
  ⟨SemiprimeD1BooleanFactorCatalogueIndicesOriginal.numericPorts N f,
    cast (congrArg Table (SemiprimeD1StackFullFactorCatalogueOriginal.numeric_arity N f).symm)
      (New.reference N hN (SemiprimeD1BooleanFactorCatalogueIndices.vertex N f))⟩
/-- Complete original factor order with only the actual stored table changed. -/
noncomputable def factors (N : Nat) (hN : 0 < N) (fs : List (Fin (factorCount N))) :
    List SemiprimeD1LeafCounter.Vertex := fs.map (factor N hN)
/-- A proof-only dimension cast does not alter canonical word shape. -/
theorem good_cast (ctx : SemiprimeD1JetAxes.Context) {m n : Nat} (h : m=n) (table : Table m)
    (hg : Good ctx table) : Good ctx (cast (congrArg Table h) table) := by cases h;exact hg
/-- Every complete new factor table is Good at the actual new public precision. -/
theorem factor_good (N : Nat) (hN : 0 < N) (f : Fin (factorCount N)) :
    Good ⟨[],SemiprimeD1PackedMomentPrecision.precision N⟩ (factor N hN f).table :=
  good_cast _ (SemiprimeD1StackFullFactorCatalogueOriginal.numeric_arity N f).symm _
    (SemiprimeD1StackMarkedRootRecordsTables.marked_good N hN _)
/-- Each new factor has EXACTLY the old ordered numeric occurrence port list. -/
theorem factor_ports (N : Nat) (hN : 0 < N) (f : Fin (factorCount N)) :
    (factor N hN f).ports=(SemiprimeD1StackFullFactorCatalogueOriginal.localVertex N hN f).ports := rfl
/-- The physically emitted row is the exact whole marked original factor row. -/
theorem row_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits)
    (f : Fin (factorCount (bitValue bits))) :
    newRow bits (originalRow (bitValue bits) hN f)=
      SemiprimeD1StackVertexRecordStream.row (SemiprimeD1StackVertexReadExecution.portTape (factor (bitValue bits) hN f).ports)
        (tape (factor (bitValue bits) hN f).table) := by
  unfold newRow
  rw [SemiprimeD1StackMarkedRootRecordsTables.original_table bits hc hN f]
  change SemiprimeD1StackVertexRecordStream.row _ _=SemiprimeD1StackVertexRecordStream.row _
    (tape (cast (congrArg Table (SemiprimeD1StackFullFactorCatalogueOriginal.numeric_arity (bitValue bits) f).symm) _))
  have h := SemiprimeD1StackBooleanRecordOriginal.tape_cast
    (SemiprimeD1StackFullFactorCatalogueOriginal.numeric_arity (bitValue bits) f).symm
    (New.reference (bitValue bits) hN (SemiprimeD1BooleanFactorCatalogueIndices.vertex (bitValue bits) f))
  exact congrArg (fun bytes => SemiprimeD1StackVertexRecordStream.row
    (SemiprimeD1StackVertexReadExecution.portTape (factor (bitValue bits) hN f).ports) bytes) h.symm
/-- Every factor record, not merely its integer value, is in exact original order. -/
theorem records_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits)
    (fs : List (Fin (factorCount (bitValue bits)))) :
    payload bits (originalRows (bitValue bits) hN fs)++[false]=
      SemiprimeD1StackVertexProduct.records (factors (bitValue bits) hN fs) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    change (newRow bits (originalRow (bitValue bits) hN f)++payload bits (originalRows (bitValue bits) hN fs))++[false]=_
    rw [List.append_assoc,ih,row_original bits hc hN f]
    exact SemiprimeD1StackVertexRecordStream.row_records _ _
/-- The original cached topology is reused verbatim, including all isolated owners. -/
abbrev old (N : Nat) (hN : 0 < N) := SemiprimeD1RootStateResources.root N hN []
/-- Actual right-vector length agrees with the old original factor count. -/
theorem old_right_length (N : Nat) (hN : 0 < N) : (old N hN).rows.length=factorCount N :=
  SemiprimeD1RootNetwork.rows_length _
/-- Named marked mathematical network: only right tensor tables change, never topology. -/
noncomputable def network (N : Nat) (hN : 0 < N) : SemiprimeD1TensorNetwork.Network :=
  { old N hN with right := Vector.ofFn (fun i => factor N hN (Fin.cast (old_right_length N hN) i)) }
/-- Owner count is definitionally the SAME original count. -/
theorem leftCount_eq (N : Nat) (hN : 0 < N) : (network N hN).leftCount=(old N hN).leftCount := rfl
/-- Explicit typed row transport before any original acquired graph is instantiated. -/
def rowsAt (base next : SemiprimeD1TensorNetwork.Network) (h : next.leftCount=base.leftCount) :
    SemiprimeD1TensorNetwork.Rows base.leftCount := cast (congrArg SemiprimeD1TensorNetwork.Rows h) next.rows
/-- Explicit typed owner-vector transport before concrete original graph instantiation. -/
def leftAt (base next : SemiprimeD1TensorNetwork.Network) (h : next.leftCount=base.leftCount) :
    Vector SemiprimeD1LeafCounter.Vertex base.leftCount := cast (congrArg (Vector SemiprimeD1LeafCounter.Vertex) h) next.left
/-- Cached factor-major owner rows are exactly unchanged under their explicit count transport. -/
theorem rows_eq (N : Nat) (hN : 0 < N) : rowsAt (old N hN) (network N hN) (leftCount_eq N hN)=(old N hN).rows := rfl
/-- All original owner tensor words are reused byte-for-byte under the same explicit transport. -/
theorem left_eq (N : Nat) (hN : 0 < N) : leftAt (old N hN) (network N hN) (leftCount_eq N hN)=(old N hN).left := rfl
/-- Scalar row counts agree without elaborating equality between concrete dependent row types. -/
theorem rows_length_eq (N : Nat) (hN : 0 < N) : (network N hN).rows.length=(old N hN).rows.length := rfl
/-- The new vector stores all complete factor tables in the same ascending original order. -/
theorem right_list (N : Nat) (hN : 0 < N) : (network N hN).right.toList=
    factors N hN (SemiprimeD1BooleanFactorCatalogueIndices.indices N) := by
  apply List.ext_getElem
  · simp only [Vector.length_toList,factors,List.length_map,SemiprimeD1BooleanFactorCatalogueIndices.indices,List.length_finRange]
    exact old_right_length N hN
  · intro i hi hj
    simp only [network,Vector.getElem_toList,Vector.getElem_ofFn,factors,List.getElem_map,
      SemiprimeD1BooleanFactorCatalogueIndices.indices,List.getElem_finRange]
    rfl
/-- Ordered literal vertices have precisely the retained owner prefix and marked factor suffix. -/
theorem vertices_original (N : Nat) (hN : 0 < N) : SemiprimeD1TensorNetwork.vertices (network N hN)=
    SemiprimeD1StackOwnerRecordsOriginal.vertices N hN []++
      factors N hN (SemiprimeD1BooleanFactorCatalogueIndices.indices N) := by
  exact congrArg₂ List.append (SemiprimeD1RootRecordCoordinates.owner_vector N hN []) (right_list N hN)
/-- SAME actual source output is the entire owner-first marked original network. -/
theorem output_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits) :
    (SemiprimeD1StackMarkedRootRecordsExecution.done bits hN).data (SemiprimeD1StackMarkedRootRecords.aux .output)=
      SemiprimeD1StackVertexProduct.records (SemiprimeD1TensorNetwork.vertices (network (bitValue bits) hN)) := by
  change SemiprimeD1StackMarkedRootRecordsExecution.owners bits hN++
    (payload bits (SemiprimeD1StackMarkedRootRecordsExecution.rows bits hN)++[false])=_
  have hf := records_original bits hc hN (SemiprimeD1BooleanFactorCatalogueIndices.indices (bitValue bits))
  have ho := SemiprimeD1StackRootNetworkRecordsOriginal.owner_payload bits hN [] []
  have hfirst := congrArg₂ List.append ho hf
  exact hfirst.trans ((SemiprimeD1StackRootNetworkRecordsOriginal.records_append _ _).trans
    (congrArg SemiprimeD1StackVertexProduct.records (vertices_original (bitValue bits) hN).symm))
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsNetwork
