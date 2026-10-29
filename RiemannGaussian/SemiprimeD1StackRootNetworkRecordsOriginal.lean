/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootNetworkRecordsExecution
import RiemannGaussian.SemiprimeD1StackRootNetworkRecordsResources
import RiemannGaussian.SemiprimeD1RootRecordCoordinates

/-! # Exact whole original root-network record output
The two actual source tapes are joined in the literal original vertex order.
All prescribed prefixes, including repeats/conflicts and retained physical tails,
are covered. No native root constructor or byte append is a runtime instruction.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackRootNetworkRecordsOriginal
open SemiprimeD1StackRootNetworkRecords SemiprimeD1StackRootNetworkRecordsExecution
open SemiprimeBitArithmetic (bitValue)
namespace V
export SemiprimeD1StackVertexProduct (records)
end V
namespace L
export SemiprimeD1StackVertexRecordStream (row row_records)
end L
/-- Chronological original record bytes, excluding only the final vector marker. -/
def recordBytes (vs:List SemiprimeD1LeafCounter.Vertex) : List Bool :=
  (vs.map (fun v=>L.row (SemiprimeD1StackVertexReadExecution.portTape v.ports)
    (SemiprimeD1TensorTapeCodec.tape v.table))).flatten
/-- Joining two whole original lists puts precisely the first payload ahead of the second list. -/
theorem records_append (vs ws:List SemiprimeD1LeafCounter.Vertex) :
    recordBytes vs++V.records ws=V.records (vs++ws) := by
  induction vs with
  | nil=>rfl
  | cons v vs ih=>
    change (L.row (SemiprimeD1StackVertexReadExecution.portTape v.ports)
      (SemiprimeD1TensorTapeCodec.tape v.table)++recordBytes vs)++V.records ws=V.records ((v::vs)++ws)
    rw [List.append_assoc,ih]
    exact L.row_records v (vs++ws)
/-- The actual owner's false-terminated source supplies exactly its chronological payload. -/
theorem owner_payload (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    ownerBytes bits hN fixed=recordBytes (SemiprimeD1StackOwnerRecordsOriginal.vertices (bitValue bits) hN fixed) := by
  have h0:=owner_output bits hN fixed tail
  have h1:=SemiprimeD1StackOwnerRecordsExecution.output_original bits hN fixed tail
  have h2:=SemiprimeD1StackOwnerRecordsOriginal.flatten_records
    (SemiprimeD1StackOwnerRecordsOriginal.vertices (bitValue bits) hN fixed)
  exact List.append_cancel_right (h0.symm.trans (h1.trans h2.symm))
/-- The actual complete factor source supplies every old factor in its unchanged original order. -/
theorem factors_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    factorTape bits=V.records (SemiprimeD1StackFullFactorCatalogueOriginal.factorVertices (bitValue bits) hN
      (SemiprimeD1BooleanFactorCatalogueIndices.indices (bitValue bits))) :=
  (factor_output bits).symm.trans (SemiprimeD1StackFullFactorCatalogueOriginal.final_output bits hc hN)
/-- Exact old cached network tape, with owners first and all factors second, for EVERY original prefix. -/
theorem output_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    (done bits hN fixed tail).data output=V.records (SemiprimeD1TensorNetwork.vertices
      (SemiprimeD1RootStateResources.root (bitValue bits) hN fixed)) := by
  change ownerBytes bits hN fixed++factorTape bits=_
  rw [owner_payload bits hN fixed tail,factors_original bits hc hN,
    SemiprimeD1RootRecordCoordinates.vertices_original]
  exact records_append _ _
/-- One genuine original-prefix execution with exact full old root record bytes. -/
theorem source_prefix_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    ∃t ≤ timeBound bits hN fixed tail,SemiprimeD1StackCalls.run program t
      (initialPrefix bits (SemiprimeD1StackRootNetworkRecordsAcquisition.prescription bits fixed tail))=
        some (done bits hN fixed tail) ∧
      (done bits hN fixed tail).data output=V.records (SemiprimeD1TensorNetwork.vertices
        (SemiprimeD1RootStateResources.root (bitValue bits) hN fixed)) := by
  obtain ⟨t,ht,hr⟩:=source_run_prefix bits hc hN fixed tail
  exact ⟨t,ht,hr,output_original bits hc hN fixed tail⟩
/-- N alone suffices to acquire the entire old original root-network input tape. -/
theorem source_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t ≤ timeBound bits hN [] []+1,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits hN [] []) ∧
      (done bits hN [] []).data output=V.records (SemiprimeD1TensorNetwork.vertices
        (SemiprimeD1RootStateResources.root (bitValue bits) hN [])) := by
  obtain ⟨t,ht,hr⟩:=source_run bits hc hN
  exact ⟨t,ht,hr,output_original bits hc hN [] []⟩
/-- The complete original-input acquisition and exact output share ONE actual global source clock. -/
theorem source_original_bounded (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<bitValue bits) :
    ∃t ≤ SemiprimeD1StackRootNetworkRecordsBounds.runBound bits,
      SemiprimeD1StackCalls.run program t (initial bits)=some (done bits hN [] []) ∧
      (done bits hN [] []).data output=V.records (SemiprimeD1TensorNetwork.vertices
        (SemiprimeD1RootStateResources.root (bitValue bits) hN [])) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackRootNetworkRecordsBounds.source_run_bounded bits hc hN
  exact ⟨t,ht,hr,output_original bits hc hN [] []⟩
/-- Fixed constants precede every N; the bound covers the SAME exact original-N acquisition. -/
theorem uniform_original :∃coef degree:Nat,∀(bits:List Bool)
    (_hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits),
    ∃t ≤ coef*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^degree*
      2^(19*SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength (bitValue bits))),
      SemiprimeD1StackCalls.run program t (initial bits)=some (done bits hN [] []) ∧
      (done bits hN [] []).data output=V.records (SemiprimeD1TensorNetwork.vertices
        (SemiprimeD1RootStateResources.root (bitValue bits) hN [])) := by
  obtain ⟨coef,degree,h⟩:=SemiprimeD1StackRootNetworkRecordsResources.source_run_monomial
  refine ⟨coef,degree,?_⟩
  intro bits hc hN
  obtain ⟨t,ht,hr⟩:=h bits hc hN
  have hw:=SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc
  refine ⟨t,?_,hr,output_original bits hc hN [] []⟩
  simpa only [SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity,hw] using ht
/-- The same fixed program covers every physical caller prefix/tail with its full input size paid. -/
theorem uniform_prefix_original :∃coef degree:Nat,∀(bits:List Bool)
    (_hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool),
    ∃t ≤ coef*(bits.length+(SemiprimeD1StackRootNetworkRecordsAcquisition.prescription bits fixed tail).length+1)^degree*
      2^(19*SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity bits),
      SemiprimeD1StackCalls.run program t
        (initialPrefix bits (SemiprimeD1StackRootNetworkRecordsAcquisition.prescription bits fixed tail))=
          some (done bits hN fixed tail) ∧
      (done bits hN fixed tail).data output=V.records (SemiprimeD1TensorNetwork.vertices
        (SemiprimeD1RootStateResources.root (bitValue bits) hN fixed)) := by
  obtain ⟨coef,degree,h⟩:=SemiprimeD1StackRootNetworkRecordsResources.source_run_prefix_monomial
  refine ⟨coef,degree,?_⟩
  intro bits hc hN fixed tail
  obtain ⟨t,ht,hr⟩:=h bits hc hN fixed tail
  exact ⟨t,ht,hr,output_original bits hc hN fixed tail⟩
/-- Actual initialization is the genuine finite machine's binary-N-only Turing.initList. -/
noncomputable def machineOriginal (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits hN [] [])))
      (SemiprimeD1StackRootNetworkRecordsBounds.runBound bits) :=
  SemiprimeD1StackRootNetworkRecordsResources.rootRecordsInTime bits hc hN
end RiemannGaussian.SemiprimeD1StackRootNetworkRecordsOriginal
