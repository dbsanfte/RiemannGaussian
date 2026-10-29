/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsEncoding
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsAcquisition
/-! # The two ACTUALLY acquired streams have the same complete original factor order -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsAlignment
open SemiprimeD1StackMarkedRootRecords SemiprimeD1StackMarkedRootRecordsEncoding
open SemiprimeBitArithmetic (bitValue)
open SemiprimePublicAcquiredExecution (factorCount)
namespace F
export SemiprimeD1StackFullFactorCatalogueOriginal (factorVertices localVertex)
end F
/-- The paired-row proof specification uses the complete original factor enumeration. -/
def originalRows (N : Nat) (hN : 0 < N) (fs : List (Fin (factorCount N))) : List Row :=
  fs.map (originalRow N hN)
/-- Old paired record bytes are exactly the retained ALL18-family real source output. -/
theorem oldRecords_original (N : Nat) (hN : 0 < N) (fs : List (Fin (factorCount N))) :
    oldRecords (originalRows N hN fs)=SemiprimeD1StackVertexProduct.records (F.factorVertices N hN fs) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    change true::SemiprimeSourceHistogramKeyBits.frame _ (SemiprimeSourceHistogramKeyBits.frame _
      (oldRecords (originalRows N hN fs)))=true::SemiprimeSourceHistogramKeyBits.frame _
        (SemiprimeSourceHistogramKeyBits.frame _ (SemiprimeD1StackVertexProduct.records (F.factorVertices N hN fs)))
    rw [ih]
    rfl
/-- The flat five-field descriptors use the EXACT same source factor order and have EMPTY EOF. -/
theorem descriptors_original (N : Nat) (hN : 0 < N) (fs : List (Fin (factorCount N))) :
    descriptors (originalRows N hN fs)=SemiprimeD1BooleanFactorCatalogueIndices.descriptorTape N fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    change SemiprimeD1EdgeCatalogueEncoding.record
      (SemiprimeD1EdgeCatalogueEncoding.vertex (SemiprimeD1BooleanFactorCatalogueIndices.vertex N f))
      (descriptors (originalRows N hN fs))=_
    rw [ih,SemiprimeD1EdgeCatalogueEncoding.record_vertex]
    rfl
/-- The actual retained old factor cache supplies precisely the row-loop's physical record input. -/
theorem factor_cache (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits) :
    SemiprimeD1StackRootNetworkRecordsExecution.result bits hN [] []
      (R.factorStack SemiprimeD1StackFullFactorCatalogue.output)=
      oldRecords (originalRows (bitValue bits) hN (SemiprimeD1BooleanFactorCatalogueIndices.indices (bitValue bits))) := by
  exact (SemiprimeD1StackFullFactorCatalogueOriginal.final_output bits hc hN).trans
    (oldRecords_original (bitValue bits) hN _).symm
/-- The fresh real53 call supplies precisely the matched original descriptor stream. -/
theorem descriptor_cache (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits) :
    SemiprimeD1StackMarkedRootRecordsAcquisition.descriptorBytes bits=
      descriptors (originalRows (bitValue bits) hN (SemiprimeD1BooleanFactorCatalogueIndices.indices (bitValue bits))) := by
  exact (SemiprimeD1BooleanFactorCatalogueIndices.descriptor_source bits hc hN).trans
    (descriptors_original (bitValue bits) hN _).symm
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsAlignment
