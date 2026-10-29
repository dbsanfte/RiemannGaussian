/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueSource
import RiemannGaussian.SemiprimeD1StackPortOwnerRecipeOriginal
import RiemannGaussian.SemiprimeD1StackRootScopeBankOriginal
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackOwnerCatalogueOriginalMetadata
open SemiprimeD1StackOwnerCatalogue SemiprimeD1StackOwnerCatalogueSource
open SemiprimeMacroParameters SemiprimePublicAcquiredExecution
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeBitArithmetic (bitValue)
/-- Exact original r/t/digits associated with original binary N, solely a proof specification. -/
def originalDimension (N:ℕ) (part:Fin 3) : ℕ :=
  if part=0 then firstAxis (bitLength N) else if part=1 then secondAxis (bitLength N) else digitCount (bitLength N)
/-- Actual retained dimension words already present after the N-only acquisition prefix. -/
theorem dimensions_raw (bits:List Bool) (part:Fin 3) : ready bits (dimension part)=unary
    (if part=0 then firstAxis bits.length else if part=1 then secondAxis bits.length
      else SemiprimeD1StackVertexCatalogueCaches.digitCountValue bits) := by
  fin_cases part <;> rfl
/-- ALL original parameter-word bindings follow from binary N and actual acquisition, not metadata advice. -/
theorem dimensions_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<bitValue bits) (part:Fin 3) :
    ready bits (dimension part)=unary (originalDimension (bitValue bits) part) := by
  have hw:bits.length=bitLength (bitValue bits):=SemiprimeD1BinaryBootstrap.canonical_width bits hc
  have hb:bits≠[]:=by intro h;subst bits;simp [bitValue] at hN
  rw [dimensions_raw,SemiprimeD1StackVertexCatalogueTags.digitCount_raw bits hb,hw]
  rfl
/-- The actually copied edge reader is the complete original E-wire tape in exact original order. -/
theorem edges_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    edges bits=(edgeEnumeration (bitValue bits)).values.foldr SemiprimeD1EdgeCatalogueEncoding.edge [] := by
  exact SemiprimeD1StackEdgeCatalogueExecution.original_edges bits hc hN
/-- Same physically acquired bytes in the parser's literal six-field record grammar. -/
theorem edge_reader_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ready bits (aux .readerEdges)=SemiprimeD1StackEdgeCount.tape
      ((edgeEnumeration (bitValue bits)).values.map SemiprimeD1StackEdgeCount.edgeFields) [] := by
  change edges bits=_
  rw [SemiprimeD1StackEdgeCount.original_tape]
  exact edges_original bits hc hN
/-- The actual ordinal engine receives M=2E from TWO real counter pushes per original edge. -/
theorem occurrences_original (bits:List Bool) :
    SemiprimeD1StackRootScopeBankExecution.occurrenceCount bits=2*wireCount (bitValue bits) :=
  congrArg (2*·) (SemiprimeD1StackRootScopeBankOriginal.wire_count bits)
/-- The actual private ID reader contains the physically generated padded M-bank, never an E-bank substitute. -/
theorem id_reader_original (bits:List Bool) :
    ready bits (aux .readerIds)=SemiprimeD1TensorTapeCodec.vectorBits
      (SemiprimeD1OrdinalBankSpec.words (2*wireCount (bitValue bits))) := by
  calc
    ready bits (aux .readerIds)=ids bits:=rfl
    _=SemiprimeD1TensorTapeCodec.vectorBits
        (SemiprimeD1OrdinalBankSpec.words (SemiprimeD1StackRootScopeBankExecution.occurrenceCount bits)):=
      SemiprimeD1StackRootScopeBankExecution.result_ids bits
    _=_:=congrArg (fun n=>SemiprimeD1TensorTapeCodec.vectorBits (SemiprimeD1OrdinalBankSpec.words n))
      (occurrences_original bits)
/-- Every original E-wire ordinal is legitimately in the acquired M-bank's first E entries. -/
theorem owner_id_value (bits:List Bool) (wire:Fin (wireCount (bitValue bits))) :
    bitValue (SemiprimeD1OrdinalBankSpec.idAt (2*wireCount (bitValue bits)) wire.val)=wire.val :=
  SemiprimeD1OrdinalBankSpec.id_value _ _ (by have hi:=wire.isLt;omega)
/-- Both original namespaces use actual M-bit payloads, while this owner ID's value lies in Fin E. -/
theorem owner_id_width (bits:List Bool) (wire:Fin (wireCount (bitValue bits))) :
    (SemiprimeD1OrdinalBankSpec.idAt (2*wireCount (bitValue bits)) wire.val).length=2*wireCount (bitValue bits) :=
  SemiprimeD1OrdinalBankSpec.id_length _ _ (by have hi:=wire.isLt;omega)
end RiemannGaussian.SemiprimeD1StackOwnerCatalogueOriginalMetadata
