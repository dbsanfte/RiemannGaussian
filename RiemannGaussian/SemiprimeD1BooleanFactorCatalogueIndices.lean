/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueSource
/-! # Concrete factor indices, physical query keys and original descriptor queue
These are proof-side views of the N-only source and actual unary counter.
No typed list, native factor number or scope answer enters runtime control.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1BooleanFactorCatalogueIndices
namespace FS
export SemiprimeD1StackFactorScopeFibre (result output)
end FS
namespace VS
export SemiprimeD1StackVertexCatalogueExecution (result)
end VS
open SemiprimePublicAcquiredExecution (factorCount indexedArity vertexEnumeration)
open SemiprimeD1StackOwnerFibreOriginal (scopeWord)
open SemiprimeBitArithmetic (bitValue)
/-- Exact physically pushed unary factor counter, not binary encoding of n. -/
def key (n : Nat) : List Bool :=SemiprimeD1FactorScopePairOriginal.key n
/-- Scope words selected by the actual generic numeric filter over the acquired pair stream. -/
def scopeWords (bits : List Bool) (n : Nat) : List (List Bool) :=
  SemiprimeD1StackOwnerFibre.values (key n)
    ((SemiprimeD1StackFactorScopePairExecution.rows bits).map SemiprimeD1FactorScopePairEncoding.pair)
/-- Exact original source factor-index order. -/
def indices (N : Nat) : List (Fin (factorCount N)) :=List.finRange (factorCount N)
/-- Exact old original vertex at its source enumeration position. -/
def vertex (N : Nat) (f : Fin (factorCount N)) : SemiprimePublicAcquiredExecution.PublicVertex N :=
  (vertexEnumeration N).equivFin f
/-- Actual descriptor suffix in original factor-major order. -/
def descriptorTape (N : Nat) (fs : List (Fin (factorCount N))) : List Bool :=
  fs.foldr (fun f tail=>SemiprimeD1VertexCatalogueEncoding.vertex (vertex N f) tail) []
/-- The actual current-source output is exactly this scope-word vector. -/
theorem source_output (bits : List Bool) (n : Nat) :
    FS.result bits (key n) FS.output=SemiprimeD1TensorTapeCodec.vectorBits (scopeWords bits n) :=rfl
/-- The counter starts at the literal empty zero word. -/
theorem key_zero : key 0=[] :=rfl
/-- One literal true push advances exactly one original factor position. -/
theorem key_succ (n : Nat) : key (n+1)=true::key n :=by
  exact List.replicate_succ
/-- All original selected scopes equal the original factor's old ordered port list. -/
theorem original_scopes (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (f : Fin (factorCount (bitValue bits))) :
    scopeWords bits f.val=((SemiprimeD1RootTensorTables.factorNode (bitValue bits) hN f).ports).map
      (scopeWord (bitValue bits)) :=
  SemiprimeD1FactorScopePairOriginal.original_fibre bits hc hN f
/-- Finite source index values are the exact ascending native range, in proofs only. -/
theorem indices_values (N : Nat) : (indices N).map Fin.val=List.range (factorCount N) :=
  SemiprimeD1FactorScopeIncidences.finRange_values _
/-- The original graph always has a carry-initial vertex, so its loop is nonempty. -/
theorem factorCount_pos (N : Nat) : 0<factorCount N :=
  List.length_pos_of_mem ((vertexEnumeration N).complete (.inl .carryInitial))
/-- Exact dependent index enumeration is the old duplicate-free vertex enumeration. -/
theorem vertices_values (N : Nat) : (indices N).map (vertex N)=(vertexEnumeration N).values := by
  change (List.finRange (vertexEnumeration N).values.length).map (vertexEnumeration N).equivFin=_
  rw [List.finRange,List.map_ofFn]
  exact List.ofFn_get (vertexEnumeration N).values
/-- Folding the exact original index order produces the exact original descriptor catalogue. -/
theorem descriptor_vertices (N : Nat) : descriptorTape N (indices N)=
    (vertexEnumeration N).values.foldr SemiprimeD1VertexCatalogueEncoding.vertex [] := by
  rw [←vertices_values N,List.foldr_map]
  rfl
/-- The actual N-only53-role catalogue output is exactly the loop's original descriptor queue. -/
theorem descriptor_source (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) :
    VS.result bits SemiprimeD1StackBooleanFactorCatalogueView.catalogueOutput=
      descriptorTape (bitValue bits) (indices (bitValue bits)) := by
  rw [descriptor_vertices]
  exact SemiprimeD1StackVertexCatalogueExecution.original_vertices bits hc hN
end RiemannGaussian.SemiprimeD1BooleanFactorCatalogueIndices
