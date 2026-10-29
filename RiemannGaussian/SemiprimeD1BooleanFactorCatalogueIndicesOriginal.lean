/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BooleanFactorCatalogueIndicesBounds
/-! # Original numeric factor ports and exact binary-to-unary scope bytes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1BooleanFactorCatalogueIndicesOriginal
open SemiprimeD1BooleanFactorCatalogueIndices SemiprimeD1BooleanFactorCatalogueIndicesBounds
open SemiprimePublicAcquiredExecution (factorCount indexedArity)
open SemiprimeD1StackOwnerFibreOriginal (enumeration scopeWord)
open SemiprimeD1RootTensorTables (Port factorNode)
open SemiprimeBitArithmetic (bitValue)
/-- Original global occurrence ordinal, in factor-major/local-slot source order. -/
def portOrdinal (N : Nat) (p : Port N) : Nat :=((enumeration N).equivFin.symm p).val
/-- Original ordered factor port list expressed in the physical numeric occurrence domain. -/
def numericPorts (N : Nat) (f : Fin (factorCount N)) : List Nat :=
  ((List.finRange (indexedArity N f)).map (Sigma.mk f)).map (portOrdinal N)
/-- Exact original eager factor-node port list, with unchanged ascending local order. -/
theorem numericPorts_factorNode (N : Nat) (hN : 0<N) (f : Fin (factorCount N)) :
    numericPorts N f=(factorNode N hN f).ports.map (portOrdinal N) := by
  rw [SemiprimeD1RootTensorTables.factorNode_ports]
  rfl
/-- Scope count equals the actual old local table arity, without a supplied degree. -/
theorem scope_count_eq (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (f : Fin (factorCount (bitValue bits))) :
    (scopeWords bits f.val).length=indexedArity (bitValue bits) f := by
  rw [original_scopes bits hc hN f,List.length_map,SemiprimeD1RootTensorTables.factorNode_degree]
/-- Numeric port inventory has exactly the old factor table's arity. -/
theorem numericPorts_length (N : Nat) (f : Fin (factorCount N)) :
    (numericPorts N f).length=indexedArity N f := by
  simp only [numericPorts,List.length_map,List.length_finRange]
/-- Every numeric original factor port lies in the acquired M-occurrence domain. -/
theorem numericPorts_lt (N : Nat) (f : Fin (factorCount N)) :
    ∀i∈numericPorts N f,i<occurrences N := by
  intro i hi
  obtain ⟨p,_,rfl⟩:=List.mem_map.mp hi
  have h:=((enumeration N).equivFin.symm p).isLt
  simpa only [portOrdinal,occurrences,SemiprimeD1StackOwnerFibreOriginal.enumeration_length] using h
/-- Actual selected binary scope values are exactly the original global numeric ports. -/
theorem scopeWords_values (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (f : Fin (factorCount (bitValue bits))) :
    (scopeWords bits f.val).map bitValue=numericPorts (bitValue bits) f := by
  rw [original_scopes bits hc hN f,numericPorts_factorNode _ hN,List.map_map]
  apply List.map_congr_left
  intro p _
  exact SemiprimeD1StackOwnerFibreOriginal.scopeWord_value _ p
/-- Every actual scope byte is the original acquired common-width idAt M word. -/
theorem scopeWords_idAt (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (f : Fin (factorCount (bitValue bits))) :
    scopeWords bits f.val=(numericPorts (bitValue bits) f).map
      (SemiprimeD1OrdinalBankSpec.idAt (occurrences (bitValue bits))) := by
  rw [original_scopes bits hc hN f,numericPorts_factorNode _ hN,List.map_map]
  rfl
/-- The actual paid scope converter emits exactly the frozen original unary port field. -/
theorem unary_portTape (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (f : Fin (factorCount (bitValue bits))) :
    SemiprimeD1StackPortOrdinalStream.result (scopeWords bits f.val)=
      SemiprimeD1StackVertexReadExecution.portTape (numericPorts (bitValue bits) f) := by
  rw [scopeWords_idAt bits hc hN f]
  exact SemiprimeD1StackPortOrdinalStreamOriginal.selected_portTape _ _ (numericPorts_lt _ f)
end RiemannGaussian.SemiprimeD1BooleanFactorCatalogueIndicesOriginal
