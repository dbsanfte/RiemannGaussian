/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRoutingView
import RiemannGaussian.SemiprimeD1StackOwnerFibreOriginal
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
namespace RiemannGaussian.SemiprimeD1PortOwnerRoutingSpec
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1FactorScopePairEncoding (Record)
open SemiprimePublicAcquiredExecution
/-- Exact six-field compact query built from actual scoped-record fields 3..8 plus a true sentinel. -/
def query (w:Record) : List Bool :=frame (w 3) (frame (w 4) (frame (w 5)
  (frame (w 6) (frame (w 7) (frame (w 8) [true])))))
/-- Actual numeric lookup result followed by that SAME actual occurrence-ID payload. -/
def pair (map:List (List Bool×List Bool)) (w:Record) : List Bool×List Bool :=
  ((SemiprimeD1StackOwnerLookup.result (query w) map []).1,w 0)
/-- Authoritative original nine-field record produces the exact original local-slot/vertex key. -/
theorem query_original (N:Nat) (p:SemiprimeD1RootTensorTables.Port N) :
    query (SemiprimeD1FactorScopeIncidencesOriginal.indexedRecord N p)=
      SemiprimeD1PortOwnerKeys.key ⟨(vertexEnumeration N).equivFin p.1,p.2⟩ := rfl
/-- Physically matching the original key computes the ORIGINAL E-wire owner ID. -/
theorem pair_original (N:Nat) (hN:0<N) (p:SemiprimeD1RootTensorTables.Port N) :
    pair (SemiprimeD1StackOwnerLookupOriginal.Public.catalogue N hN)
      (SemiprimeD1FactorScopeIncidencesOriginal.indexedRecord N p)=
      (SemiprimeD1StackOwnerLookupOriginal.Public.encode N (indexedCoordinate N hN p.1 p.2),
        SemiprimeD1StackOwnerFibreOriginal.scopeWord N p) := by
  unfold pair
  rw [query_original]
  have ho:=SemiprimeD1StackOwnerLookupOriginal.Public.indexed_output N hN p.1 p.2 []
  change (SemiprimeD1StackOwnerLookup.result _ _ []).1=_ at ho
  rw [ho]
  change (_,SemiprimeD1FactorScopeIncidencesOriginal.scope N p)=_
  rw [SemiprimeD1FactorScopeIncidencesOriginal.scope_original]
  rfl
/-- ALL original occurrence rows route in their original FACTOR-major order, without permutation advice. -/
theorem original_rows (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<SemiprimeBitArithmetic.bitValue bits) :
    (SemiprimeD1StackPortOwnerRoutingView.rows bits).map
      (pair (SemiprimeD1StackOwnerLookupOriginal.Public.catalogue (SemiprimeBitArithmetic.bitValue bits) hN))=
      SemiprimeD1StackOwnerFibreOriginal.rows (SemiprimeBitArithmetic.bitValue bits) hN := by
  rw [SemiprimeD1StackPortOwnerRoutingView.rows,SemiprimeD1FactorScopeIncidencesOriginal.original_rows bits hc hN]
  unfold SemiprimeD1FactorScopeIncidencesOriginal.indexedRows SemiprimeD1StackOwnerFibreOriginal.rows
    SemiprimeD1StackOwnerFibreOriginal.routed
  rw [List.map_map]
  apply List.map_congr_left
  intro p _
  exact pair_original _ hN p
end RiemannGaussian.SemiprimeD1PortOwnerRoutingSpec
