/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1FactorScopeIncidences
/-! # Original-N physical scoped records are the original typed incidence enumeration -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1FactorScopeIncidencesOriginal
open SemiprimeD1FactorScopePairEncoding SemiprimeD1FactorScopeIncidences
open SemiprimeD1StackFactorScopePairExecution
open SemiprimeD1RootTensorTables (Port factorNode)
open SemiprimePublicAcquiredExecution (factorCount indexedArity vertexEnumeration)
open SemiprimeD1StackOwnerFibreOriginal (enumeration scopeWord)
open SemiprimeBitArithmetic (bitValue)
open SemiprimeD1StackUnaryDivmod (unary)
/-- Original occurrence scope ID, retaining the actual acquired common width. -/
def scope (N : Nat) (p : Port N) : List Bool :=
  SemiprimeD1OrdinalBankSpec.idAt (enumeration N).values.length ((enumeration N).equivFin.symm p).val
/-- The acquired M-bit occurrence code is the exact old scope-domain code. -/
theorem scope_original (N : Nat) (p : Port N) : scope N p=scopeWord N p := by
  apply congrArg (fun M=>SemiprimeD1OrdinalBankSpec.idAt M ((enumeration N).equivFin.symm p).val)
    (SemiprimeD1StackOwnerFibreOriginal.enumeration_length N)
/-- All nine original physical record fields in their original typed incidence order. -/
def indexedRecord (N : Nat) (p : Port N) : Record :=
  joined (SemiprimeD1PortScopeEncoding.fields
    (SemiprimeD1EdgeCatalogueEncoding.vertex ((vertexEnumeration N).equivFin p.1))
    ((enumeration N).equivFin.symm p).val p.1.val p.2.val) (scope N p)
/-- Complete all-original-port row list, mathematical specification only. -/
def indexedRows (N : Nat) : List Record :=(enumeration N).values.map (indexedRecord N)
/-- Full physically acquired scoped-port list equals the old indexed incidence order.
Only original canonical positive N is assumed; no row/order/cardinality advice. -/
theorem original_rows (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) : rows bits=indexedRows (bitValue bits) := by
  have hb:bits≠[]:=by intro h;rw [h] at hN;exact Nat.lt_irrefl _ hN
  have hd:=SemiprimeD1StackVertexCatalogueTags.digitCount_raw bits hb
  have hw:=SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc
  unfold rows SemiprimeD1StackPortScopeSource.ports SemiprimeD1StackPortScopeSource.ids
    SemiprimeD1StackPortOrdinalBankExecution.occurrences SemiprimeD1StackPortCatalogueExecution.vertices
  rw [hd,hw]
  exact scoped_indexed (vertexEnumeration (bitValue bits))
end RiemannGaussian.SemiprimeD1FactorScopeIncidencesOriginal
