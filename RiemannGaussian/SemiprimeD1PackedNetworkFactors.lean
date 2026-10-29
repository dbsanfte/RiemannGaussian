/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PackedNetworkEntries
import RiemannGaussian.SemiprimeD1PackedNetworkOwners
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsTopology
/-! # Every actual marked factor entry at the original ordered coordinates
The natural coefficient comes from the actual new stored table. Only its
port list is reused from the original topology; no old entry is reused.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
noncomputable section
namespace RiemannGaussian.SemiprimeD1PackedNetworkFactors
open scoped BigOperators
open SemiprimePublicAcquiredExecution (wireCount factorCount indexedArity indexedCoordinate)
open SemiprimeD1TensorNetwork
open SemiprimeD1TensorTables SemiprimeD1PackedNetworkSemantics SemiprimeD1PackedNetworkEntries
open SemiprimeD1StackMarkedRootRecordsNetwork (network factor factors)
open SemiprimeD1BooleanFactorCatalogueIndices (vertex indices)
attribute [local irreducible] SemiprimeD1RootTensorTables.acquirePositive
/-- Finite complete ordered products, before original metadata is inserted. -/
theorem finRange_product {S : Type*} [CommMonoid S] {n : ℕ} (f : Fin n→S) :
    ((List.finRange n).map f).prod=∏i : Fin n,f i := by
  simp only [List.finRange,List.map_ofFn,List.prod_ofFn]
  rfl
/-- The actual marked factor keeps its original canonical incidence fibre. -/
theorem canonical_ports (N : ℕ) (hN : 0<N) (f : Fin (factorCount N)) :
    (factor N hN f).ports=rightPorts
      (SemiprimeD1RootNetwork.rows (SemiprimeD1RootLocalAssignments.source N hN []))
      (SemiprimeD1RootEntrySemantics.factorIndex N hN [] f) :=
  (SemiprimeD1StackMarkedRootRecordsNetwork.factor_ports N hN f).trans
    (SemiprimeD1RootRecordCoordinates.factor_ports N hN [] f).symm
/-- The actual new stored factor table gives its complete natural marked coefficient. -/
theorem factor_lookup (N : ℕ) (hN : 0<N) (f : Fin (factorCount N)) (bits : List Bool)
    (hb : bits.length=indexedArity N f) :
    wordNat (lookup (factor N hN f).table bits).words=
      SemiprimeD1PackedMomentPrecision.coefficient N hN (vertex N f)
        (fun j => (bits.toArray[j.val]?).getD false) := by
  change wordNat (lookup (cast (congrArg Table
    (SemiprimeD1StackFullFactorCatalogueOriginal.numeric_arity N f).symm)
    (SemiprimeD1StackMarkedPublicInputTableOriginal.reference N hN (vertex N f))) bits).words=_
  exact (congrArg wordNat (lookup_cast
    (SemiprimeD1StackFullFactorCatalogueOriginal.numeric_arity N f).symm
    (SemiprimeD1StackMarkedPublicInputTableOriginal.reference N hN (vertex N f)) bits)).trans
      (reference_lookup N hN (vertex N f) bits hb)
/-- The complete ordered actual factor gather is the original local coordinate vector. -/
theorem factor_consistent (N : ℕ) (hN : 0<N) (bits : Fin (wireCount N)→Bool)
    (f : Fin (factorCount N)) :
    entry (factor N hN f) (SemiprimeD1RootRightAssignments.originalAssignment N hN [] bits)=
      SemiprimeD1PackedMomentPrecision.coefficient N hN (vertex N f)
        (fun j => bits (indexedCoordinate N hN f j)) := by
  let a:=SemiprimeD1RootRightAssignments.originalAssignment N hN [] bits
  let input:=(factor N hN f).ports.map (fun p => ((List.ofFn a)[p]?).getD false)
  have hi : input=List.ofFn (fun j : Fin (indexedArity N f) => bits (indexedCoordinate N hN f j)) := by
    change (factor N hN f).ports.map _=_
    rw [canonical_ports N hN f]
    exact SemiprimeD1RootRightAssignments.right_bits N hN [] bits f
  have hl : input.length=indexedArity N f := by rw [hi,List.length_ofFn]
  have hg : (fun j : Fin (indexedArity N f) => (input.toArray[j.val]?).getD false)=
      (fun j => bits (indexedCoordinate N hN f j)) := by
    rw [hi]
    exact bits_ofFn _
  calc
    _ = wordNat (lookup (factor N hN f).table input).words := entry_lookup _ a
    _ = _ := (factor_lookup N hN f input hl).trans
      (congrArg (SemiprimeD1PackedMomentPrecision.coefficient N hN (vertex N f)) hg)
/-- All complete marked right factors occur once in their actual original order. -/
theorem right_consistent (N : ℕ) (hN : 0<N) (bits : Fin (wireCount N)→Bool) :
    SemiprimeD1PackedNetworkOwners.consistentRight N hN bits=
      ∏f : Fin (factorCount N),SemiprimeD1PackedMomentPrecision.coefficient N hN (vertex N f)
        (fun j => bits (indexedCoordinate N hN f j)) := by
  let a:=SemiprimeD1RootRightAssignments.originalAssignment N hN [] bits
  have h:=congrArg (fun vs : List SemiprimeD1LeafCounter.Vertex =>
    (vs.map (fun v => entry v a)).prod) (SemiprimeD1StackMarkedRootRecordsNetwork.right_list N hN)
  refine h.trans ?_
  simp only [factors,List.map_map,Function.comp_def,indices]
  change (((List.finRange (factorCount N)).map (fun f => entry (factor N hN f) a)).prod)=_
  rw [finRange_product]
  exact Finset.prod_congr rfl (fun f _ => factor_consistent N hN bits f)
end RiemannGaussian.SemiprimeD1PackedNetworkFactors
