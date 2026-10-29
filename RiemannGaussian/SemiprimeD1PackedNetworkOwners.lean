/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PackedNetworkSemantics
import RiemannGaussian.SemiprimeD1RootRightAssignments
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsTopology
/-! # Natural copy elimination in the actual acquired marked root
The generic owner's natural-value premise is discharged from the actual
retained owner words. No modular-four equality is transported to a new ring.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
noncomputable section
namespace RiemannGaussian.SemiprimeD1PackedNetworkOwners
open scoped BigOperators
open SemiprimePublicAcquiredExecution SemiprimeD1TensorNetwork
open SemiprimeD1TensorNetworkLayout
open SemiprimeD1TensorTables SemiprimeD1PackedNetworkSemantics
open SemiprimeD1StackMarkedRootRecordsNetwork (network)
attribute [local irreducible] SemiprimeD1RootTensorTables.acquirePositive
/-- Empty-prefix elimination before any concrete original graph metadata is inserted. -/
theorem eliminate_empty (net : Network) (hw : WellFormed net)
    (hentry : ∀v : Fin net.leftCount,∀bits : List Bool,bits.length=(leftPorts net.rows v).length→
      wordNat (lookup (net.left[v.val]).table bits).words=SemiprimeD1RootOwnerTables.weight [] v bits) :
    naturalContraction net=∑bits : Fin net.leftCount→Bool,
      rightValue net (fun i => bits (leftGroup net.rows i)) := by
  have h:=copy_elimination net hw [] hentry
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro bits _
  exact ite_eq_left (fun _ => rfl)
/-- Changed-right normal form with the acquired owner's count explicit in its input type. -/
def changed {n F : ℕ} {arity : Fin F→ℕ}
    (data : SemiprimeD1RootTensorTables.Acquired n F arity)
    (right : Vector SemiprimeD1LeafCounter.Vertex (SemiprimeD1RootNetwork.rows data).length) : Network :=
  {(SemiprimeD1RootNetwork.fromCache data).network with right := right}
/-- Typed acquired-cache elimination before the original graph is instantiated. -/
theorem eliminate_changed {n F : ℕ} {arity : Fin F→ℕ}
    (data : SemiprimeD1RootTensorTables.Acquired n F arity)
    (right : Vector SemiprimeD1LeafCounter.Vertex (SemiprimeD1RootNetwork.rows data).length)
    (hw : WellFormed (changed data right))
    (hentry : ∀v : Fin n,∀bits : List Bool,
      bits.length=(leftPorts (SemiprimeD1RootNetwork.rows data) v).length→
      wordNat (lookup (((SemiprimeD1RootNetwork.fromCache data).network).left[v.val]).table bits).words=
        SemiprimeD1RootOwnerTables.weight [] v bits) :
    naturalContraction (changed data right)=∑bits : Fin n→Bool,rightValue (changed data right)
      (fun i => bits (leftGroup (SemiprimeD1RootNetwork.rows data) i)) :=
  eliminate_empty (changed data right) hw hentry
/-- Each actual retained owner has its full natural zero/one/two copy weight. -/
theorem owner_lookup (N : ℕ) (hN : 0<N) (v : Fin (wireCount N)) (bits : List Bool)
    (hb : bits.length=(leftPorts
      (SemiprimeD1RootNetwork.rows (SemiprimeD1RootLocalAssignments.source N hN [])) v).length) :
    wordNat (lookup (SemiprimeD1RootEntrySemantics.ownerVertex N hN [] v).table bits).words=
      SemiprimeD1RootOwnerTables.weight [] v bits := by
  rw [SemiprimeD1RootEntrySemantics.original_owner_lookup N hN [] v bits hb]
  exact wordNat_of_values _ _ (SemiprimeD1StackMarkedRootRecordsIntegral.owner_value [] v bits)
/-- Exact factor-side pullback value, typed before insertion beneath a public Boolean sum. -/
def consistentRight (N : ℕ) (hN : 0<N) (bits : Fin (wireCount N)→Bool) : ℕ :=
  rightValue (network N hN) (SemiprimeD1RootRightAssignments.originalAssignment N hN [] bits)
/-- Every incidence assignment is eliminated using actual complete owner fibres.
All marked right entries and isolated-owner multiplicities are retained. -/
theorem eliminate (N : ℕ) (hN : 0<N) :
    naturalContraction (network N hN)=
      ∑bits : Fin (wireCount N)→Bool,consistentRight N hN bits := by
  let data:=SemiprimeD1RootLocalAssignments.source N hN []
  let right : Vector SemiprimeD1LeafCounter.Vertex (SemiprimeD1RootNetwork.rows data).length :=
    Vector.ofFn (fun i => SemiprimeD1StackMarkedRootRecordsNetwork.factor N hN
      (Fin.cast (SemiprimeD1RootNetwork.rows_length data) i))
  have hn : network N hN=changed data right := rfl
  have h:=eliminate_changed data right
    (hn ▸ SemiprimeD1StackMarkedRootRecordsTopology.wellFormed N hN)
    (fun v bits hb => owner_lookup N hN v bits hb)
  exact h
end RiemannGaussian.SemiprimeD1PackedNetworkOwners
