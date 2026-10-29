/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildStateResources
import RiemannGaussian.SemiprimeD1RootTensorTablesBounds
import RiemannGaussian.SemiprimeD1RootCoordinates
import RiemannGaussian.SemiprimeD1PublicPackingReady
import RiemannGaussian.SemiprimePublicBudgetDimensions

/-! # Original-input root dimensions and literal table inventory
All root size and degree facts are derived from the actual acquired macro
network. Original configuration/descriptor native arithmetic remains a separate
primitive-lowering obligation, not hidden in this storage theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1RootStateResources
open scoped BigOperators
open SemiprimePublicAcquiredExecution SemiprimeMacroParameters
open SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkLayout
open SemiprimeD1NetworkStateResources SemiprimeD1TensorNetworkRecursion
open SemiprimeD1RootNetwork SemiprimeD1RootTensorTablesBounds
attribute [local irreducible] SemiprimeD1RootTensorTables.acquirePositive
attribute [local irreducible] wireCount factorCount indexedArity indexedCoordinate

/-- The actual original-binary acquired root network. -/
abbrev root (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :=
  (SemiprimeD1RootNetwork.acquirePositive N hN fixed).network

/-- Canonical factor grouping preserves every acquired real occurrence. -/
theorem fromCache_edges {n F : ℕ} {arity : Fin F→ℕ}
    (data : SemiprimeD1RootTensorTables.Acquired n F arity) :
    edgeCount (fromCache data).network=data.records.length := by
  change scope (rows data)=_
  rw [←rows_flatten_length]
  simpa only [List.length_map] using (SemiprimeD1RootPortCounts.rows_owner_perm data).length_eq

/-- Root incidence count is twice the ACTUAL subdivided public Boolean wire count. -/
theorem root_edges (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    edgeCount (root N hN fixed)=2*wireCount N := by
  rw [show root N hN fixed=(fromCache (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)).network from rfl,
    fromCache_edges,records_length,indexed_incidence_count N hN]

/-- Both acquired original vertex families retain their literal declared counts. -/
theorem root_vertices (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    vertexCount (root N hN fixed)=wireCount N+factorCount N := by
  change wireCount N+(rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)).length=_
  rw [rows_length]

/-- Isolated root vertices are paid, using the actual original factor-count bound. -/
theorem root_vertices_le_edges (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    vertexCount (root N hN fixed)≤edgeCount (root N hN fixed) := by
  rw [root_vertices,root_edges]
  have h:=SemiprimePublicBudgetDimensions.factorCount_le N hN
  omega

/-- The fixed original public scale pays both copies of every actual occurrence. -/
theorem root_edges_le_scale (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    edgeCount (root N hN fixed)≤SemiprimeD1PublicPackingReady.scale (bitLength N) := by
  rw [root_edges,wireCount_eq]
  have h:=variableCount_le (bitLength_pos hN)
  unfold SemiprimeD1PublicPackingReady.scale
  norm_num
  omega

/-- The original uniform scope envelope includes the equality/copy scopes. -/
theorem two_le_scope (L : ℕ) : 2 ≤ scopeBound L := by
  unfold scopeBound
  nlinarith

/-- Original root degree is bounded by its ACTUAL macro scope envelope. -/
theorem root_degree (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    DegreeBound (root N hN fixed) (scopeBound (bitLength N)) := by
  apply SemiprimeD1ChildStateResources.canonical_degree _ (acquirePositive_wellFormed N hN fixed) _
  · intro v
    change Fin (wireCount N) at v
    change (leftPorts (rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)) v).length≤_
    rw [SemiprimeD1RootPortCounts.original_owner_degree]
    have h:=owner_degree_le N hN fixed v
    simp only [SemiprimeD1RootTensorTables.ownerPorts,List.length_map] at h
    exact h.trans (two_le_scope _)
  · intro e
    change Fin (rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)).length at e
    let original : Fin (factorCount N):=⟨e.val,lt_of_lt_of_eq e.isLt
      (rows_length (SemiprimeD1RootTensorTables.acquirePositive N hN fixed))⟩
    have he : SemiprimeD1RootEntrySemantics.factorIndex N hN fixed original=e:=Fin.ext rfl
    change (rightPorts (rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)) e).length≤_
    rw [SemiprimeD1RootNetworkOrder.rightPorts_length]
    have ha := (congrArg (arity (rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed))) he).symm.trans
      (SemiprimeD1RootCoordinates.original_arity N hN fixed original)
    exact ha.trans_le (indexedArity_le N original)

/-- The actual root satisfies the ONE original-scale degree cap; no maximum
scope answer is an input to recursive resource theorems. -/
theorem root_global_degree (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    DegreeBound (root N hN fixed)
      (SemiprimeD1PackingReady.degreeCap (SemiprimeD1PublicPackingReady.scale (bitLength N))) := by
  intro v hv
  exact (root_degree N hN fixed v hv).trans
    (SemiprimeD1PublicPackingReady.actual_scope _ (bitLength_pos hN))

/-- Full actual root table/port/row data is bounded from N alone, including
all eager2^scope entries, rather than treating acquired tables as free input. -/
theorem root_inventory (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    inventory (root N hN fixed)≤
      (wireCount N+factorCount N)*(13*2^(scopeBound (bitLength N))+scopeBound (bitLength N))+
      2*wireCount N+factorCount N+1 := by
  have h:=inventory_bound SemiprimeD1RootOwnerTables.rootContext (root N hN fixed)
    (scopeBound (bitLength N)) (acquirePositive_good N hN fixed) (root_degree N hN fixed)
  rw [root_vertices,root_edges] at h
  have hr : (root N hN fixed).rows.length=factorCount N:=rows_length _
  simpa only [SemiprimeD1RootOwnerTables.rootContext,SemiprimeD1JetAxes.Context.rank,List.prod_nil,
    Nat.mul_one,Nat.one_mul,hr] using h

end RiemannGaussian.SemiprimeD1RootStateResources
