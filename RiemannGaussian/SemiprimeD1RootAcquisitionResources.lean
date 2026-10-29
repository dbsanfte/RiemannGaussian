/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootStateResources

/-! # Paid original root source plus its actual complete table copies
This bounds the retained physical/table/list report, including both acquisitions.
Native public configuration arithmetic and primitive tape lowering are separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1RootAcquisitionResources
open scoped BigOperators
open SemiprimeD1JetAxes SemiprimeD1TensorTables SemiprimeD1TensorNetwork
open SemiprimeD1RootNetwork SemiprimeD1RootTensorTables
open SemiprimeD1NetworkStateResources SemiprimeD1RootStateResources
open SemiprimeD1RootTensorTablesBounds SemiprimePublicAcquiredExecution SemiprimeMacroParameters
attribute [local irreducible] SemiprimeD1RootTensorTables.acquirePositive
attribute [local irreducible] wireCount factorCount indexedArity indexedCoordinate

/-- Actual cached source owner node, with zero fallback kept explicit. -/
def ownerAt {n F : ℕ} {arity : Fin F→ℕ} (data : Acquired n F arity) (v : Fin n) :=
  (data.owners[v.val]?).getD (defaultNode _)

/-- Actual cached source factor node, with zero fallback kept explicit. -/
def factorAt {n F : ℕ} {arity : Fin F→ℕ} (data : Acquired n F arity)
    (e : Fin (rows data).length) := (data.factors[e.val]?).getD (defaultNode _)

/-- Actual table-copy report envelope at the root scalar precision. -/
def copyBudget (D : ℕ) : ℕ := (18+4*D)*2^D

/-- Complete literal copy cost from actual source and target scope bounds. -/
theorem copy_clock {I : Type} (ports : List ℕ) (source : Node I) (D : ℕ)
    (hg : Good SemiprimeD1RootOwnerTables.rootContext source.table)
    (hs : source.ports.length ≤ D) (ht : ports.length ≤ D) :
    (copyNode ports source).2 ≤ copyBudget D := by
  have h:=copyNode_clock SemiprimeD1RootOwnerTables.rootContext ports source hg
  have hp:=Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) ht
  have hn : 18+4*source.ports.length ≤ 18+4*D:=by omega
  have he : SemiprimeD1RootOwnerTables.rootContext.rank*
      (3*SemiprimeD1RootOwnerTables.rootContext.precision+4)+4*source.ports.length+8=
      18+4*source.ports.length := by
    simp only [SemiprimeD1RootOwnerTables.rootContext,Context.rank,List.prod_nil]
    omega
  rw [he] at h
  exact h.trans (Nat.mul_le_mul hn hp)


/-- Whole literal assembly report, including every table copy and the acquired
source report once. The closed original-N theorem below supplies all shape facts. -/
theorem fromCache_clock {n F : ℕ} {arity : Fin F→ℕ} (data : Acquired n F arity) (D : ℕ)
    (hl : ∀v,Good SemiprimeD1RootOwnerTables.rootContext (ownerAt data v).table ∧
      (ownerAt data v).ports.length ≤ D ∧ (leftPorts (rows data) v).length ≤ D)
    (hr : ∀e,Good SemiprimeD1RootOwnerTables.rootContext (factorAt data e).table ∧
      (factorAt data e).ports.length ≤ D ∧ (rightPorts (rows data) e).length ≤ D) :
    (fromCache data).clock ≤ data.clock+(n+(rows data).length)*copyBudget D+
      10*(data.records.length+F+n+1)^3 := by
  have hleft : (∑v : Fin n,(copyNode (leftPorts (rows data) v) (ownerAt data v)).2) ≤ n*copyBudget D := by
    have h:=Finset.sum_le_sum (fun (v : Fin n) (_ : v∈Finset.univ)=>
      copy_clock _ _ D (hl v).1 (hl v).2.1 (hl v).2.2)
    simpa using h
  have hright : (∑e : Fin (rows data).length,(copyNode (rightPorts (rows data) e) (factorAt data e)).2) ≤
      (rows data).length*copyBudget D := by
    have h:=Finset.sum_le_sum (fun (e : Fin (rows data).length) (_ : e∈Finset.univ)=>
      copy_clock _ _ D (hr e).1 (hr e).2.1 (hr e).2.2)
    simpa using h
  unfold fromCache
  simp only [Vector.toList_ofFn,List.map_ofFn,Function.comp_def,List.sum_ofFn]
  change data.clock+(∑v : Fin n,(copyNode (leftPorts (rows data) v) (ownerAt data v)).2)+
    (∑e : Fin (rows data).length,(copyNode (rightPorts (rows data) e) (factorAt data e)).2)+
    10*(data.records.length+F+n+1)^3 ≤ _
  nlinarith

/-- Original binary-input root assembly budget; every table exponential retains
its actual original scope, rather than the full original wire count. -/
def budget (N P : ℕ) : ℕ :=
  SemiprimeD1RootTensorTablesBounds.budget N P+
    (wireCount N+factorCount N)*copyBudget (scopeBound (bitLength N))+
    10*(2*wireCount N+factorCount N+wireCount N+1)^3

/-- CLOSED retained original acquisition report, with no encoded table, scope,
source validity, entry truth or callback clock supplied as advice. -/
theorem acquirePositive_clock (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    (SemiprimeD1RootNetwork.acquirePositive N hN fixed).clock ≤ budget N fixed.length := by
  let data:=SemiprimeD1RootTensorTables.acquirePositive N hN fixed
  let D:=scopeBound (bitLength N)
  have hwell:=SemiprimeD1RootNetwork.acquirePositive_wellFormed N hN fixed
  have hdegree:=root_degree N hN fixed
  have hcopy:=fromCache_clock data D (by
    intro v
    have hsrc : ownerAt data v=ownerNode N fixed data.records v:=
      SemiprimeD1RootEntrySemantics.owner_cache_at N hN fixed v
    have hg : Good SemiprimeD1RootOwnerTables.rootContext (ownerAt data v).table := by
      rw [hsrc];exact ownerNode_good N fixed data.records v
    have hs : (ownerAt data v).ports.length ≤ D := by
      rw [hsrc]
      exact (owner_degree_le N hN fixed v).trans (two_le_scope _)
    have ht:=hdegree _ (SemiprimeD1TensorNetworkRecursion.left_mem (root N hN fixed) v)
    rw [hwell.1 v] at ht
    exact ⟨hg,hs,ht⟩) (by
    intro e
    let original : Fin (factorCount N):=⟨e.val,lt_of_lt_of_eq e.isLt (rows_length data)⟩
    have hsrc : factorAt data e=factorNode N hN original:=
      SemiprimeD1RootEntrySemantics.factor_cache_at N hN fixed original
    have hg : Good SemiprimeD1RootOwnerTables.rootContext (factorAt data e).table := by
      rw [hsrc];exact factorNode_good N hN original
    have hs : (factorAt data e).ports.length ≤ D := by
      rw [hsrc];exact factor_degree_le N hN original
    have ht:=hdegree _ (SemiprimeD1TensorNetworkRecursion.right_mem (root N hN fixed) e)
    rw [hwell.2 e] at ht
    exact ⟨hg,hs,ht⟩)
  have hsource:=SemiprimeD1RootTensorTablesBounds.acquirePositive_clock N hN fixed
  have hrecords : data.records.length=2*wireCount N:=
    (records_length N hN fixed).trans (indexed_incidence_count N hN)
  rw [rows_length,hrecords] at hcopy
  change data.clock ≤ SemiprimeD1RootTensorTablesBounds.budget N fixed.length at hsource
  exact hcopy.trans (Nat.add_le_add_right (Nat.add_le_add_right hsource _) _)

end RiemannGaussian.SemiprimeD1RootAcquisitionResources
