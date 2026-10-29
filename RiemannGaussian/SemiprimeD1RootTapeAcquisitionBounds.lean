/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootAcquisitionResources
import RiemannGaussian.SemiprimeD1RootTapeNetwork

/-! # Actual tape-root acquisition bound from the original input
The unchanged original source and every new serialized table recopy are paid.
No clock equality with the old root copier is asserted. Native configuration,
array/index/control and whole machine lowering remain separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1RootTapeAcquisitionBounds
open scoped BigOperators
open SemiprimeD1JetAxes SemiprimeD1TensorTables SemiprimeD1TensorNetwork
open SemiprimeD1RootNetwork (rows rows_length defaultNode)
open SemiprimeD1RootTapeNetwork SemiprimeD1RootTensorTables
open SemiprimeD1RootAcquisitionResources (ownerAt factorAt)
open SemiprimeD1ChildNetworkTape (copyTable)
open SemiprimeD1NetworkStateResources SemiprimeD1RootStateResources
open SemiprimeD1RootTensorTablesBounds SemiprimePublicAcquiredExecution SemiprimeMacroParameters
attribute [local irreducible] SemiprimeD1RootTensorTables.acquirePositive
attribute [local irreducible] wireCount factorCount indexedArity indexedCoordinate

/-- Actual table-copy report envelope at the root scalar precision. -/
def copyBudget (D : ℕ) : ℕ := (72*(D+2)*2^D+11)*2^D

/-- Actual tape serialization and every subtree scan are paid at every entry. -/
theorem copy_clock {I : Type} (ports : List ℕ) (source : Node I) (D : ℕ)
    (hg : Good SemiprimeD1RootOwnerTables.rootContext source.table)
    (hs : source.ports.length ≤ D) (ht : ports.length ≤ D) :
    (copyTable ports source.table).2 ≤ copyBudget D := by
  have hlookup (bits : List Bool) :
      (SemiprimeD1TensorTapeLookup.fromTable source.table bits).clock ≤
        72*(D+2)*2^D+4 := by
    have h:=SemiprimeD1TensorTapeLookup.fromTable_good_clock
      SemiprimeD1RootOwnerTables.rootContext source.table hg bits
    simp only [SemiprimeD1RootOwnerTables.rootContext,Context.rank,List.prod_nil] at h
    apply h.trans
    calc
      _ = 72*(source.ports.length+2)*2^source.ports.length+4 := by ring
      _ ≤ _ := by gcongr
  have h:=build_clock ports.length (72*(D+2)*2^D+4)
    (fun bits=>SemiprimeD1TensorTapeLookup.fromTable source.table bits)
    (fun bits _=>hlookup bits)
  have hp:=Nat.pow_le_pow_right (by decide:0<(2:ℕ)) ht
  have hm:=Nat.mul_le_mul_left (72*(D+2)*2^D+11) hp
  rw [show 72*(D+2)*2^D+4+7=72*(D+2)*2^D+11 by omega] at h
  change (build ports.length (fun bits=>SemiprimeD1TensorTapeLookup.fromTable source.table bits)).clock+3≤_
  unfold copyBudget
  omega

/-- Whole literal assembly report, including every table copy and the acquired
source report once. The closed original-N theorem below supplies all shape facts. -/
theorem fromCache_clock {n F : ℕ} {arity : Fin F→ℕ} (data : Acquired n F arity) (D : ℕ)
    (hl : ∀v,Good SemiprimeD1RootOwnerTables.rootContext (ownerAt data v).table ∧
      (ownerAt data v).ports.length ≤ D ∧ (leftPorts (rows data) v).length ≤ D)
    (hr : ∀e,Good SemiprimeD1RootOwnerTables.rootContext (factorAt data e).table ∧
      (factorAt data e).ports.length ≤ D ∧ (rightPorts (rows data) e).length ≤ D) :
    (fromCache data).clock ≤ data.clock+(n+(rows data).length)*copyBudget D+
      10*(data.records.length+F+n+1)^3 := by
  have hleft : (∑v : Fin n,(copyTable (leftPorts (rows data) v) (ownerAt data v).table).2) ≤ n*copyBudget D := by
    have h:=Finset.sum_le_sum (fun (v : Fin n) (_ : v∈Finset.univ)=>
      copy_clock _ _ D (hl v).1 (hl v).2.1 (hl v).2.2)
    simpa using h
  have hright : (∑e : Fin (rows data).length,(copyTable (rightPorts (rows data) e) (factorAt data e).table).2) ≤
      (rows data).length*copyBudget D := by
    have h:=Finset.sum_le_sum (fun (e : Fin (rows data).length) (_ : e∈Finset.univ)=>
      copy_clock _ _ D (hr e).1 (hr e).2.1 (hr e).2.2)
    simpa using h
  unfold fromCache
  simp only [Vector.toList_ofFn,List.map_ofFn,Function.comp_def,List.sum_ofFn]
  change data.clock+(∑v : Fin n,(copyTable (leftPorts (rows data) v) (ownerAt data v).table).2)+
    (∑e : Fin (rows data).length,(copyTable (rightPorts (rows data) e) (factorAt data e).table).2)+
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
    (SemiprimeD1RootTapeNetwork.acquirePositive N hN fixed).clock ≤ budget N fixed.length := by
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

end RiemannGaussian.SemiprimeD1RootTapeAcquisitionBounds
