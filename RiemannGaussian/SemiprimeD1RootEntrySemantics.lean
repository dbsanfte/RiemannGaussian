/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootScalar
import RiemannGaussian.SemiprimeD1RootPortCounts

/-! # Actual root copied-table entries retain original producer semantics
All finite cache bounds and local factor orders are derived from the original
root constructor; no table-entry verdict is supplied to these endpoints.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace RiemannGaussian.SemiprimeD1RootEntrySemantics
open SemiprimeD1RootTensorTables SemiprimeD1RootNetwork SemiprimeD1RootNetworkOrder
open SemiprimeD1TensorNetwork SemiprimeD1TensorTables SemiprimeD1RootScalar
open SemiprimeD1JetInterpretation SemiprimeD1RootOwnerTables
open SemiprimePublicAcquiredExecution
noncomputable section

/-- Actual canonical factor copy reads the same acquired local source table. -/
theorem fromCache_right_lookup {n F : ℕ} {arity : Fin F→ℕ}
    (data : Acquired n F arity) (e : Fin (fromCache data).network.rows.length)
    (bits : List Bool) (hb : bits.length=(rightPorts (fromCache data).network.rows e).length) :
    (lookup ((fromCache data).network.right[e.val]).table bits).words=
      (lookup (data.factors[e.val]?.getD (defaultNode _)).table bits).words := by
  have hv : (fromCache data).network.right[e.val]=
      (copyNode (rightPorts (fromCache data).network.rows e)
        (data.factors[e.val]?.getD (defaultNode _))).1 := by
    simp only [fromCache,Vector.getElem_map,Vector.getElem_ofFn]
    congr 1
  exact (congrArg (fun v : SemiprimeD1LeafCounter.Vertex => (lookup v.table bits).words) hv).trans
    (copyNode_value _ _ bits hb)

/-- Actual canonical owner copy reads the same acquired local source table. -/
theorem fromCache_left_lookup {n F : ℕ} {arity : Fin F→ℕ}
    (data : Acquired n F arity) (v : Fin (fromCache data).network.leftCount)
    (bits : List Bool) (hb : bits.length=(leftPorts (fromCache data).network.rows v).length) :
    (lookup ((fromCache data).network.left[v.val]).table bits).words=
      (lookup (data.owners[v.val]?.getD (defaultNode _)).table bits).words := by
  have hv : (fromCache data).network.left[v.val]=
      (copyNode (leftPorts (fromCache data).network.rows v)
        (data.owners[v.val]?.getD (defaultNode _))).1 := by
    simp only [fromCache,Vector.getElem_map,Vector.getElem_ofFn]
    congr 1
  exact (congrArg (fun v : SemiprimeD1LeafCounter.Vertex => (lookup v.table bits).words) hv).trans
    (copyNode_value _ _ bits hb)

/-- Every requested original factor cache cell is present and exactly its
actually materialized original factor node. -/
theorem factor_cache_at (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (e : Fin (factorCount N)) :
    ((SemiprimeD1RootTensorTables.acquirePositive N hN fixed).factors[e.val]?).getD (defaultNode _)=factorNode N hN e := by
  rw [acquirePositive_factors,List.getElem?_map]
  have he : e.val<(List.finRange (factorCount N)).length := by simpa only [List.length_finRange] using e.isLt
  rw [List.getElem?_eq_getElem he]
  simp only [List.getElem_finRange,Option.map_some,Option.getD_some]
  congr 1

/-- Every original owner cache cell is present, including isolated owners. -/
theorem owner_cache_at (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (v : Fin (wireCount N)) :
    ((SemiprimeD1RootTensorTables.acquirePositive N hN fixed).owners[v.val]?).getD (defaultNode _)=
      ownerNode N fixed (SemiprimeD1RootTensorTables.acquirePositive N hN fixed).records v := by
  rw [acquirePositive_owners,List.getElem?_map]
  have hv : v.val<(List.finRange (wireCount N)).length := by simpa only [List.length_finRange] using v.isLt
  rw [List.getElem?_eq_getElem hv]
  simp only [List.getElem_finRange,Option.map_some,Option.getD_some]
  congr 1

/-- Original factor index in the actual cached row vector, computed by its
proved constructor length. -/
def factorIndex (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (e : Fin (factorCount N)) : Fin
      (SemiprimeD1RootNetwork.rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)).length :=
  ⟨e.val,by rw [rows_length]; exact e.isLt⟩

/-- Actual factor vertex behind a nondependent typed cache interface. -/
def factorVertex (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (e : Fin (factorCount N)) : SemiprimeD1LeafCounter.Vertex :=
  (fromCache (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)).network.right[
    (factorIndex N hN fixed e).val]'(factorIndex N hN fixed e).isLt

/-- Actual original owner vertex behind a nondependent typed cache interface. -/
def ownerVertex (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (v : Fin (wireCount N)) : SemiprimeD1LeafCounter.Vertex :=
  (fromCache (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)).network.left[v.val]'v.isLt

/-- Actual acquired root factor table produces the original public arithmetic
checker at exactly the original local port order. -/
theorem original_factor_lookup (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (e : Fin (factorCount N)) (bits : List Bool) (hb : bits.length=indexedArity N e) :
    (lookup (factorVertex N hN fixed e).table bits).words=(factorProducer N hN e bits).words := by
  have hl : bits.length=(rightPorts
      (fromCache (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)).network.rows
      (factorIndex N hN fixed e)).length := by
    change bits.length=(rightPorts (SemiprimeD1RootNetwork.rows
      (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)) (factorIndex N hN fixed e)).length
    rw [rightPorts_length]
    exact hb.trans (original_row_length N hN fixed e).symm
  have h := fromCache_right_lookup (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)
    (factorIndex N hN fixed e) bits hl
  calc
    _ = (lookup ((SemiprimeD1RootTensorTables.acquirePositive N hN fixed).factors[e.val]?.getD (defaultNode _)).table bits).words := h
    _ = _ := by rw [factor_cache_at N hN fixed e,factorNode_value N hN e bits hb]

/-- Root scalar decoding of the actual factor entry is the original checker
indicator modulo four, with no supplied local truth predicate. -/
theorem original_factor_scalar (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (e : Fin (factorCount N)) (bits : List Bool) (hb : bits.length=indexedArity N e) :
    scalar (interpret rootContext
      (lookup (factorVertex N hN fixed e).table bits).words)=
      if (indexedEntry N hN e (fun i => (bits.toArray[i.val]?).getD false)).accepted then (1:ZMod 4) else 0 := by
  rw [original_factor_lookup N hN fixed e bits hb]
  change scalar (interpret ⟨[],2⟩ (factorProducer N hN e bits).words)=_
  rw [scalar_interpret]
  exact factorProducer_value N hN e bits

/-- The actual owner-copy node is read at its proved canonical fibre degree,
including a zero-port isolated owner. -/
theorem original_owner_lookup (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (v : Fin (wireCount N)) (bits : List Bool)
    (hb : bits.length=(leftPorts (SemiprimeD1RootNetwork.rows
      (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)) v).length) :
    (lookup (ownerVertex N hN fixed v).table bits).words=
      (SemiprimeD1RootOwnerTables.producer fixed v bits).words := by
  have h := fromCache_left_lookup (SemiprimeD1RootTensorTables.acquirePositive N hN fixed) v bits hb
  calc
    _ = (lookup ((SemiprimeD1RootTensorTables.acquirePositive N hN fixed).owners[v.val]?.getD (defaultNode _)).table bits).words := h
    _ = _ := by
      rw [owner_cache_at N hN fixed v]
      apply ownerNode_value
      rw [ownerPorts,List.length_map]
      exact hb.trans (SemiprimeD1RootPortCounts.original_owner_degree _ v)

/-- The actual root scalar owner entry is its complete original two-value
prefix-compatible copy weight, retaining isolated-variable multiplicity. -/
theorem original_owner_scalar (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (v : Fin (wireCount N)) (bits : List Bool)
    (hb : bits.length=(leftPorts (SemiprimeD1RootNetwork.rows
      (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)) v).length) :
    scalar (interpret rootContext
      (lookup (ownerVertex N hN fixed v).table bits).words)=
      (SemiprimeD1RootOwnerTables.weight fixed v bits : ZMod 4) := by
  rw [original_owner_lookup N hN fixed v bits hb]
  change scalar (interpret ⟨[],2⟩ (SemiprimeD1RootOwnerTables.producer fixed v bits).words)=_
  rw [scalar_interpret]
  exact SemiprimeD1RootOwnerTables.producer_value fixed v bits

end
end RiemannGaussian.SemiprimeD1RootEntrySemantics
