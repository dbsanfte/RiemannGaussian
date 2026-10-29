/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootEntrySemantics
import RiemannGaussian.SemiprimeD1TensorNetworkFactorization

/-! # Exact original coordinates in actual root occurrence/port order
Every factor port is its original indexed coordinate, derived from cached rows
and the actual canonical edge index search. No bijection is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace RiemannGaussian.SemiprimeD1RootCoordinates
open SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkLayout SemiprimeD1RootEntrySemantics
open SemiprimePublicAcquiredExecution SemiprimeD1RootNetworkOrder
noncomputable section

/-- Original factor degree is the actual acquired row degree. -/
theorem original_arity (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (e : Fin (factorCount N)) :
    arity (SemiprimeD1RootNetwork.rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed))
      (factorIndex N hN fixed e)=indexedArity N e := original_row_length N hN fixed e

/-- Original local port in the actual typed root row layout. -/
def portIndex (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (e : Fin (factorCount N)) (j : Fin (indexedArity N e)) :
    Incidence (SemiprimeD1RootNetwork.rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)) :=
  ⟨factorIndex N hN fixed e,⟨j.val,by rw [original_arity]; exact j.isLt⟩⟩

/-- The actual root row owner read is its literal original public coordinate. -/
theorem owner_portIndex (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (e : Fin (factorCount N)) (j : Fin (indexedArity N e)) :
    owner (SemiprimeD1RootNetwork.rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed))
      (portIndex N hN fixed e j)=indexedCoordinate N hN e j := by
  have he : e.val<(SemiprimeD1RootNetwork.rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)).length :=
    (factorIndex N hN fixed e).isLt
  let row := (SemiprimeD1RootNetwork.rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed))[e.val]'he
  have hr : row=(List.finRange (indexedArity N e)).map (indexedCoordinate N hN e) := original_row N hN fixed e
  have hj : j.val<row.length := by
    rw [hr,List.length_map,List.length_finRange]
    exact j.isLt
  have hf : j.val<(List.finRange (indexedArity N e)).length := by
    simpa only [List.length_finRange] using j.isLt
  have hg := congrArg (fun xs : List (Fin (wireCount N)) => xs[j.val]?) hr
  rw [List.getElem?_eq_getElem hj,List.getElem?_map,List.getElem?_eq_getElem hf] at hg
  have hg' := Option.some.inj hg
  have hfin : (List.finRange (indexedArity N e))[j.val]'hf=j := by
    apply Fin.ext
    simp only [List.getElem_finRange,Fin.val_cast]
  calc
    _ = row[j.val] := rfl
    _ = indexedCoordinate N hN e ((List.finRange (indexedArity N e))[j.val]) := hg'
    _ = _ := congrArg (indexedCoordinate N hN e) hfin

/-- Canonical right-port ordering retains each original local port's exact
computed global occurrence identifier. -/
theorem right_port_at (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (e : Fin (factorCount N)) (j : Fin (indexedArity N e)) :
    (rightPorts (SemiprimeD1RootNetwork.rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed))
      (factorIndex N hN fixed e))[j.val]?=
      some (edgeID (SemiprimeD1RootNetwork.rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed))
        (portIndex N hN fixed e j)) := by
  rw [rightPorts_order,List.getElem?_map]
  have hj : j.val<(List.finRange (arity
      (SemiprimeD1RootNetwork.rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed))
      (factorIndex N hN fixed e))).length := by
    rw [List.length_finRange,original_arity]
    exact j.isLt
  rw [List.getElem?_eq_getElem hj]
  simp only [Option.map_some]
  congr 1
  apply congrArg (fun k => edgeID
    (SemiprimeD1RootNetwork.rows (SemiprimeD1RootTensorTables.acquirePositive N hN fixed))
    ⟨factorIndex N hN fixed e,k⟩)
  apply Fin.ext
  simp only [List.getElem_finRange,Fin.val_cast]

/-- An actual canonical global read of pulled-back owner bits is exactly its
original occurrence owner, with the literal edgeID/edgeEquiv index search. -/
theorem pullback_read {n : ℕ} (rs : Rows n) (bits : Fin n→Bool) (p : Incidence rs) :
    ((List.ofFn (fun j : Fin (scope rs) => bits (leftGroup rs j)))[edgeID rs p]?).getD false=bits (owner rs p) := by
  have hp := edgeID_lt rs p
  rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using hp)]
  simp only [List.getElem_ofFn,Option.getD_some]
  have he : (⟨edgeID rs p,hp⟩ : Fin (scope rs))=edgeEquiv rs p := Fin.ext rfl
  rw [he]
  change bits (owner rs ((edgeEquiv rs).symm (edgeEquiv rs p)))=_
  rw [Equiv.symm_apply_apply]

end
end RiemannGaussian.SemiprimeD1RootCoordinates
