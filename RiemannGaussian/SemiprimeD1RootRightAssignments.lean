/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootLocalAssignments
import RiemannGaussian.SemiprimeD1RootCoordinates

/-! # Original arithmetic factors on consistent acquired incidence assignments
Canonical right-port reads are the original local coordinate order, proved from
actual cached rows and edge indices rather than supplied as a correspondence.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace RiemannGaussian.SemiprimeD1RootRightAssignments
open SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkLayout SemiprimeD1RootNetworkOrder
open SemiprimeD1RootLocalAssignments SemiprimeD1RootCoordinates SemiprimeD1RootEntrySemantics
open SemiprimeD1LeafCounter SemiprimeD1TensorTables SemiprimeD1RootScalar SemiprimeD1JetInterpretation
open SemiprimePublicAcquiredExecution
noncomputable section

/-- Internal canonical row-layout read; the original endpoint below supplies
its actual cached vertex and proves the original coordinate transport. -/
theorem right_bits_general {n : ℕ} (rs : Rows n) (e : Fin rs.length) (vertex : Vertex)
    (hp : vertex.ports=rightPorts rs e) (bits : Fin n→Bool) :
    vertex.ports.map (fun p => ((List.ofFn (fun j : Fin (scope rs) => bits (leftGroup rs j)))[p]?).getD false)=
      List.ofFn (fun j : Fin (arity rs e) => bits (owner rs ⟨e,j⟩)) := by
  have hl : vertex.ports.length=arity rs e := by rw [hp,rightPorts_length]
  apply List.ext_getElem
  · rw [List.length_map,List.length_ofFn,hl]
  · intro k hk hk'
    have hka : k<arity rs e := by simpa only [List.length_ofFn] using hk'
    have hkP : k<vertex.ports.length := by simpa only [List.length_map] using hk
    have hget := congrArg (fun ps : List ℕ => ps[k]?) hp
    rw [rightPorts_order,List.getElem?_map] at hget
    have hkr : k<(List.finRange (arity rs e)).length := by simpa only [List.length_finRange] using hka
    rw [List.getElem?_eq_getElem hkP,List.getElem?_eq_getElem hkr] at hget
    have hid := Option.some.inj hget
    rw [List.getElem_map,List.getElem_ofFn,hid,pullback_read]
    congr 2
    congr 1
    apply Fin.ext
    simp only [List.getElem_finRange,Fin.val_cast]

/-- Literal global gather into an actual factor is exactly the original
coordinate vector when original owner bits are pulled back to incidences. -/
theorem right_bits (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (bits : Fin (wireCount N)→Bool) (e : Fin (factorCount N)) :
    let rs := SemiprimeD1RootNetwork.rows (source N hN fixed)
    (rightPorts rs (factorIndex N hN fixed e)).map (fun p =>
      ((List.ofFn (fun j : Fin (scope rs) => bits (leftGroup rs j)))[p]?).getD false)=
      List.ofFn (fun j : Fin (indexedArity N e) => bits (indexedCoordinate N hN e j)) := by
  let rs := SemiprimeD1RootNetwork.rows (source N hN fixed)
  apply List.ext_getElem
  · rw [List.length_map,rightPorts_length,List.length_ofFn,original_arity N hN fixed e]
  · intro k hk hk'
    have hka : k < indexedArity N e := by simpa only [List.length_ofFn] using hk'
    let j : Fin (indexedArity N e) := ⟨k,hka⟩
    have hp := right_port_at N hN fixed e j
    have hkP : k < (rightPorts rs (factorIndex N hN fixed e)).length := by simpa only [List.length_map] using hk
    rw [List.getElem?_eq_getElem hkP] at hp
    have he := Option.some.inj hp
    rw [List.getElem_map,he,pullback_read,List.getElem_ofFn]
    exact congrArg bits (owner_portIndex N hN fixed e j)

/-- A canonical right vertex, kept opaque while original caches are inserted. -/
def rightVertex {n F : ℕ} {arity : Fin F→ℕ}
    (data : SemiprimeD1RootTensorTables.Acquired n F arity)
    (e : Fin (SemiprimeD1RootNetwork.rows data).length) : Vertex :=
  (SemiprimeD1RootNetwork.fromCache data).network.right[e.val]'e.isLt

/-- The canonical right vertex's literal port fibre. -/
theorem rightVertex_ports {n F : ℕ} {arity : Fin F→ℕ}
    (data : SemiprimeD1RootTensorTables.Acquired n F arity)
    (e : Fin (SemiprimeD1RootNetwork.rows data).length) :
    (rightVertex data e).ports=rightPorts (SemiprimeD1RootNetwork.rows data) e :=
  (SemiprimeD1RootNetwork.fromCache_wellFormed data).2 e

/-- Opaque scalar local-entry wrapper prevents normalization of acquired metadata
while elaborating a dependent table/assignment pair. -/
def scalarEntry {M : ℕ} (vertex : Vertex) (a : Fin M→Bool) : ZMod 4 :=
  scalar (interpret ⟨[],2⟩ (valueAt vertex.table (localAssignment a vertex)))

/-- Local gather refinement, proved before inserting any acquired cache. -/
theorem scalarEntry_lookup {M : ℕ} (vertex : Vertex) (a : Fin M→Bool) :
    scalarEntry vertex a=scalar (interpret ⟨[],2⟩ (lookup vertex.table
      (vertex.ports.map (fun p => ((List.ofFn a)[p]?).getD false))).words) := by
  unfold scalarEntry
  rw [valueAt_global_lookup]

/-- Canonical owner-bit pullback, kept behind its typed function interface. -/
def originalAssignment (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (bits : Fin (wireCount N)→Bool) :
    Fin (scope (SemiprimeD1RootNetwork.rows (source N hN fixed)))→Bool :=
  fun j => bits (leftGroup (SemiprimeD1RootNetwork.rows (source N hN fixed)) j)

/-- Canonical original factor vertex, with actual computed index hidden. -/
def originalVertex (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (e : Fin (factorCount N)) : Vertex :=
  rightVertex (source N hN fixed) (factorIndex N hN fixed e)

/-- Actual root factor entry on a consistent owner assignment is the actual
original indexed arithmetic checker, with no truth-function advice. -/
theorem factor_entry (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool))
    (bits : Fin (wireCount N)→Bool) (e : Fin (factorCount N)) :
    scalarEntry (originalVertex N hN fixed e) (originalAssignment N hN fixed bits)=
      if (indexedEntry N hN e (fun j => bits (indexedCoordinate N hN e j))).accepted then (1:ZMod 4) else 0 := by
  let rs := SemiprimeD1RootNetwork.rows (source N hN fixed)
  let a := fun j : Fin (scope rs) => bits (leftGroup rs j)
  let vertex := rightVertex (source N hN fixed) (factorIndex N hN fixed e)
  let input := vertex.ports.map (fun p => ((List.ofFn a)[p]?).getD false)
  have hi : input=List.ofFn (fun j : Fin (indexedArity N e) => bits (indexedCoordinate N hN e j)) := by
    have hp := rightVertex_ports (source N hN fixed) (factorIndex N hN fixed e)
    change vertex.ports.map _=_
    rw [hp]
    exact right_bits N hN fixed bits e
  have hl : input.length=indexedArity N e := by rw [hi,List.length_ofFn]
  have hinput : (fun j : Fin (indexedArity N e) => (input.toArray[j.val]?).getD false)=
      (fun j => bits (indexedCoordinate N hN e j)) := by
    funext j
    rw [hi,List.getElem?_toArray,List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using j.isLt)]
    simp only [List.getElem_ofFn,Option.getD_some]
  change scalarEntry vertex a=_
  rw [scalarEntry_lookup]
  have h := original_factor_scalar N hN fixed e input hl
  exact h.trans (congrArg (fun f : Fin (indexedArity N e)→Bool =>
    if (indexedEntry N hN e f).accepted then (1:ZMod 4) else 0) hinput)

end
end RiemannGaussian.SemiprimeD1RootRightAssignments
