/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorNetwork
import RiemannGaussian.SemiprimeD1ChildGraphInterface
import Mathlib.Data.List.NodupEquivFin

/-! # Exact finite-variable partitions of literal network caches
All global and local relabellings below use actual list entries and index
searches. They certify the partitions needed for multilinear factorization;
they are not permutation or entry-value inputs to the acquisition algorithm.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace RiemannGaussian.SemiprimeD1TensorNetworkLayout
open scoped BigOperators
open SemiprimeD1TensorNetwork

/-- Occurrence-to-global-variable bijection is the actual finite index search. -/
def edgeEquiv {n : ℕ} (rows : Rows n) : Incidence rows ≃ Fin (scope rows) :=
  (List.Nodup.getEquivOfForallMemList (incidences rows) (incidences_nodup rows)
    (incidence_mem rows)).symm

/-- The global bijection's native identifier is exactly the executed search. -/
theorem edgeEquiv_val {n : ℕ} (rows : Rows n) (i : Incidence rows) :
    (edgeEquiv rows i).val = edgeID rows i := rfl

/-- Read the actual left owner of a canonical global variable. -/
def leftGroup {n : ℕ} (rows : Rows n) (j : Fin (scope rows)) : Fin n :=
  owner rows ((edgeEquiv rows).symm j)

/-- Read the actual factor owner of a canonical global variable. -/
def rightGroup {n : ℕ} (rows : Rows n) (j : Fin (scope rows)) : Fin rows.length :=
  ((edgeEquiv rows).symm j).1

/-- Every actual global variable belongs to precisely its left owner's port list. -/
theorem leftGroup_mem {n : ℕ} (rows : Rows n) (v : Fin n) (j : Fin (scope rows)) :
    j.val ∈ leftPorts rows v ↔ leftGroup rows j = v := by
  have h := edgeID_mem_leftPorts rows v ((edgeEquiv rows).symm j)
  rw [← edgeEquiv_val, (edgeEquiv rows).apply_symm_apply] at h
  exact h

/-- Every actual global variable belongs to precisely its factor's port list. -/
theorem rightGroup_mem {n : ℕ} (rows : Rows n) (e : Fin rows.length) (j : Fin (scope rows)) :
    j.val ∈ rightPorts rows e ↔ rightGroup rows j = e := by
  have h := edgeID_mem_rightPorts rows e ((edgeEquiv rows).symm j)
  rw [← edgeEquiv_val, (edgeEquiv rows).apply_symm_apply] at h
  exact h

/-- An actual nodup port list that is one full fibre has a computed local/global
bijection. Its inverse is the literal list index search, including empty fibres. -/
def portEquiv {M : ℕ} {G : Type*} (group : Fin M → G) (g : G) (ports : List ℕ)
    (hb : ∀ p ∈ ports, p < M) (hn : ports.Nodup)
    (hm : ∀ j : Fin M, j.val ∈ ports ↔ group j = g) :
    Fin ports.length ≃ {j // group j = g} where
  toFun i :=
    let j : Fin M := ⟨ports[i.val], hb _ (List.getElem_mem i.isLt)⟩
    ⟨j, (hm j).mp (List.getElem_mem i.isLt)⟩
  invFun j := ⟨ports.idxOf j.val.val, List.idxOf_lt_length_of_mem ((hm j.val).mpr j.property)⟩
  left_inv i := by
    apply Fin.ext
    exact hn.idxOf_getElem i.val i.isLt
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    exact List.getElem_idxOf (List.idxOf_lt_length_of_mem ((hm j.val).mpr j.property))

/-- The local/global bijection reads exactly the literal cached port index. -/
theorem portEquiv_val {M : ℕ} {G : Type*} (group : Fin M → G) (g : G) (ports : List ℕ)
    (hb : ∀ p ∈ ports, p < M) (hn : ports.Nodup)
    (hm : ∀ j : Fin M, j.val ∈ ports ↔ group j = g) (i : Fin ports.length) :
    ((portEquiv group g ports hb hn hm i).val).val = ports[i.val] := rfl

/-- The complete actual local left tensor scope is one fibre of the global owner map. -/
def leftEquiv {n : ℕ} (rows : Rows n) (v : Fin n) :
    Fin (leftPorts rows v).length ≃ {j // leftGroup rows j = v} :=
  portEquiv (leftGroup rows) v (leftPorts rows v) (leftPorts_lt rows v)
    (leftPorts_nodup rows v) (leftGroup_mem rows v)

/-- The complete actual local factor scope is one fibre of the global factor map. -/
def rightEquiv {n : ℕ} (rows : Rows n) (e : Fin rows.length) :
    Fin (rightPorts rows e).length ≃ {j // rightGroup rows j = e} :=
  portEquiv (rightGroup rows) e (rightPorts rows e) (rightPorts_lt rows e)
    (rightPorts_nodup rows e) (rightGroup_mem rows e)

/-- The sparse selector's original metadata is the SAME actual factor-major list. -/
theorem original_ports {n : ℕ} (rows : Rows n) (Q : ℕ) :
    SemiprimeD1CollisionOriginal.ports n rows.length Q (arity rows) = incidences rows := by
  simp only [SemiprimeD1CollisionOriginal.ports, SemiprimeSourceHistogramMetadata.acquire,
    SemiprimePaidFiniteEnumerationLists.flat_value, SemiprimeSourceHistogramMetadata.finFast_value,
    SemiprimeSourceHistogramMetadata.ports_value, incidences,
    SemiprimeFiniteEnumerations.indexedIncidences, SemiprimeFiniteEnumerations.sigma,
    SemiprimeFiniteEnumerations.fin]

/-- Actual child cached endpoint rows, with no external incidence-map supplier. -/
def childRows {V : ℕ} (graph : SemiprimeD1ChildGraph.Graph V) : Rows V :=
  graph.factors.map (List.map SemiprimeD1ChildGraph.Endpoint.vertex)

/-- The row adapter preserves the actual observed packet-factor count. -/
theorem childRows_length {V : ℕ} (graph : SemiprimeD1ChildGraph.Graph V) :
    (childRows graph).length = graph.factors.length := List.length_map _

/-- Actual global child scope is exactly the literal cached endpoint count. -/
theorem child_scope {V : ℕ} (graph : SemiprimeD1ChildGraph.Graph V) :
    scope (childRows graph) = graph.factors.flatten.length := by
  rw [scope_eq_sum]
  have hsum : (∑ e : Fin (childRows graph).length, arity (childRows graph) e) =
      (((childRows graph).map List.length).sum) := by
    simpa only [arity, List.map_ofFn, Function.comp_def, List.sum_ofFn] using
      congrArg (fun xs : List (List (Fin V)) => (xs.map List.length).sum)
        (List.ofFn_getElem (xs := childRows graph))
  rw [hsum]
  simp only [childRows, List.map_map, Function.comp_def, List.length_map, List.length_flatten]

/-- Concrete layout gives the local distinct-variable property needed by the
leaf storage bound; it is DERIVED, rather than a caller's scope promise. -/
theorem vertex_ports_nodup (net : Network) (hw : WellFormed net)
    (v : SemiprimeD1LeafCounter.Vertex) (hv : v ∈ vertices net) : v.ports.Nodup := by
  rcases List.mem_append.mp hv with hl | hr
  · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hl
    rw [Vector.getElem_toList] at he
    subst v
    rw [hw.1 ⟨i, by simpa only [Vector.length_toList] using hi⟩]
    exact leftPorts_nodup net.rows _
  · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hr
    rw [Vector.getElem_toList] at he
    subst v
    rw [hw.2 ⟨i, by simpa only [Vector.length_toList] using hi⟩]
    exact rightPorts_nodup net.rows _

end RiemannGaussian.SemiprimeD1TensorNetworkLayout
