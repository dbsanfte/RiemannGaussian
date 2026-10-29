/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryLeaf
import RiemannGaussian.SemiprimeD1BoundaryRefinement
import RiemannGaussian.SemiprimeD1BoundaryIdentity
import RiemannGaussian.SemiprimeD1BoundaryChoice

/-! # Literal class and merge port metadata

The original ordered occurrence list supplies every address. Distinct ordinals
remain distinct for parallel incidences, and all vertices are retained.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryLeafPorts
open SemiprimeD1BoundaryLeaf
open SemiprimeD1BoundaryRefinement

/-- The ordinal scan used by both executed class-port filters. -/
def selectedIndices {α : Type} (xs : List α) (p : α × Nat → Bool) : List Nat :=
  ((xs.zipIdx).filter p).map Prod.snd

/-- Selection returns exactly the original address whose predicate succeeds. -/
theorem selectedIndices_mem {α : Type} (xs : List α) (p : α × Nat → Bool)
    (i : Nat) (hi : i < xs.length) :
    i ∈ selectedIndices xs p ↔ p (xs[i], i) = true := by
  constructor
  · intro h
    obtain ⟨x, hx, he⟩ := List.mem_map.mp h
    obtain ⟨hm, hp⟩ := List.mem_filter.mp hx
    have hg := List.mem_zipIdx' hm
    have hxe : x = (xs[i], i) := by
      apply Prod.ext
      · simpa only [he] using hg.2
      · exact he
    exact hxe ▸ hp
  · intro hp
    apply List.mem_map.mpr
    refine ⟨(xs[i], i), List.mem_filter.mpr ⟨?_, hp⟩, rfl⟩
    exact List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)

/-- Every selected ordinal is an actual original occurrence. -/
theorem selectedIndices_lt {α : Type} (xs : List α) (p : α × Nat → Bool)
    (i : Nat) (hi : i ∈ selectedIndices xs p) : i < xs.length := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hi
  exact (List.mem_zipIdx' (List.mem_filter.mp hx).1).1

/-- Filtering never duplicates an original occurrence ordinal. -/
theorem selectedIndices_nodup {α : Type} (xs : List α) (p : α × Nat → Bool) :
    (selectedIndices xs p).Nodup := by
  exact List.Nodup.sublist (List.Sublist.map Prod.snd List.filter_sublist)
    (List.nodup_zipIdx_map_snd xs)

/-- The actual finite set of vertices assigned this colour. -/
def colourClass (net : Network) (colours : List Nat) (c : Nat) : Finset Nat :=
  (Finset.range (SemiprimeD1TensorNetwork.vertices net).length).filter
    (fun v => colours.getD v 0 = c)

/-- Distinct colours give disjoint vertex sets, even when a class is empty. -/
theorem colourClass_disjoint (net : Network) (colours : List Nat) (c d : Nat) (h : c ≠ d) :
    Disjoint (colourClass net colours c) (colourClass net colours d) := by
  apply Finset.disjoint_left.mpr
  intro v hc hd
  exact h ((Finset.mem_filter.mp hc).2.symm.trans (Finset.mem_filter.mp hd).2)

/-- Exact selected-vertex product, indexed by original positions rather than values.
Thus repeated scalar tables and isolated vertices keep their multiplicities. -/
theorem classVertices_product {R : Type} [CommMonoid R]
    (net : Network) (colours : List Nat) (c : Nat) (f : Vertex → R) :
    ((classVertices (SemiprimeD1TensorNetwork.vertices net) colours c).map f).prod =
      ∏ i ∈ colourClass net colours c,
        if hi : i < (SemiprimeD1TensorNetwork.vertices net).length
          then f ((SemiprimeD1TensorNetwork.vertices net)[i]) else 1 := by
  classical
  let vs := SemiprimeD1TensorNetwork.vertices net
  let pairs := vs.zipIdx.filter (fun x => colours.getD x.2 0 == c)
  have hnd : pairs.Nodup := by
    exact (List.Nodup.of_map Prod.snd (List.nodup_zipIdx_map_snd vs)).filter _
  simp only [classVertices, List.map_map]
  change (pairs.map (fun x => f x.1)).prod = _
  rw [←List.prod_toFinset _ hnd]
  apply Finset.prod_bij (fun x _ => x.2)
  · intro x hx
    have hm := List.mem_filter.mp (List.mem_toFinset.mp hx)
    have hg := List.mem_zipIdx' hm.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.1, beq_iff_eq.mp hm.2⟩
  · intro x hx y hy he
    have hxm := (List.mem_filter.mp (List.mem_toFinset.mp hx)).1
    have hym := (List.mem_filter.mp (List.mem_toFinset.mp hy)).1
    apply Prod.ext
    · have hxx := (List.mem_zipIdx' hxm).2
      have hyy := (List.mem_zipIdx' hym).2
      rw [hxx, hyy]
      congr 1
    · exact he
  · intro i hi
    have hv := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hc := (Finset.mem_filter.mp hi).2
    refine ⟨(vs[i], i), List.mem_toFinset.mpr ?_, rfl⟩
    exact List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr
      (List.getElem?_eq_getElem hv), beq_iff_eq.mpr hc⟩
  · intro x hx
    have hg := List.mem_zipIdx' (List.mem_filter.mp (List.mem_toFinset.mp hx)).1
    change f x.1 = if hi : x.2 < vs.length then f vs[x.2] else 1
    simp only [dite_eq_left hg.1, hg.2]

/-- Both endpoints lie in the complete original vertex range. -/
theorem endpoints_lt (net : Network) (e : Fin (SemiprimeD1TensorNetwork.edgeCount net)) :
    (networkGraph net).left e < (SemiprimeD1TensorNetwork.vertices net).length ∧
      (networkGraph net).right e < (SemiprimeD1TensorNetwork.vertices net).length := by
  have hl := (SemiprimeD1TensorNetwork.owner net.rows (occurrence net e)).isLt
  have hr := (occurrence net e).1.isLt
  simp only [networkGraph, vertices_length]
  constructor <;> omega

/-- Literal class incident addresses equal the mathematical incident-edge set. -/
theorem classPorts_incident (net : Network) (colours : List Nat) (c : Nat)
    (e : Fin (SemiprimeD1TensorNetwork.edgeCount net)) :
    e.val ∈ (classPorts (SemiprimeD1BoundaryPlan.graph net) colours c).1 ↔
      e ∈ SemiprimeD1BoundarySemantics.incident (networkGraph net) (colourClass net colours c) := by
  change e.val ∈ selectedIndices (SemiprimeD1BoundaryPlan.graph net).edges
    (fun x => colours.getD x.1.1 0 == c || colours.getD x.1.2 0 == c) ↔ _
  rw [selectedIndices_mem _ _ e.val (by
    simpa only [SemiprimeD1BoundaryPlan.graph_edges_length] using e.isLt)]
  have hi : e.val < (SemiprimeD1BoundaryPlan.graph net).edges.length := by
    simpa only [SemiprimeD1BoundaryPlan.graph_edges_length] using e.isLt
  have he : (SemiprimeD1BoundaryPlan.graph net).edges[e.val]'hi =
      ((networkGraph net).left e, (networkGraph net).right e) := networkEndpoints_get net e
  rw [he]
  have hb := endpoints_lt net e
  simp [SemiprimeD1BoundarySemantics.incident, colourClass, hb.1, hb.2]

/-- Literal class boundary addresses equal precisely the exclusive endpoint set. -/
theorem classPorts_boundary (net : Network) (colours : List Nat) (c : Nat)
    (e : Fin (SemiprimeD1TensorNetwork.edgeCount net)) :
    e.val ∈ (classPorts (SemiprimeD1BoundaryPlan.graph net) colours c).2 ↔
      e ∈ SemiprimeD1BoundarySemantics.boundary (networkGraph net) (colourClass net colours c) := by
  change e.val ∈ selectedIndices (SemiprimeD1BoundaryPlan.graph net).edges
    (fun x => (colours.getD x.1.1 0 == c) != (colours.getD x.1.2 0 == c)) ↔ _
  rw [selectedIndices_mem _ _ e.val (by
    simpa only [SemiprimeD1BoundaryPlan.graph_edges_length] using e.isLt)]
  have hi : e.val < (SemiprimeD1BoundaryPlan.graph net).edges.length := by
    simpa only [SemiprimeD1BoundaryPlan.graph_edges_length] using e.isLt
  have he : (SemiprimeD1BoundaryPlan.graph net).edges[e.val]'hi =
      ((networkGraph net).left e, (networkGraph net).right e) := networkEndpoints_get net e
  rw [he]
  have hb := endpoints_lt net e
  simp only [SemiprimeD1BoundarySemantics.boundary, SemiprimeD1BoundarySemantics.incident,
    SemiprimeD1BoundarySemantics.internal, colourClass, Finset.mem_sdiff,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range, hb.1, hb.2,
    bne_iff_ne]
  change (¬ (colours.getD ((networkGraph net).left e) 0 == c) =
      (colours.getD ((networkGraph net).right e) 0 == c)) ↔ _
  rw [not_congr Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  tauto

/-- Both executed class address lists contain each selected occurrence only once. -/
theorem classPorts_nodup (g : SemiprimeD1BoundaryPlan.Graph) (colours : List Nat) (c : Nat) :
    (classPorts g colours c).1.Nodup ∧ (classPorts g colours c).2.Nodup :=
  ⟨selectedIndices_nodup _ _, selectedIndices_nodup _ _⟩

/-- Both actual class lists contain only valid global occurrence ordinals. -/
theorem classPorts_lt (g : SemiprimeD1BoundaryPlan.Graph) (colours : List Nat) (c p : Nat) :
    (p ∈ (classPorts g colours c).1 → p < g.edges.length) ∧
      (p ∈ (classPorts g colours c).2 → p < g.edges.length) :=
  ⟨selectedIndices_lt _ _ p, selectedIndices_lt _ _ p⟩

/-- A selected literal vertex retains its original ordinal and acquired colour. -/
theorem classVertices_index (vs : List Vertex) (colours : List Nat) (c : Nat)
    (v : Vertex) (hv : v ∈ classVertices vs colours c) :
    ∃ i, ∃ hi : i < vs.length, vs[i] = v ∧ colours.getD i 0 = c := by
  obtain ⟨x, hx, he⟩ := List.mem_map.mp hv
  obtain ⟨hm, hc⟩ := List.mem_filter.mp hx
  have hg := List.mem_zipIdx' hm
  exact ⟨x.2, hg.1, hg.2.symm.trans he, beq_iff_eq.mp hc⟩

/-- Well-formed local port caches have no repeated original ordinal. -/
theorem vertex_ports_nodup (net : Network) (hw : SemiprimeD1TensorNetwork.WellFormed net)
    (v : Vertex) (hv : v ∈ SemiprimeD1TensorNetwork.vertices net) : v.ports.Nodup := by
  rcases List.mem_append.mp hv with hl | hr
  · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hl
    rw [Vector.getElem_toList] at he
    subst v
    rw [hw.1 ⟨i, by simpa only [Vector.length_toList] using hi⟩]
    exact SemiprimeD1TensorNetwork.leftPorts_nodup _ _
  · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hr
    rw [Vector.getElem_toList] at he
    subst v
    rw [hw.2 ⟨i, by simpa only [Vector.length_toList] using hi⟩]
    exact SemiprimeD1TensorNetwork.rightPorts_nodup _ _

/-- Every selected local table address is among that class's acquired incident edges. -/
theorem class_vertex_ports_subset (net : Network) (hw : SemiprimeD1TensorNetwork.WellFormed net)
    (colours : List Nat) (c : Nat) (v : Vertex)
    (hv : v ∈ classVertices (SemiprimeD1TensorNetwork.vertices net) colours c) :
    ∀ p ∈ v.ports, p ∈ (classPorts (SemiprimeD1BoundaryPlan.graph net) colours c).1 := by
  obtain ⟨i, hi, he, hc⟩ := classVertices_index _ colours c v hv
  intro p hp
  have hmem : v ∈ SemiprimeD1TensorNetwork.vertices net := he ▸ List.getElem_mem hi
  have hbound := SemiprimeD1TensorNetwork.wellFormed_vertices net hw v hmem p hp
  let e : Fin (SemiprimeD1TensorNetwork.edgeCount net) := ⟨p, hbound⟩
  have hp' : e.val ∈ ((SemiprimeD1TensorNetwork.vertices net)[i]).ports := he.symm ▸ hp
  have hend := (edge_mem_vertex_ports net hw i hi e).mp hp'
  apply (classPorts_incident net colours c e).mpr
  simp only [SemiprimeD1BoundarySemantics.incident, colourClass, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_range]
  rcases hend with hl | hr
  · exact Or.inl ⟨hl ▸ hi, hl ▸ hc⟩
  · exact Or.inr ⟨hr ▸ hi, hr ▸ hc⟩

/-- Every stored selected local arity is bounded by the actual incident dimension. -/
theorem class_vertex_arity (net : Network) (hw : SemiprimeD1TensorNetwork.WellFormed net)
    (colours : List Nat) (c : Nat) (v : Vertex)
    (hv : v ∈ classVertices (SemiprimeD1TensorNetwork.vertices net) colours c) :
    v.ports.length ≤ (classPorts (SemiprimeD1BoundaryPlan.graph net) colours c).1.length := by
  obtain ⟨i, hi, he, _⟩ := classVertices_index _ colours c v hv
  have hn := vertex_ports_nodup net hw v (he ▸ List.getElem_mem hi)
  exact hn.length_le_of_subset (class_vertex_ports_subset net hw colours c v hv)

/-- Every colour class together is exactly the original complete vertex set. -/
theorem colourClass_cover (net : Network) (colours : List Nat) (k : Nat)
    (hc : ∀ v, v < (SemiprimeD1TensorNetwork.vertices net).length → colours.getD v 0 < k) :
    (Finset.range k).biUnion (colourClass net colours) = fullVertices net := by
  ext v
  simp only [Finset.mem_biUnion, colourClass, fullVertices, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨c, _, hv, _⟩
    exact hv
  · intro hv
    exact ⟨colours.getD v 0, hc v hv, hv, rfl⟩

/-- The partition actually acquired at runtime covers the complete original family. -/
theorem acquired_cover (net : Network) :
    (Finset.range (SemiprimeD1BoundaryPlan.acquire
      (SemiprimeD1BoundaryPlan.graph net)).k).biUnion
      (colourClass net (SemiprimeD1BoundaryPlan.acquire
        (SemiprimeD1BoundaryPlan.graph net)).colours) = fullVertices net := by
  apply colourClass_cover
  intro v hv
  have hl := SemiprimeD1BoundaryChoice.acquire_length (SemiprimeD1BoundaryPlan.graph net)
  have hvi : v < (SemiprimeD1BoundaryPlan.acquire
      (SemiprimeD1BoundaryPlan.graph net)).colours.length := by
    rw [hl]
    exact hv
  apply SemiprimeD1BoundaryChoice.acquire_colours
  rw [List.getD_eq_getElem _ _ hvi]
  exact List.getElem_mem hvi

/-- Selecting all original vertices leaves no boundary variable. -/
theorem boundary_full (net : Network) :
    SemiprimeD1BoundarySemantics.boundary (networkGraph net) (fullVertices net) = ∅ := by
  ext e
  have hb := endpoints_lt net e
  simp [SemiprimeD1BoundarySemantics.boundary, SemiprimeD1BoundarySemantics.incident,
    SemiprimeD1BoundarySemantics.internal, fullVertices, hb.1, hb.2]

noncomputable section

/-- The selected original table product is exactly the graph's local vertex product. -/
theorem classVertices_value (ctx : SemiprimeD1JetAxes.Context) (net : Network)
    (colours : List Nat) (c : Nat) (bits : Fin (SemiprimeD1TensorNetwork.edgeCount net) → Bool) :
    ((classVertices (SemiprimeD1TensorNetwork.vertices net) colours c).map (fun v =>
      SemiprimeD1JetInterpretation.interpret ctx (SemiprimeD1TensorTables.valueAt v.table
        (SemiprimeD1LeafCounter.localAssignment bits v)))).prod =
    SemiprimeD1BoundarySemantics.product (vertexValue ctx net) (colourClass net colours c)
      (SemiprimeD1BoundarySemantics.bitsEquiv.symm bits) := by
  rw [classVertices_product]
  simp only [SemiprimeD1BoundarySemantics.product, vertexValue, Equiv.apply_symm_apply]

end

/-- The actual sorted union contains exactly the two input port sets. -/
theorem unionPorts_mem (xs ys : List Nat) (p : Nat) :
    p ∈ unionPorts xs ys ↔ p ∈ xs ∨ p ∈ ys := by
  simp [unionPorts]

/-- The actual new boundary is exactly the exclusive union of the old lists. -/
theorem remainingPorts_mem (xs ys : List Nat) (p : Nat) :
    p ∈ remainingPorts xs ys ↔ (p ∈ xs ∧ p ∉ ys) ∨ (p ∈ ys ∧ p ∉ xs) := by
  by_cases hx : p ∈ xs <;> by_cases hy : p ∈ ys <;>
    simp [remainingPorts, unionPorts_mem, hx, hy]

/-- Sorted union does not duplicate a variable shared by two old boundaries. -/
theorem eraseDups_nodup (xs : List Nat) : xs.eraseDups.Nodup := by
  induction hn : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      constructor
      · intro hm
        have hh := List.mem_filter.mp (List.mem_eraseDups.mp hm)
        simpa using hh.2
      · apply ih ((xs.filter (fun b => !(b == x))).length)
          (by have := List.length_filter_le (fun b => !(b == x)) xs
              simp only [List.length_cons] at hn
              omega) _ rfl

/-- Sorted union does not duplicate a variable shared by two old boundaries. -/
theorem unionPorts_nodup (xs ys : List Nat) : (unionPorts xs ys).Nodup :=
  eraseDups_nodup _

/-- The executed symmetric difference has no duplicate ordinal. -/
theorem remainingPorts_nodup (xs ys : List Nat) : (remainingPorts xs ys).Nodup :=
  (unionPorts_nodup xs ys).filter _

end RiemannGaussian.SemiprimeD1BoundaryLeafPorts
