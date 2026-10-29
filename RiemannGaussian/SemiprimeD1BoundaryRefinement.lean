import RiemannGaussian.SemiprimeD1BoundaryIdentity
import RiemannGaussian.SemiprimeD1LeafCounterBounds

/-! # Ordered original-network and canonical-word boundary refinement

The endpoint stream is exactly the actual factor-major occurrence stream.
These theorems connect concrete boundary records to the old whole-jet leaf;
they do not supply entries, partitions, sorting results or runtime clocks.
-/
set_option autoImplicit false

namespace RiemannGaussian.SemiprimeD1BoundaryRefinement
open scoped BigOperators
open SemiprimeD1TensorNetwork
open SemiprimeD1JetAxes (Context)
open SemiprimeD1JetInterpretation (Carrier interpret)
open SemiprimeD1TensorTables (GoodWords)
open SemiprimeD1BoundarySemantics

/-- Original endpoints, in exact occurrence order, retaining parallel occurrences. -/
def networkEndpoints (net : Network) : List (ℕ × ℕ) :=
  (incidences net.rows).map (fun i => ((owner net.rows i).val, net.leftCount + i.1.val))

/-- Each original variable produces exactly one endpoint pair. -/
theorem networkEndpoints_length (net : Network) :
    (networkEndpoints net).length = edgeCount net := by
  simp [networkEndpoints, edgeCount, scope]

/-- Read the actual occurrence at an original variable ordinal. -/
def occurrence (net : Network) (e : Fin (edgeCount net)) : Incidence net.rows :=
  (incidences net.rows)[e.val]

/-- Actual occurrence lookup and its computed ordinal are mutually consistent. -/
theorem edgeID_occurrence (net : Network) (e : Fin (edgeCount net)) :
    edgeID net.rows (occurrence net e) = e.val :=
  (incidences_nodup net.rows).idxOf_getElem e.val e.isLt

/-- The proof graph reads exactly the two original endpoint bytes by ordinal. -/
def networkGraph (net : Network) : SemiprimeD1BoundarySemantics.Graph ℕ (Fin (edgeCount net)) where
  left e := (owner net.rows (occurrence net e)).val
  right e := net.leftCount + (occurrence net e).1.val
  distinct e := by
    have h := (owner net.rows (occurrence net e)).isLt
    omega

/-- The graph's endpoint pair is exactly the corresponding acquired stream item. -/
theorem networkEndpoints_get (net : Network) (e : Fin (edgeCount net)) :
    (networkEndpoints net)[e.val]'(by simpa only [networkEndpoints_length] using e.isLt) =
      ((networkGraph net).left e, (networkGraph net).right e) := by
  simp [networkEndpoints, networkGraph, occurrence]

/-- All actual vertices, including zero-port owner and factor vertices. -/
def fullVertices (net : Network) : Finset ℕ := Finset.range (vertices net).length

/-- Literal stored vertex count; no isolated vertex is removed. -/
theorem vertices_length (net : Network) :
    (vertices net).length = net.leftCount + net.rows.length := by
  simp [vertices]

/-- The physical ordered-port caches realize exactly the two original endpoints. -/
theorem edge_mem_vertex_ports (net : Network) (hw : WellFormed net)
    (v : ℕ) (hv : v < (vertices net).length) (e : Fin (edgeCount net)) :
    e.val ∈ ((vertices net)[v]).ports ↔
      (networkGraph net).left e = v ∨ (networkGraph net).right e = v := by
  by_cases hl : v < net.leftCount
  · have ha : (vertices net)[v] = net.left[v] := by
      simp only [vertices, List.getElem_append, Vector.length_toList, dite_eq_left hl, Vector.getElem_toList]
    rw [ha, hw.1 ⟨v, hl⟩, ← edgeID_occurrence net e, edgeID_mem_leftPorts]
    constructor
    · intro he
      exact Or.inl (congrArg Fin.val he)
    · intro he
      rcases he with he | he
      · exact Fin.ext he
      · simp only [networkGraph] at he
        omega
  · have hr : v - net.leftCount < net.rows.length := by rw [vertices_length] at hv; omega
    have ha : (vertices net)[v] = net.right[v - net.leftCount] := by
      simp only [vertices, List.getElem_append, Vector.length_toList, dite_eq_right hl, Vector.getElem_toList]
    rw [ha, hw.2 ⟨v - net.leftCount, hr⟩, ← edgeID_occurrence net e, edgeID_mem_rightPorts]
    constructor
    · intro he
      have hh := congrArg Fin.val he
      change (occurrence net e).1.val = v - net.leftCount at hh
      right
      simp only [networkGraph]
      omega
    · intro he
      rcases he with he | he
      · have hh := (owner net.rows (occurrence net e)).isLt
        simp only [networkGraph] at he
        omega
      · apply Fin.ext
        change (occurrence net e).1.val = v - net.leftCount
        simp only [networkGraph] at he
        omega

noncomputable section

/-- Original vertex value in its ACTUAL cached local port order. -/
def vertexValue (ctx : Context) (net : Network) (v : ℕ)
    (x : Finset (Fin (edgeCount net))) : Carrier ctx :=
  if hv : v < (vertices net).length then
    let vertex := (vertices net)[v]
    interpret ctx (SemiprimeD1TensorTables.valueAt vertex.table
      (SemiprimeD1LeafCounter.localAssignment (bitsEquiv x) vertex))
  else 1

/-- The original cached entry depends only on its actual incident variables. -/
theorem vertexValue_local (ctx : Context) (net : Network) (hw : WellFormed net) :
    Local (networkGraph net) (vertexValue ctx net) := by
  intro v x y hxy
  by_cases hv : v < (vertices net).length
  · simp only [vertexValue, dite_eq_left hv]
    congr 2
    funext j
    let vertex := (vertices net)[v]
    have hmem : vertex.ports[j.val] ∈ vertex.ports := List.getElem_mem j.isLt
    have hport : vertex.ports[j.val] < edgeCount net :=
      wellFormed_vertices net hw vertex (List.getElem_mem hv) _ hmem
    let e : Fin (edgeCount net) := ⟨vertex.ports[j.val], hport⟩
    have he := (edge_mem_vertex_ports net hw v hv e).mp hmem
    have hh := hxy e he
    have hb : (bitsEquiv x) e = (bitsEquiv y) e := by
      change decide (e ∈ x) = decide (e ∈ y)
      simp only [hh]
    simpa [SemiprimeD1LeafCounter.localAssignment, List.getElem?_ofFn, hport, e, vertex] using hb
  · simp only [vertexValue, dite_eq_right hv]

/-- Exact boundary entry for an actual ordered-port network and global completion. -/
def boundaryValue (ctx : Context) (net : Network) (s : Finset ℕ)
    (bits : Fin (edgeCount net) → Bool) : Carrier ctx :=
  value (networkGraph net) (vertexValue ctx net) s (bitsEquiv.symm bits)

/-- Selecting every vertex internalizes every original variable exactly once. -/
theorem internal_full (net : Network) :
    internal (networkGraph net) (fullVertices net) = Finset.univ := by
  ext e
  have hl := (owner net.rows (occurrence net e)).isLt
  have hr := (occurrence net e).1.isLt
  simp only [internal, fullVertices, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_range, vertices_length, networkGraph]
  constructor
  · intro _
    trivial
  · intro _
    constructor
    · omega
    · omega

/-- The finite vertex product is exactly the old list product, with no reordering of ports. -/
theorem full_product (ctx : Context) (net : Network) (x : Finset (Fin (edgeCount net))) :
    product (vertexValue ctx net) (fullVertices net) x =
      ((vertices net).map (fun v => interpret ctx (SemiprimeD1TensorTables.valueAt v.table
        (SemiprimeD1LeafCounter.localAssignment (bitsEquiv x) v)))).prod := by
  unfold product fullVertices
  rw [← Fin.prod_univ_eq_prod_range, ← List.prod_ofFn]
  congr 1
  apply List.ext_getElem (by simp)
  intro i hi hj
  have hv : i < (vertices net).length := by simpa only [List.length_ofFn] using hi
  simp only [List.getElem_ofFn, List.getElem_map, vertexValue, dite_eq_left hv]

/-- A complete boundary contraction is exactly the original whole-jet leaf value. -/
theorem full_value (ctx : Context) (net : Network) (hp : ctx.Positive)
    (bits : Fin (edgeCount net) → Bool) :
    boundaryValue ctx net (fullVertices net) bits = interpret ctx (leaf ctx net).words := by
  unfold boundaryValue value
  rw [internal_full]
  have hz : bitsEquiv.symm bits \ (Finset.univ : Finset (Fin (edgeCount net))) = ∅ :=
    Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ _)
  simp only [patch, hz, Finset.empty_union]
  rw [sum_boolean]
  simp_rw [full_product, Equiv.apply_symm_apply]
  exact (leaf_value ctx hp net).symm

/-- Intrinsic canonicality upgrades the complete boundary identity to exact old bytes.
The words here are the concrete leaf output, never an input entry supplier. -/
theorem words_eq_leaf_of_boundary (ctx : Context) (net : Network) (hp : ctx.Positive)
    (words : List (List Bool)) (hw : GoodWords ctx words)
    (he : interpret ctx words = boundaryValue ctx net (fullVertices net) (fun _ => false)) :
    words = (leaf ctx net).words := by
  have ht : GoodWords ctx (leaf ctx net).words :=
    SemiprimeD1LeafCounterBounds.run_good (edgeCount net) ctx (vertices net)
  exact SemiprimeD1JetInterpretation.interpret_injective ctx words _ hp hw.1 ht.1
    (fun w h => (hw.2 w h).1) (fun w h => (ht.2 w h).1)
    (fun w h => (hw.2 w h).2) (fun w h => (ht.2 w h).2)
    (he.trans (full_value ctx net hp _))

end
end RiemannGaussian.SemiprimeD1BoundaryRefinement
