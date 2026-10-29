import RiemannGaussian.SemiprimeD1BoundaryCatalogue
import RiemannGaussian.SemiprimeD1BoundaryLeafPorts
import RiemannGaussian.SemiprimeD1BoundaryFiber

/-! The executed incident catalogue computes the original class boundary value. -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryBucketValue
open scoped BigOperators
open SemiprimeD1BoundaryRecords
open SemiprimeD1BoundaryLeaf
open SemiprimeD1BoundaryLeafPorts
open SemiprimeD1BoundaryCatalogue
open SemiprimeD1BoundaryRefinement
open SemiprimeD1BoundarySemantics
open SemiprimeD1JetAxes (Context)
open SemiprimeD1JetInterpretation (interpret)

theorem lookup_lift (m : Nat) (v : Vertex) (z : Finset Nat)
    (h : ∀ p ∈ v.ports, p < m) :
    (SemiprimeD1TensorTables.lookup v.table
      (v.ports.map (fun p => decide (p ∈ z)))).words =
      SemiprimeD1TensorTables.valueAt v.table
        (SemiprimeD1LeafCounter.localAssignment (bitsEquiv (lift m z)) v) := by
  rw [SemiprimeD1TensorTables.lookup_value _ _ (by simp)]
  congr 1
  funext j
  have hp := h v.ports[j.val] (List.getElem_mem j.isLt)
  simp only [List.getElem_map,SemiprimeD1LeafCounter.localAssignment,
    List.getElem?_ofFn, dite_eq_left hp, Option.getD_some]
  change decide (v.ports[j.val] ∈ z) = decide ((⟨v.ports[j.val],hp⟩ : Fin m) ∈ lift m z)
  simp only [mem_lift]

theorem boundary_subset_incident (net : Network) (colours : List Nat) (c : Nat) :
    ∀ p ∈ (classPorts (SemiprimeD1BoundaryPlan.graph net) colours c).2,
      p ∈ (classPorts (SemiprimeD1BoundaryPlan.graph net) colours c).1 := by
  intro p hp
  have hb := (classPorts_lt (SemiprimeD1BoundaryPlan.graph net) colours c p).2 hp
  rw [SemiprimeD1BoundaryPlan.graph_edges_length] at hb
  let e : Fin (SemiprimeD1TensorNetwork.edgeCount net) := ⟨p,hb⟩
  exact (classPorts_incident net colours c e).mpr
    (Finset.mem_sdiff.mp ((classPorts_boundary net colours c e).mp hp)).1

theorem lift_incident (net : Network) (colours : List Nat) (c : Nat) :
    lift (SemiprimeD1TensorNetwork.edgeCount net)
      (classPorts (SemiprimeD1BoundaryPlan.graph net) colours c).1.toFinset =
      incident (networkGraph net) (colourClass net colours c) := by
  ext e
  simpa only [mem_lift,List.mem_toFinset] using classPorts_incident net colours c e

theorem lift_boundary (net : Network) (colours : List Nat) (c : Nat) :
    lift (SemiprimeD1TensorNetwork.edgeCount net)
      (classPorts (SemiprimeD1BoundaryPlan.graph net) colours c).2.toFinset =
      boundary (networkGraph net) (colourClass net colours c) := by
  ext e
  simpa only [mem_lift,List.mem_toFinset] using classPorts_boundary net colours c e

theorem projected_product (ctx : Context) (net : Network)
    (hw : SemiprimeD1TensorNetwork.WellFormed net) (colours : List Nat) (c : Nat)
    (bits : List Bool)
    (hl : bits.length = (classPorts (SemiprimeD1BoundaryPlan.graph net) colours c).1.length) :
    ((classVertices (SemiprimeD1TensorNetwork.vertices net) colours c).map (fun v =>
      interpret ctx (SemiprimeD1TensorTables.lookup v.table
        (project bits (classPorts (SemiprimeD1BoundaryPlan.graph net) colours c).1 v.ports).value).words)).prod =
      product (vertexValue ctx net) (colourClass net colours c)
        (lift (SemiprimeD1TensorNetwork.edgeCount net)
          (selected (classPorts (SemiprimeD1BoundaryPlan.graph net) colours c).1 bits)) := by
  have hnd := (classPorts_nodup (SemiprimeD1BoundaryPlan.graph net) colours c).1
  have hp : ((classVertices (SemiprimeD1TensorNetwork.vertices net) colours c).map (fun v =>
      interpret ctx (SemiprimeD1TensorTables.lookup v.table
        (project bits (classPorts (SemiprimeD1BoundaryPlan.graph net) colours c).1 v.ports).value).words)) =
    (classVertices (SemiprimeD1TensorNetwork.vertices net) colours c).map (fun v =>
      interpret ctx (SemiprimeD1TensorTables.valueAt v.table
        (SemiprimeD1LeafCounter.localAssignment
          (bitsEquiv (lift (SemiprimeD1TensorNetwork.edgeCount net)
            (selected (classPorts (SemiprimeD1BoundaryPlan.graph net) colours c).1 bits))) v))) := by
    apply List.map_congr_left
    intro v hv
    rw [project_selected _ _ hnd bits hl (class_vertex_ports_subset net hw colours c v hv)]
    rw [lookup_lift]
    obtain ⟨i,hi,he,_⟩ := classVertices_index _ colours c v hv
    exact SemiprimeD1TensorNetwork.wellFormed_vertices net hw v (he ▸ List.getElem_mem hi)
  rw [hp,classVertices_value]
  simp only [Equiv.symm_apply_apply]

theorem bucket_natural_sum (ctx : Context) (hp : ctx.Positive) (net : Network)
    (hw : SemiprimeD1TensorNetwork.WellFormed net) (colours : List Nat) (c : Nat)
    (x : Finset Nat) :
    SemiprimeD1BoundaryRecordsReduction.weighted ctx
      (bucket ctx (SemiprimeD1BoundaryPlan.graph net) (SemiprimeD1TensorNetwork.vertices net)
        colours c).value.entries
      ((classPorts (SemiprimeD1BoundaryPlan.graph net) colours c).2.map (fun p => decide (p ∈ x))) =
    ∑ z ∈ (classPorts (SemiprimeD1BoundaryPlan.graph net) colours c).1.toFinset.powerset,
      if z ∩ (classPorts (SemiprimeD1BoundaryPlan.graph net) colours c).2.toFinset =
        x ∩ (classPorts (SemiprimeD1BoundaryPlan.graph net) colours c).2.toFinset then
        product (vertexValue ctx net) (colourClass net colours c)
          (lift (SemiprimeD1TensorNetwork.edgeCount net) z) else 0 := by
  rw [SemiprimeD1BoundaryLeafCorrectness.bucket_weighted ctx hp]
  simp only [seed,List.map_map,Function.comp_def,
    SemiprimeD1JetAffineCoefficient.interpret_one ctx hp,one_mul]
  rw [←assignments_selected_sum _ (classPorts_nodup _ colours c).1]
  congr 1
  apply List.map_congr_left
  intro bits hb
  have hl := (SemiprimeD1BoundaryAddresses.assignments_mem _ bits).mp hb
  rw [project_selected _ _ (classPorts_nodup _ colours c).1 bits hl
    (boundary_subset_incident net colours c)]
  simp only [address_eq_iff]
  rw [projected_product ctx net hw colours c bits hl]

/-- The literal bucket is the original network boundary contraction at every
retained address. No canonical-entry supplier or assumed tensor is an operand. -/
theorem bucket_value (ctx : Context) (hp : ctx.Positive) (net : Network)
    (hw : SemiprimeD1TensorNetwork.WellFormed net) (colours : List Nat) (c : Nat)
    (x : Finset (Fin (SemiprimeD1TensorNetwork.edgeCount net))) :
    SemiprimeD1BoundaryRecordsReduction.weighted ctx
      (bucket ctx (SemiprimeD1BoundaryPlan.graph net) (SemiprimeD1TensorNetwork.vertices net)
        colours c).value.entries
      ((classPorts (SemiprimeD1BoundaryPlan.graph net) colours c).2.map
        (fun p => decide (p ∈ x.image Fin.val))) =
      value (networkGraph net) (vertexValue ctx net) (colourClass net colours c) x := by
  classical
  rw [bucket_natural_sum ctx hp net hw colours c]
  let m := SemiprimeD1TensorNetwork.edgeCount net
  let source := (classPorts (SemiprimeD1BoundaryPlan.graph net) colours c).1
  let target := (classPorts (SemiprimeD1BoundaryPlan.graph net) colours c).2
  have hsource : ∀ p ∈ source.toFinset, p < m := by
    intro p hp
    simpa only [SemiprimeD1BoundaryPlan.graph_edges_length] using
      (classPorts_lt (SemiprimeD1BoundaryPlan.graph net) colours c p).1 (List.mem_toFinset.mp hp)
  have htarget : ∀ p ∈ target.toFinset, p < m := by
    intro p hp
    simpa only [SemiprimeD1BoundaryPlan.graph_edges_length] using
      (classPorts_lt (SemiprimeD1BoundaryPlan.graph net) colours c p).2 (List.mem_toFinset.mp hp)
  have hcond (z : Finset Nat) :
      (z ∩ target.toFinset = x.image Fin.val ∩ target.toFinset) ↔
      (lift m z ∩ boundary (networkGraph net) (colourClass net colours c) =
        x ∩ boundary (networkGraph net) (colourClass net colours c)) := by
    rw [←lift_boundary net colours c]
    change (z ∩ target.toFinset = x.image Fin.val ∩ target.toFinset) ↔
      (lift m z ∩ lift m target.toFinset = x ∩ lift m target.toFinset)
    have hh := (lift_eq_iff m (z ∩ target.toFinset) (x.image Fin.val ∩ target.toFinset)
      (fun p hp => htarget p (Finset.mem_inter.mp hp).2)
      (fun p hp => htarget p (Finset.mem_inter.mp hp).2)).symm
    rw [lift_inter,lift_inter,lift_image m x] at hh
    exact hh
  have he : (∑ z ∈ source.toFinset.powerset,
      if z ∩ target.toFinset = x.image Fin.val ∩ target.toFinset then
        product (vertexValue ctx net) (colourClass net colours c) (lift m z) else 0) =
    ∑ z ∈ source.toFinset.powerset,
      if lift m z ∩ boundary (networkGraph net) (colourClass net colours c) =
        x ∩ boundary (networkGraph net) (colourClass net colours c) then
        product (vertexValue ctx net) (colourClass net colours c) (lift m z) else 0 := by
    apply Finset.sum_congr rfl
    intro z _
    simp only [hcond z]
  rw [he]
  rw [sum_lift_powerset m source.toFinset hsource (fun z =>
    if z ∩ boundary (networkGraph net) (colourClass net colours c) =
      x ∩ boundary (networkGraph net) (colourClass net colours c) then
      product (vertexValue ctx net) (colourClass net colours c) z else 0)]
  rw [lift_incident]
  exact SemiprimeD1BoundaryFiber.incident_fiber _ _ (vertexValue_local ctx net hw) _ _

end RiemannGaussian.SemiprimeD1BoundaryBucketValue
