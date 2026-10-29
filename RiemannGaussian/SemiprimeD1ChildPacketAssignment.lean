/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1NestedPositions
import RiemannGaussian.SemiprimeD1ChildOldEntryAssignment

/-! # Exact packet endpoint bits under the canonical child assignment
Nested-list shape transport preserves the actual factor/local-index stream.
The canonical right-port gather consequently reads the COMMON original
endpoint assignment at every actual packet endpoint, not an advised bit list.
-/
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1ChildPacketAssignment
open SemiprimeD1TensorNetwork
open SemiprimeD1ChildGraph (Graph Endpoint)
open SemiprimeD1ChildOldEntrySemantics
open SemiprimeD1ChildOldEntryAssignment

/-- Actual row arities are the endpoint-bucket lengths, with only the factor-index cast. -/
theorem shape_length {V : ℕ} (graph : Graph V)
    (e : Fin (SemiprimeD1TensorNetworkLayout.childRows graph).length) :
    arity (SemiprimeD1TensorNetworkLayout.childRows graph) e=
      (graph.factors[((finCongr (SemiprimeD1TensorNetworkLayout.childRows_length graph)) e).val]).length := by
  simp only [arity,SemiprimeD1TensorNetworkLayout.childRows,List.getElem_map,List.length_map]
  rfl

/-- Identity-index shape bijection, derived from the literal endpoint rows. -/
def endpointShape {V : ℕ} (graph : Graph V) :
    Incidence (SemiprimeD1TensorNetworkLayout.childRows graph) ≃
      SemiprimeD1NestedPositions.Position graph.factors :=
  SemiprimeD1NestedPositions.shapeEquiv
    (arity (SemiprimeD1TensorNetworkLayout.childRows graph)) (fun e => (graph.factors[e.val]).length)
    (SemiprimeD1TensorNetworkLayout.childRows_length graph) (shape_length graph)

/-- Actual physical endpoint at a typed canonical child occurrence. -/
def endpointAt {V : ℕ} (graph : Graph V)
    (i : Incidence (SemiprimeD1TensorNetworkLayout.childRows graph)) : Endpoint V :=
  SemiprimeD1NestedPositions.read graph.factors (endpointShape graph i)

/-- Endpoint reads preserve the full factor-major stream in EXACT order. -/
theorem endpoint_stream {V : ℕ} (graph : Graph V) :
    (incidences (SemiprimeD1TensorNetworkLayout.childRows graph)).map (endpointAt graph)=
      graph.factors.flatten := by
  have heq : endpointAt graph=(SemiprimeD1NestedPositions.read graph.factors) ∘
      (SemiprimeD1NestedPositions.shapeEquiv
        (arity (SemiprimeD1TensorNetworkLayout.childRows graph)) (fun e => (graph.factors[e.val]).length)
        (SemiprimeD1TensorNetworkLayout.childRows_length graph) (shape_length graph)) := rfl
  rw [heq]
  have h:=SemiprimeD1NestedPositions.enumeration_shape
    (arity (SemiprimeD1TensorNetworkLayout.childRows graph)) (fun e => (graph.factors[e.val]).length)
    (SemiprimeD1TensorNetworkLayout.childRows_length graph) (shape_length graph)
  calc
    _=(SemiprimeFiniteEnumerations.indexedIncidences graph.factors.length
        (fun e => (graph.factors[e.val]).length)).values.map
          (SemiprimeD1NestedPositions.read graph.factors) := by
      simpa only [incidences,List.map_map,Function.comp_def] using
        congrArg (List.map (SemiprimeD1NestedPositions.read graph.factors)) h
    _=graph.factors.flatten:=SemiprimeD1NestedPositions.enumeration_read graph.factors

/-- The actual occurrence ID points to its exact flattened physical endpoint. -/
theorem endpoint_position {V : ℕ} (graph : Graph V)
    (i : Incidence (SemiprimeD1TensorNetworkLayout.childRows graph)) :
    endpointAt graph i=graph.factors.flatten[edgeID (SemiprimeD1TensorNetworkLayout.childRows graph) i]'(by
      rw [← SemiprimeD1TensorNetworkLayout.child_scope];exact edgeID_lt _ i) := by
  have h:=congrArg (fun xs : List (Endpoint V) =>
    xs[edgeID (SemiprimeD1TensorNetworkLayout.childRows graph) i]?) (endpoint_stream graph)
  simp only [List.getElem?_map,edgeID,List.getElem?_idxOf (incidence_mem _ i),Option.map_some] at h
  have hi : edgeID (SemiprimeD1TensorNetworkLayout.childRows graph) i<graph.factors.flatten.length := by
    rw [← SemiprimeD1TensorNetworkLayout.child_scope];exact edgeID_lt _ i
  change some (endpointAt graph i)=graph.factors.flatten[edgeID (SemiprimeD1TensorNetworkLayout.childRows graph) i]? at h
  rw [List.getElem?_eq_getElem hi] at h
  exact Option.some.inj h

/-- The common original endpoint assignment agrees at each canonical typed occurrence. -/
theorem endpoint_bit (net : Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (bits : Incidence net.rows×Bool→Bool) (i : Incidence (rows net r a q g)) :
    SemiprimeD1ChildAssignmentEndpoint.originalEndpointBit net.leftCount net.rows.length r a
      (arity net.rows) (owner net.rows) bits (endpointAt (data net r a q g).graph i)=
        bits (tagAt net r a q g i) := by
  rw [endpoint_position]
  have hi : edgeID (rows net r a q g) i<
      SemiprimeD1ChildAssignmentEquiv.scope net.leftCount net.rows.length r a
        (arity net.rows) (owner net.rows) q g := by
    change edgeID (rows net r a q g) i<(data net r a q g).graph.factors.flatten.length
    rw [← SemiprimeD1TensorNetworkLayout.child_scope];exact edgeID_lt _ i
  have h:=SemiprimeD1ChildAssignmentEndpoint.originalEndpointBit_assignment net.leftCount net.rows.length r a
    (arity net.rows) (owner net.rows) q g bits ⟨edgeID (rows net r a q g) i,hi⟩
  simpa only [SemiprimeD1ChildAssignmentEquiv.assignments_value,
    SemiprimeD1ChildAssignmentEquiv.childEquiv_value,tagAt] using h

private theorem map_cast_reads {A : Type} (xs : List A) (K : ℕ) (h : K=xs.length) :
    (List.finRange K).map (fun j => xs[j.val]'(by rw [← h];exact j.isLt))=xs := by
  subst K
  exact SemiprimeD1ParentTagOrder.map_fin_reads xs

/-- Reading all local canonical occurrences gives the literal endpoint bucket in order. -/
theorem endpoint_row {V : ℕ} (graph : Graph V)
    (e : Fin (SemiprimeD1TensorNetworkLayout.childRows graph).length) :
    (List.finRange (arity (SemiprimeD1TensorNetworkLayout.childRows graph) e)).map
      (fun j => endpointAt graph ⟨e,j⟩)=
      graph.factors[((finCongr (SemiprimeD1TensorNetworkLayout.childRows_length graph)) e).val] := by
  exact map_cast_reads _ _ (shape_length graph e)

/-- The ACTUAL canonical right-port gather is the COMMON original endpoint assignment
on the actual bucket, with no packet-bit or local-gather premise. -/
theorem gather_right (net : Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (bits : Incidence net.rows×Bool→Bool) (e : Fin (rows net r a q g).length) :
    (SemiprimeD1LeafCounter.gather (List.ofFn (networkAssignment net r a q g bits))
      (rightPorts (rows net r a q g) e)).bits=
    ((data net r a q g).graph.factors[((finCongr
      (SemiprimeD1TensorNetworkLayout.childRows_length (data net r a q g).graph)) e).val]).map
      (SemiprimeD1ChildAssignmentEndpoint.originalEndpointBit net.leftCount net.rows.length r a
        (arity net.rows) (owner net.rows) bits) := by
  rw [SemiprimeD1LeafCounter.gather_value,SemiprimeD1RootNetworkOrder.rightPorts_order,List.map_map]
  have h (j : Fin (arity (rows net r a q g) e)) :
      ((List.ofFn (networkAssignment net r a q g bits))[edgeID (rows net r a q g) ⟨e,j⟩]?).getD false=
      SemiprimeD1ChildAssignmentEndpoint.originalEndpointBit net.leftCount net.rows.length r a
        (arity net.rows) (owner net.rows) bits (endpointAt (data net r a q g).graph ⟨e,j⟩) := by
    have hi : edgeID (rows net r a q g) ⟨e,j⟩<
        (List.ofFn (networkAssignment net r a q g bits)).length := by
      rw [List.length_ofFn];exact edgeID_lt _ _
    rw [List.getElem?_eq_getElem hi,List.getElem_ofFn,networkAssignment_edge,endpoint_bit]
    rfl
  simp_rw [Function.comp_def,h]
  simpa only [List.map_map,Function.comp_def] using
    congrArg (List.map (SemiprimeD1ChildAssignmentEndpoint.originalEndpointBit net.leftCount net.rows.length r a
      (arity net.rows) (owner net.rows) bits)) (endpoint_row (data net r a q g).graph e)
end RiemannGaussian.SemiprimeD1ChildPacketAssignment
