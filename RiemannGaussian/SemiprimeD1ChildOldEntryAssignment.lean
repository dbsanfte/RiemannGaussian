/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildOldEntrySemantics

/-! # Actual canonical child assignments feed literal old-table entries
Computed occurrence IDs, actual physical resolved tags and canonical child
port gathers are identified in their exact list order. The old-entry formula
therefore applies to the global assignment bijection, not a local-bit oracle.
-/
set_option autoImplicit false
set_option maxHeartbeats 180000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1ChildOldEntryAssignment
open SemiprimeD1TensorNetwork
open SemiprimeD1ChildOldEntrySemantics
open SemiprimeD1ChildPortBijection (linkVertex)
open SemiprimeD1JetAxes (Context)
open scoped BigOperators

/-- Actual canonical child owner rows. -/
abbrev rows (net : Network) (r a : ℕ) (q : Fin a) (g : Fin r) :=
  SemiprimeD1TensorNetworkLayout.childRows (data net r a q g).graph

/-- Original-tag cache length equals the actual canonical child variable count. -/
theorem tags_scope (net : Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r) :
    (SemiprimeD1ChildAssignmentEquiv.tags net.leftCount net.rows.length r a
      (arity net.rows) (owner net.rows) q g).length=scope (rows net r a q g) := by
  rw [SemiprimeD1ChildAssignmentEquiv.tags_length]
  exact (SemiprimeD1TensorNetworkLayout.child_scope (data net r a q g).graph).symm

/-- Same-position original tag of an actual canonical child occurrence. -/
def tagAt (net : Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (i : Incidence (rows net r a q g)) : Incidence net.rows×Bool :=
  (SemiprimeD1ChildAssignmentEquiv.tags net.leftCount net.rows.length r a
    (arity net.rows) (owner net.rows) q g)[edgeID (rows net r a q g) i]'(by
      rw [tags_scope];exact edgeID_lt _ i)

/-- Reading the same-position tag at every canonical incidence recovers the whole cache in order. -/
theorem incidence_tags (net : Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r) :
    (incidences (rows net r a q g)).map (tagAt net r a q g)=
      SemiprimeD1ChildAssignmentEquiv.tags net.leftCount net.rows.length r a
        (arity net.rows) (owner net.rows) q g := by
  apply List.ext_getElem
  · rw [List.length_map,tags_scope]
    rfl
  · intro j hj ht
    simp only [List.getElem_map]
    have hi : j<(incidences (rows net r a q g)).length := by simpa only [List.length_map] using hj
    have hidx:=(incidences_nodup (rows net r a q g)).idxOf_getElem j hi
    simp only [tagAt,edgeID,hidx]

/-- Vertex preservation holds at every actual typed child occurrence. -/
theorem tagAt_vertex (net : Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (i : Incidence (rows net r a q g)) :
    linkVertex (owner net.rows) (tagAt net r a q g i)=owner (rows net r a q g) i := by
  have hm : (incidences (rows net r a q g)).map
      (fun i => linkVertex (owner net.rows) (tagAt net r a q g i))=
      (incidences (rows net r a q g)).map (owner (rows net r a q g)) := by
    calc
      _=(SemiprimeD1ChildAssignmentEquiv.tags net.leftCount net.rows.length r a
          (arity net.rows) (owner net.rows) q g).map (linkVertex (owner net.rows)) := by
        simpa only [List.map_map,Function.comp_def] using
          congrArg (List.map (linkVertex (owner net.rows))) (incidence_tags net r a q g)
      _=(data net r a q g).graph.factors.flatten.map SemiprimeD1ChildGraph.Endpoint.vertex :=
        tags_vertices net r a q g
      _=_ := by
        rw [SemiprimeD1ParentTagOrder.incidence_owners]
        exact List.map_flatten
  have h:=congrArg (fun xs : List (Fin (net.leftCount+net.rows.length)) =>
    xs[edgeID (rows net r a q g) i]?) hm
  simp only [List.getElem?_map,edgeID,List.getElem?_idxOf (incidence_mem _ i),Option.map_some] at h
  exact Option.some.inj h

/-- Selecting canonical child incidences at a vertex gives its ACTUAL local tag stream. -/
theorem filtered_tags (net : Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (v : Fin (net.leftCount+net.rows.length)) :
    ((incidences (rows net r a q g)).filter
      (fun i => decide (owner (rows net r a q g) i=v))).map (tagAt net r a q g)=
      (order net r a q g v).child := by
  change _=(SemiprimeD1ChildAssignmentEquiv.tags net.leftCount net.rows.length r a
    (arity net.rows) (owner net.rows) q g).filter (fun t => decide (linkVertex (owner net.rows) t=v))
  rw [← incidence_tags,List.filter_map]
  simp only [Function.comp_def,tagAt_vertex]

/-- Actual global assignment from the computed child bijection, transported to canonical scope. -/
def networkAssignment (net : Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (bits : Incidence net.rows×Bool→Bool) : Fin (scope (rows net r a q g))→Bool :=
  fun j => SemiprimeD1ChildAssignmentEquiv.assignments net.leftCount net.rows.length r a
    (arity net.rows) (owner net.rows) q bits g
    ⟨j.val,by
      change j.val<(data net r a q g).graph.factors.flatten.length
      rw [← SemiprimeD1TensorNetworkLayout.child_scope]
      exact j.isLt⟩

/-- The actual global assignment reads exactly the original tag at this occurrence position. -/
theorem networkAssignment_edge (net : Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (bits : Incidence net.rows×Bool→Bool) (i : Incidence (rows net r a q g)) :
    networkAssignment net r a q g bits ⟨edgeID (rows net r a q g) i,edgeID_lt _ i⟩=
      bits (tagAt net r a q g i) := by
  simp only [networkAssignment,SemiprimeD1ChildAssignmentEquiv.assignments_value,
    SemiprimeD1ChildAssignmentEquiv.childEquiv_value,tagAt]

/-- The actual canonical left-port gather equals the acquired local original-tag assignment. -/
theorem gather_assignment (net : Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (bits : Incidence net.rows×Bool→Bool) (v : Fin (net.leftCount+net.rows.length)) :
    (SemiprimeD1LeafCounter.gather (List.ofFn (networkAssignment net r a q g bits))
      (leftPorts (rows net r a q g) v)).bits=localBits net r a q g bits v := by
  rw [SemiprimeD1LeafCounter.gather_value]
  change (((incidences (rows net r a q g)).filter
    (fun i => decide (owner (rows net r a q g) i=v))).map (edgeID (rows net r a q g))).map _=_
  rw [List.map_map]
  have h (i : Incidence (rows net r a q g)) :
      ((List.ofFn (networkAssignment net r a q g bits))[edgeID (rows net r a q g) i]?).getD false=
      bits (tagAt net r a q g i) := by
    have hi : edgeID (rows net r a q g) i<(List.ofFn (networkAssignment net r a q g bits)).length := by
      rw [List.length_ofFn];exact edgeID_lt _ i
    rw [List.getElem?_eq_getElem hi,List.getElem_ofFn]
    exact networkAssignment_edge net r a q g bits i
  simp_rw [Function.comp_def,h]
  simpa only [localBits,List.map_map,Function.comp_def] using
    congrArg (List.map bits) (filtered_tags net r a q g v)

/-- Actual left-table evaluation under the GLOBAL child assignment has no local-bit oracle or guards. -/
theorem evaluate_left (net : Network) (hw : WellFormed net) (r a : ℕ) [NeZero r]
    (q : Fin a) (g : Fin r) (old : Context) (extra : List ℕ) (p : ℕ)
    (bits : Incidence net.rows×Bool→Bool) (v : Fin (net.leftCount+net.rows.length)) :
    (SemiprimeD1LeafCounter.evaluateVertex
      (SemiprimeD1ChildNetwork.leftOne net (data net r a q g) old extra p v).1
      (List.ofFn (networkAssignment net r a q g bits))).words=
    if vertexColour net r a q v=g then
      (SemiprimeD1ChildTableCopy.lift old extra p
        (SemiprimeD1TensorTables.valueAt (SemiprimeD1ChildNetwork.parentVertex net v).table
          (parentBits net hw bits v))).words
    else unitWords ⟨extra++old.axes,p⟩ := by
  have hg : (SemiprimeD1LeafCounter.gather (List.ofFn (networkAssignment net r a q g bits))
      (SemiprimeD1ChildNetwork.leftOne net (data net r a q g) old extra p v).1.ports).bits=
        localBits net r a q g bits v := by
    rw [SemiprimeD1ChildNetwork.leftOne_ports]
    exact gather_assignment net r a q g bits v
  dsimp only [SemiprimeD1LeafCounter.evaluateVertex]
  rw [hg]
  exact leftOne_value_group net hw r a q g old extra p bits v
/-- Actual cached left vector stores the computed old-vertex table exactly once. -/
theorem fromSource_left (net : Network) {r a : ℕ} (source : SemiprimeD1ChildNetwork.Source net a)
    (q : Fin a) (g : Fin r) (old : Context) (extra : List ℕ) (p : ℕ)
    (z : SemiprimeD1JetRingBits.Run) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (v : Fin (net.leftCount+net.rows.length)) :
    (SemiprimeD1ChildNetwork.fromSource net source q g old extra p z t beta).network.left[v.val]=
      (SemiprimeD1ChildNetwork.leftOne net
        (SemiprimeD1ChildPortPullback.fromReplay (owner net.rows) source.packets q g) old extra p v).1 := by
  simp only [SemiprimeD1ChildNetwork.fromSource,Vector.getElem_map,Vector.getElem_ofFn]

/-- Original-source cached output vertex is the one whose global-entry semantics was proved. -/
theorem acquire_left (net : Network) (old : Context) (extra : List ℕ) (p r a u phase : ℕ)
    (q : Fin a) (g : Fin r) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (v : Fin (net.leftCount+net.rows.length)) :
    (SemiprimeD1ChildNetwork.acquire net old extra p r a u phase q g z t beta).network.left[v.val]=
      (SemiprimeD1ChildNetwork.leftOne net (data net r a q g) old extra p v).1 := by
  exact fromSource_left net
    (SemiprimeD1OriginalModeAcquisition.acquire net.leftCount net.rows.length r a u phase
      old.precision (arity net.rows) (owner net.rows)) q g old extra p z t beta v

/-- The emitted concrete child Network, not a helper table or local-value oracle,
has the original parent entry under the actual global child assignment. -/
theorem evaluate_acquire_left (net : Network) (hw : WellFormed net) (old : Context)
    (extra : List ℕ) (p r a u phase : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (z : SemiprimeD1JetRingBits.Run) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (beta : List ℕ) (bits : Incidence net.rows×Bool→Bool)
    (v : Fin (net.leftCount+net.rows.length)) :
    (SemiprimeD1LeafCounter.evaluateVertex
      (SemiprimeD1ChildNetwork.acquire net old extra p r a u phase q g z t beta).network.left[v.val]
      (List.ofFn (networkAssignment net r a q g bits))).words=
    if vertexColour net r a q v=g then
      (SemiprimeD1ChildTableCopy.lift old extra p
        (SemiprimeD1TensorTables.valueAt (SemiprimeD1ChildNetwork.parentVertex net v).table
          (parentBits net hw bits v))).words
    else unitWords ⟨extra++old.axes,p⟩ := by
  rw [acquire_left]
  exact evaluate_left net hw r a q g old extra p bits v
/-- Across the ACTUAL emitted child caches, every parent scalar is preserved exactly once,
even at an isolated old vertex; off-group evaluator results are one. -/
theorem product_acquire_left (net : Network) (hw : WellFormed net) (old : Context)
    (extra : List ℕ) (p r a u phase : ℕ) [NeZero r] (q : Fin a)
    (z : SemiprimeD1JetRingBits.Run) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (beta : List ℕ) (bits : Incidence net.rows×Bool→Bool)
    (v : Fin (net.leftCount+net.rows.length)) (hpos : ∀k∈extra++old.axes,0<k) :
    (∏g : Fin r,SemiprimeD1JetInterpretation.interpret ⟨extra++old.axes,p⟩
      (SemiprimeD1LeafCounter.evaluateVertex
        (SemiprimeD1ChildNetwork.acquire net old extra p r a u phase q g z t beta).network.left[v.val]
        (List.ofFn (networkAssignment net r a q g bits))).words)=
    SemiprimeD1JetInterpretation.interpret ⟨extra++old.axes,p⟩
      (SemiprimeD1ChildTableCopy.lift old extra p
        (SemiprimeD1TensorTables.valueAt (SemiprimeD1ChildNetwork.parentVertex net v).table
          (parentBits net hw bits v))).words := by
  classical
  have he (g : Fin r) := (evaluate_acquire_left net hw old extra p r a u phase q g z t beta bits v).trans
    (leftOne_value_group net hw r a q g old extra p bits v).symm
  simp_rw [he]
  exact product_groups net hw r a q old extra p bits v hpos
end RiemannGaussian.SemiprimeD1ChildOldEntryAssignment
