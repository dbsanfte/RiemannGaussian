/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ParentTagOrder

/-! # Actual old-vertex entries under the original two-sided assignment
The physical endpoint-position theorem identifies selected child tag order
with the actual canonical child ports. Activation and length conditions are
derived from actual acquisitions, including empty and isolated vertices.
-/
set_option autoImplicit false
set_option maxHeartbeats 160000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1ChildOldEntrySemantics
open scoped BigOperators
open SemiprimeD1TensorNetwork
open SemiprimeD1ChildPortBijection (linkVertex)
open SemiprimeD1JetAxes (Context)

/-- Actual original-input pullback for the literal current network. -/
abbrev data (net : Network) (r a : ℕ) (q : Fin a) (g : Fin r) :=
  SemiprimeD1ChildPortPullback.acquire net.leftCount net.rows.length r a
    (arity net.rows) (owner net.rows) q g

/-- Actual acquired per-old-vertex tag ordering. -/
abbrev order (net : Network) (r a : ℕ) (q : Fin a) (g : Fin r)
    (v : Fin (net.leftCount+net.rows.length)) :=
  SemiprimeD1ChildTableOrder.acquire (owner net.rows) (data net r a q g) v

/-- Same-position physical resolution preserves the whole vertex stream in exact order. -/
theorem tags_vertices (net : Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r) :
    (SemiprimeD1ChildAssignmentEquiv.tags net.leftCount net.rows.length r a
      (arity net.rows) (owner net.rows) q g).map (linkVertex (owner net.rows))=
      (data net r a q g).graph.factors.flatten.map SemiprimeD1ChildGraph.Endpoint.vertex := by
  apply List.ext_getElem
  · simp only [List.length_map]
    exact SemiprimeD1ChildAssignmentEquiv.tags_length _ _ _ _ _ _ _ _
  · intro j hj ht
    simp only [List.getElem_map]
    have hscope : j<SemiprimeD1ChildAssignmentEquiv.scope net.leftCount net.rows.length r a
        (arity net.rows) (owner net.rows) q g := by
      change j<(data net r a q g).graph.factors.flatten.length
      simpa only [List.length_map] using ht
    have h:=SemiprimeD1ChildAssignmentEndpoint.childEquiv_endpoint net.leftCount net.rows.length r a
      (arity net.rows) (owner net.rows) q g ⟨j,hscope⟩
    rw [SemiprimeD1ChildAssignmentEquiv.childEquiv_value] at h
    exact h.1

/-- Canonical child port length equals the ACTUALLY acquired local tag length for every vertex. -/
theorem child_length (net : Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (v : Fin (net.leftCount+net.rows.length)) :
    (leftPorts (SemiprimeD1TensorNetworkLayout.childRows (data net r a q g).graph) v).length=
      (order net r a q g v).child.length := by
  rw [SemiprimeD1ParentTagOrder.leftPorts_length]
  change (((data net r a q g).graph.factors.map
    (List.map SemiprimeD1ChildGraph.Endpoint.vertex)).flatten.filter (fun u => decide (u=v))).length=_
  rw [← List.map_flatten,← tags_vertices net r a q g]
  simp only [List.filter_map,List.length_map,Function.comp_def]
  rfl

/-- Gathering by actual index searches recovers every requested source value. -/
theorem gather_indices {A : Type} [BEq A] [LawfulBEq A] (xs ys : List A) (f : A→Bool)
    (hmem : ∀x∈xs,x∈ys) :
    (SemiprimeD1ChildTableCopy.gather (ys.map f) (xs.map ys.idxOf)).value=xs.map f := by
  rw [SemiprimeD1ChildTableCopy.gather_value]
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro x hx
  rw [List.getElem?_map,List.getElem?_idxOf (hmem x hx)]
  rfl

/-- Actual local Boolean vector under one original two-sided assignment. -/
def localBits (net : Network) (r a : ℕ) (q : Fin a) (g : Fin r)
    (bits : Incidence net.rows×Bool→Bool) (v : Fin (net.leftCount+net.rows.length)) : List Bool :=
  (order net r a q g v).child.map bits

/-- No local child-size advice is needed for the actual original assignment vector. -/
theorem localBits_length (net : Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (bits : Incidence net.rows×Bool→Bool) (v : Fin (net.leftCount+net.rows.length)) :
    (localBits net r a q g bits v).length=
      (leftPorts (SemiprimeD1TensorNetworkLayout.childRows (data net r a q g).graph) v).length := by
  rw [localBits,List.length_map,child_length]

/-- Original-tag bits have exactly the literal well-formed parent table degree. -/
theorem parentBits_length (net : Network) (hw : WellFormed net)
    (bits : Incidence net.rows×Bool→Bool) (v : Fin (net.leftCount+net.rows.length)) :
    ((SemiprimeD1ParentTagOrder.oldTags net.rows v).map bits).length=
      (SemiprimeD1ChildNetwork.parentVertex net v).ports.length := by
  have h:=congrArg List.length (SemiprimeD1ParentTagOrder.oldTags_parent net hw v)
  simpa only [List.length_map] using h

/-- Correctly typed parent local assignment, in the exact literal parent port order. -/
def parentBits (net : Network) (hw : WellFormed net)
    (bits : Incidence net.rows×Bool→Bool) (v : Fin (net.leftCount+net.rows.length)) :
    Fin (SemiprimeD1ChildNetwork.parentVertex net v).ports.length→Bool :=
  fun j => ((SemiprimeD1ParentTagOrder.oldTags net.rows v).map bits)[j.val]'(by
    rw [parentBits_length net hw bits v];exact j.isLt)

/-- At an active vertex, the actual computed gather recovers all original parent bits. -/
theorem gathered_parent (net : Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (bits : Incidence net.rows×Bool→Bool) (v : Fin (net.leftCount+net.rows.length))
    (ha : ((data net r a q g).activation.bits[v.val]?).getD false=true) :
    (SemiprimeD1ChildTableCopy.gather (localBits net r a q g bits v)
      (order net r a q g v).order).value=
      (SemiprimeD1ParentTagOrder.oldTags net.rows v).map bits := by
  change (SemiprimeD1ChildTableCopy.gather
    ((order net r a q g v).child.map bits)
    ((order net r a q g v).old.map (order net r a q g v).child.idxOf)).value=_
  rw [gather_indices]
  · rw [SemiprimeD1ParentTagOrder.acquired_old]
  · intro tag ht
    exact SemiprimeD1ChildTableOrder.old_mem_child net.leftCount net.rows.length r a
      (arity net.rows) (owner net.rows) q g v ha tag ht
/-- Actual zero-port unit coefficients, not a supplied neutral-entry answer. -/
def unitWords (ctx : Context) : List (List Bool) :=
  (SemiprimeD1TensorTables.lookup (SemiprimeD1ChildTensorTables.unit ctx).table []).words

/-- All activation and size guards are discharged by the actual acquisitions. -/
theorem leftOne_value (net : Network) (hw : WellFormed net) (r a : ℕ) [NeZero r]
    (q : Fin a) (g : Fin r) (old : Context) (extra : List ℕ) (p : ℕ)
    (bits : Incidence net.rows×Bool→Bool) (v : Fin (net.leftCount+net.rows.length)) :
    (SemiprimeD1TensorTables.lookup
      (SemiprimeD1ChildNetwork.leftOne net (data net r a q g) old extra p v).1.table
      (localBits net r a q g bits v)).words=
    if ((data net r a q g).activation.bits[v.val]?).getD false then
      (SemiprimeD1ChildTableCopy.lift old extra p
        (SemiprimeD1TensorTables.valueAt (SemiprimeD1ChildNetwork.parentVertex net v).table
          (parentBits net hw bits v))).words
    else unitWords ⟨extra++old.axes,p⟩ := by
  have hb:=localBits_length net r a q g bits v
  by_cases ha : ((data net r a q g).activation.bits[v.val]?).getD false=true
  · rw [ite_eq_left ha]
    rw [SemiprimeD1ChildNetwork.leftOne_active_value net (data net r a q g) old extra p v
      (localBits net r a q g bits v) hb ha (List.length_map _)]
    rw [gathered_parent net r a q g bits v ha]
    rw [SemiprimeD1TensorTables.lookup_value _ _ (parentBits_length net hw bits v)]
    rfl
  · rw [ite_eq_right ha]
    have hf : ((data net r a q g).activation.bits[v.val]?).getD false=false := Bool.eq_false_iff.mpr ha
    dsimp only [SemiprimeD1ChildNetwork.leftOne]
    rw [SemiprimeD1ChildNetwork.copyTable_value _ _ _ hb]
    dsimp only [SemiprimeD1ChildTensorTables.fromCache]
    rw [hf]
    rfl

/-- The actual selected class of every old vertex, including isolated vertices. -/
def vertexColour (net : Network) (r a : ℕ) [NeZero r] (q : Fin a)
    (v : Fin (net.leftCount+net.rows.length)) : Fin r :=
  SemiprimeMaterializedScoreEnvironment.denote
    (SemiprimeSourceHistogramHeadOriginal.originalEnv r a
      (SemiprimeD1IncidenceSearch.run net.leftCount net.rows.length r a
        (arity net.rows) (owner net.rows)).value) v.val q

/-- The physical activation bit is exactly the original selected vertex class. -/
theorem active_iff (net : Network) (r a : ℕ) [NeZero r] (q : Fin a) (g : Fin r)
    (v : Fin (net.leftCount+net.rows.length)) :
    ((data net r a q g).activation.bits[v.val]?).getD false=true ↔ vertexColour net r a q v=g :=
  SemiprimeD1ChildActivationOriginal.mask_value net.leftCount net.rows.length r a
    (arity net.rows) (owner net.rows) q g v

/-- Actual old entries occur in their unique selected group, and every other group emits the literal unit. -/
theorem leftOne_value_group (net : Network) (hw : WellFormed net) (r a : ℕ) [NeZero r]
    (q : Fin a) (g : Fin r) (old : Context) (extra : List ℕ) (p : ℕ)
    (bits : Incidence net.rows×Bool→Bool) (v : Fin (net.leftCount+net.rows.length)) :
    (SemiprimeD1TensorTables.lookup
      (SemiprimeD1ChildNetwork.leftOne net (data net r a q g) old extra p v).1.table
      (localBits net r a q g bits v)).words=
    if vertexColour net r a q v=g then
      (SemiprimeD1ChildTableCopy.lift old extra p
        (SemiprimeD1TensorTables.valueAt (SemiprimeD1ChildNetwork.parentVertex net v).table
          (parentBits net hw bits v))).words
    else unitWords ⟨extra++old.axes,p⟩ := by
  rw [leftOne_value net hw r a q g old extra p bits v]
  by_cases h : vertexColour net r a q v=g
  · have ha:=(active_iff net r a q g v).mpr h
    simp [ha,h]
  · have ha : ¬((data net r a q g).activation.bits[v.val]?).getD false=true :=
      fun ha => h ((active_iff net r a q g v).mp ha)
    simp [ha,h]
/-- The actual unit table allocates precisely the dense scalar-one coefficient vector. -/
theorem unitWords_scalar (ctx : Context) (hpos : ∀q∈ctx.axes,0<q) :
    unitWords ctx=(SemiprimeD1JetPolynomialBits.scalar ctx
      (SemiprimeD1JetScalarBits.reduce ctx.precision [true]).bits).words := by
  have hn : 0<ctx.rank:=List.prod_pos hpos
  obtain ⟨k,hk⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp [unitWords,SemiprimeD1ChildTensorTables.unit,SemiprimeD1TensorTables.lookup,
    SemiprimeD1JetAxes.copyVector_value,SemiprimeD1JetPolynomialBits.scalar,
    SemiprimeSourceCompactBits.copy_bits,hk,List.range_succ_eq_map,Function.comp_def]

/-- The actual off-group table is one in the concrete nilpotent quotient. -/
theorem unitWords_interpret (ctx : Context) (hpos : ∀q∈ctx.axes,0<q) :
    SemiprimeD1JetInterpretation.interpret ctx (unitWords ctx)=1 := by
  rw [unitWords_scalar ctx hpos,SemiprimeD1JetPolynomialBits.scalar_value ctx _ hpos]
  have h : (SemiprimeBitArithmetic.bitValue
      (SemiprimeD1JetScalarBits.reduce ctx.precision [true]).bits:ZMod (2^ctx.precision))=1 := by
    simp [SemiprimeD1JetScalarBits.reduce_value,ZMod.natCast_mod,SemiprimeBitArithmetic.bitValue,SemiprimeBitArithmetic.bitNat]
  rw [h,map_one]

/-- Every original vertex contributes its literal lifted scalar exactly once over all groups,
including isolated vertices; all other groups contribute one. -/
theorem product_groups (net : Network) (hw : WellFormed net) (r a : ℕ) [NeZero r]
    (q : Fin a) (old : Context) (extra : List ℕ) (p : ℕ)
    (bits : Incidence net.rows×Bool→Bool) (v : Fin (net.leftCount+net.rows.length))
    (hpos : ∀k∈extra++old.axes,0<k) :
    (∏g : Fin r,SemiprimeD1JetInterpretation.interpret ⟨extra++old.axes,p⟩
      (SemiprimeD1TensorTables.lookup
        (SemiprimeD1ChildNetwork.leftOne net (data net r a q g) old extra p v).1.table
        (localBits net r a q g bits v)).words)=
    SemiprimeD1JetInterpretation.interpret ⟨extra++old.axes,p⟩
      (SemiprimeD1ChildTableCopy.lift old extra p
        (SemiprimeD1TensorTables.valueAt (SemiprimeD1ChildNetwork.parentVertex net v).table
          (parentBits net hw bits v))).words := by
  classical
  have heq (g : Fin r) :
      SemiprimeD1JetInterpretation.interpret ⟨extra++old.axes,p⟩
        (SemiprimeD1TensorTables.lookup
          (SemiprimeD1ChildNetwork.leftOne net (data net r a q g) old extra p v).1.table
          (localBits net r a q g bits v)).words=
      if vertexColour net r a q v=g then
        SemiprimeD1JetInterpretation.interpret ⟨extra++old.axes,p⟩
          (SemiprimeD1ChildTableCopy.lift old extra p
            (SemiprimeD1TensorTables.valueAt (SemiprimeD1ChildNetwork.parentVertex net v).table
              (parentBits net hw bits v))).words else 1 := by
    rw [leftOne_value_group net hw r a q g old extra p bits v]
    split_ifs <;> simp only [unitWords_interpret ⟨extra++old.axes,p⟩ hpos]
  simp_rw [heq]
  simp
end RiemannGaussian.SemiprimeD1ChildOldEntrySemantics
