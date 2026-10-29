/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildNetworkIntegrand
import RiemannGaussian.SemiprimeD1ParentOriginalAssignment
import RiemannGaussian.SemiprimeD1ChildFreshLiftValue

/-! # All actual child integrands preserve the individual original parent entries
Every old entry occurs in its actual selected group exactly once. The same
literal entry bytes, interpreted at child precision, then enter a legitimate
fresh-axis embedding. No aggregate parent residue is lifted.
-/
set_option autoImplicit false
set_option maxHeartbeats 180000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1OriginalChildProduct
open scoped BigOperators
open SemiprimeD1TensorNetwork SemiprimeD1JetAxes SemiprimeD1JetInterpretation
open SemiprimeD1ChildNetworkIntegrand SemiprimeD1ChildPacketEntrySemantics
open SemiprimeD1ChildOldEntrySemantics SemiprimeD1ChildOldEntryAssignment
open SemiprimeD1ParentOriginalAssignment SemiprimeD1OriginalDoubleAssignments
noncomputable section

/-- Canonicality at every literal table leaf applies to every finite local
assignment, not an advised reached-value invariant. -/
theorem valueAt_good (ctx : Context) {n : ℕ} (table : SemiprimeD1TensorTables.Table n)
    (ht : SemiprimeD1TensorTables.Good ctx table) (bits : Fin n → Bool) :
    SemiprimeD1TensorTables.GoodWords ctx (SemiprimeD1TensorTables.valueAt table bits) := by
  induction table with
  | leaf words => exact ht
  | fork low high ihlow ihhigh =>
    dsimp only [SemiprimeD1TensorTables.valueAt]
    split
    · exact ihhigh ht.2 _
    · exact ihlow ht.1 _

/-- Literal left-parent cache indexing preserves its original vector entry. -/
theorem parentVertex_left (net : Network) (v : Fin net.leftCount) :
    SemiprimeD1ChildNetwork.parentVertex net (Fin.castAdd net.rows.length v) = net.left[v.val] := by
  change (net.left.toList++net.right.toList)[v.val]'(by
    simp only [List.length_append,Vector.length_toList]
    omega) = net.left[v.val]
  rw [List.getElem_append_left (by simpa only [Vector.length_toList] using v.isLt),Vector.getElem_toList]

/-- Literal right-parent cache indexing preserves the distinct right namespace. -/
theorem parentVertex_right (net : Network) (e : Fin net.rows.length) :
    SemiprimeD1ChildNetwork.parentVertex net (Fin.natAdd net.leftCount e) = net.right[e.val] := by
  change (net.left.toList++net.right.toList)[net.leftCount+e.val]'(by
    simp only [List.length_append,Vector.length_toList]
    omega) = net.right[e.val]
  rw [List.getElem_append_right (by simp only [Vector.length_toList];omega)]
  simp only [Vector.length_toList,Nat.add_sub_cancel_left,Vector.getElem_toList]

/-- Across ALL actual groups the actual executed child integrands have one
copy of every original parent entry and every acquired packet/group entry. -/
theorem all_child_integrands (net : Network) (hw : WellFormed net) (old : Context)
    (extra : List ℕ) (p r a u : ℕ) [NeZero r] (i : Fin a)
    (z : SemiprimeD1JetRingBits.Run) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (beta : List ℕ) (bits : Incidence net.rows × Bool → Bool)
    (hpos : (⟨extra++old.axes,p⟩ : Context).Positive) :
    (∏ g : Fin r,interpret ⟨extra++old.axes,p⟩
      (SemiprimeD1LeafCounter.evaluateAssignment ⟨extra++old.axes,p⟩
        (vertices (child net old extra p r a u i g z t beta))
        (List.ofFn (networkAssignment net r a i g bits))).words) =
      (∏ v : Fin (net.leftCount+net.rows.length),interpret ⟨extra++old.axes,p⟩
        (SemiprimeD1ChildTableCopy.lift old extra p
          (SemiprimeD1TensorTables.valueAt (SemiprimeD1ChildNetwork.parentVertex net v).table
            (parentBits net hw bits v))).words) *
      ∏ f : Fin (original net r a).state.packets.length,∏ g : Fin r,
        packetTerm net r a u old.precision i g ⟨extra++old.axes,p⟩ z t beta bits f := by
  simp_rw [evaluate_child net hw old extra p r a u i _ z t beta bits hpos]
  rw [Finset.prod_mul_distrib]
  apply congrArg₂ (·*·)
  · rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro v _
    exact Fintype.prod_ite_eq (vertexColour net r a i v) (fun _ => _)
  · exact Finset.prod_comm

/-- The old factors of the complete child product are the original X/Y
factors from the deformation theorem, with individual-entry carries intact. -/
theorem original_parent_product (net : Network) (hw : WellFormed net) (old : Context)
    (hg : Good old net) (q p r a : ℕ) (hq : 0 < q)
    (x y : Bits net.leftCount net.rows.length r a (arity net.rows) (owner net.rows)) :
    (∏ v : Fin (net.leftCount+net.rows.length),interpret ⟨q::old.axes,p⟩
      (SemiprimeD1ChildTableCopy.lift old [q] p
        (SemiprimeD1TensorTables.valueAt (SemiprimeD1ChildNetwork.parentVertex net v).table
          (parentBits net hw (SemiprimeD1PacketAssignmentRows.tagBits net.leftCount net.rows.length r a
            (arity net.rows) (owner net.rows) x y) v))).words) =
      SemiprimeD1JetBlockPolynomial.actualEmbedding old q p
        ((net.right.toList.map (fun v => interpret ⟨old.axes,p⟩
          (SemiprimeD1TensorTables.valueAt v.table (SemiprimeD1LeafCounter.localAssignment x v)))).prod) *
      SemiprimeD1JetBlockPolynomial.actualEmbedding old q p
        ((net.left.toList.map (fun v => interpret ⟨old.axes,p⟩
          (SemiprimeD1TensorTables.valueAt v.table (SemiprimeD1LeafCounter.localAssignment y v)))).prod) := by
  let f : Carrier ⟨old.axes,p⟩ →+* Carrier ⟨q::old.axes,p⟩ :=
    SemiprimeD1JetBlockPolynomial.actualEmbedding old q p
  have he (v : Fin (net.leftCount+net.rows.length)) :
      interpret ⟨q::old.axes,p⟩
        (SemiprimeD1ChildTableCopy.lift old [q] p
          (SemiprimeD1TensorTables.valueAt (SemiprimeD1ChildNetwork.parentVertex net v).table
            (parentBits net hw (SemiprimeD1PacketAssignmentRows.tagBits net.leftCount net.rows.length r a
              (arity net.rows) (owner net.rows) x y) v))).words =
        f (interpret ⟨old.axes,p⟩ (SemiprimeD1TensorTables.valueAt
          (SemiprimeD1ChildNetwork.parentVertex net v).table
          (SemiprimeD1LeafCounter.localAssignment (if v.val < net.leftCount then y else x)
            (SemiprimeD1ChildNetwork.parentVertex net v)))) := by
    rw [parentBits_original]
    exact SemiprimeD1ChildFreshLiftValue.lift_fresh_value old q p _ hq
      (valueAt_good old _ (SemiprimeD1ChildNetwork.parentVertex_good old net hg v) _).1
  simp_rw [he]
  change _ = f _ * f _
  rw [Fin.prod_univ_add]
  have hl :
      (∏ v : Fin net.leftCount,f (interpret ⟨old.axes,p⟩
        (SemiprimeD1TensorTables.valueAt (SemiprimeD1ChildNetwork.parentVertex net (Fin.castAdd net.rows.length v)).table
          (SemiprimeD1LeafCounter.localAssignment
            (if (Fin.castAdd net.rows.length v).val < net.leftCount then y else x)
            (SemiprimeD1ChildNetwork.parentVertex net (Fin.castAdd net.rows.length v)))))) =
      f ((net.left.toList.map (fun v => interpret ⟨old.axes,p⟩
        (SemiprimeD1TensorTables.valueAt v.table (SemiprimeD1LeafCounter.localAssignment y v)))).prod) := by
    rw [map_list_prod,List.map_map,vector_product]
    apply Finset.prod_congr rfl
    intro v _
    simp only [Fin.val_castAdd,v.isLt,ite_true,Function.comp_def]
    exact congrArg (fun vertex : SemiprimeD1LeafCounter.Vertex =>
      f (interpret ⟨old.axes,p⟩ (SemiprimeD1TensorTables.valueAt vertex.table
        (SemiprimeD1LeafCounter.localAssignment y vertex)))) (parentVertex_left net v)
  have hr :
      (∏ e : Fin net.rows.length,f (interpret ⟨old.axes,p⟩
        (SemiprimeD1TensorTables.valueAt (SemiprimeD1ChildNetwork.parentVertex net (Fin.natAdd net.leftCount e)).table
          (SemiprimeD1LeafCounter.localAssignment
            (if (Fin.natAdd net.leftCount e).val < net.leftCount then y else x)
            (SemiprimeD1ChildNetwork.parentVertex net (Fin.natAdd net.leftCount e)))))) =
      f ((net.right.toList.map (fun v => interpret ⟨old.axes,p⟩
        (SemiprimeD1TensorTables.valueAt v.table (SemiprimeD1LeafCounter.localAssignment x v)))).prod) := by
    rw [map_list_prod,List.map_map,vector_product]
    apply Finset.prod_congr rfl
    intro e _
    simp only [Fin.val_natAdd,show ¬net.leftCount+e.val < net.leftCount by omega,
      ite_false,Function.comp_def]
    exact congrArg (fun vertex : SemiprimeD1LeafCounter.Vertex =>
      f (interpret ⟨old.axes,p⟩ (SemiprimeD1TensorTables.valueAt vertex.table
        (SemiprimeD1LeafCounter.localAssignment x vertex)))) (parentVertex_right net e)
  rw [hl,hr,mul_comm]

end
end RiemannGaussian.SemiprimeD1OriginalChildProduct
