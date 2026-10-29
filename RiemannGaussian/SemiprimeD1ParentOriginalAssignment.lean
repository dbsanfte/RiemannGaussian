/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildOldEntrySemantics
import RiemannGaussian.SemiprimeD1OriginalDoubleAssignments

/-! # The actual old-cache assignment is the original X or Y in literal port order
Both endpoint sides and every parallel incidence are preserved by the computed
original placement index. No local assignment or permutation is a premise.
-/
set_option autoImplicit false
set_option maxHeartbeats 180000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1ParentOriginalAssignment
open SemiprimeD1TensorNetwork SemiprimeD1ParentTagOrder
open SemiprimeD1ChildOldEntrySemantics SemiprimeD1PacketAssignmentRows
open SemiprimeD1OriginalDoubleAssignments SemiprimeD1OriginalIncidenceIndex
open SemiprimeD1ChildPortBijection (linkVertex)
noncomputable section

/-- Every tag at a literal old vertex has the endpoint side determined by
that vertex's original left/right namespace. -/
theorem oldTags_side (net : Network) (v : Fin (net.leftCount+net.rows.length))
    (tag : Incidence net.rows × Bool) (ht : tag ∈ oldTags net.rows v) :
    tag.2 = decide (v.val < net.leftCount) := by
  have hv : linkVertex (owner net.rows) tag = v :=
    of_decide_eq_true (List.mem_filter.mp ht).2
  have hval := congrArg Fin.val hv
  rcases tag with ⟨port,side⟩
  cases side with
  | false =>
    change net.leftCount+port.1.val = v.val at hval
    simp only [show ¬ v.val < net.leftCount by omega,decide_false]
  | true =>
    change (owner net.rows port).val = v.val at hval
    have hp := (owner net.rows port).isLt
    simp only [show v.val < net.leftCount by omega,decide_true]

/-- A canonical cached port read is exactly its acquired original position
read, with the actual position constructor providing the bound. -/
theorem read_position (net : Network) (r a : ℕ)
    (bits : Bits net.leftCount net.rows.length r a (arity net.rows) (owner net.rows))
    (port : Incidence net.rows) :
    ((List.ofFn bits)[edgeID net.rows port]?).getD false =
      bits (position net.leftCount net.rows.length r a (arity net.rows) (owner net.rows) port) := by
  have he := position_network_val net.rows r a port
  rw [← he]
  rw [List.getElem?_eq_getElem (by
    rw [List.length_ofFn]
    exact (position net.leftCount net.rows.length r a (arity net.rows) (owner net.rows) port).isLt)]
  simp only [List.getElem_ofFn,Option.getD_some]

/-- The actual old table callback receives precisely Y on left vertices and
X on right vertices, in the ORIGINAL cached table's exact local port order. -/
theorem parentBits_original (net : Network) (hw : WellFormed net) (r a : ℕ)
    (x y : Bits net.leftCount net.rows.length r a (arity net.rows) (owner net.rows))
    (v : Fin (net.leftCount+net.rows.length)) :
    parentBits net hw
      (tagBits net.leftCount net.rows.length r a (arity net.rows) (owner net.rows) x y) v =
      SemiprimeD1LeafCounter.localAssignment (if v.val < net.leftCount then y else x)
        (SemiprimeD1ChildNetwork.parentVertex net v) := by
  funext k
  have hmap := oldTags_parent net hw v
  have hlen := congrArg List.length hmap
  simp only [List.length_map] at hlen
  have hk : k.val < (oldTags net.rows v).length := by omega
  let tag := (oldTags net.rows v)[k.val]'hk
  have ht : tag ∈ oldTags net.rows v := List.getElem_mem hk
  have hside := oldTags_side net v tag ht
  have hp := congrArg (fun xs : List ℕ => xs[k.val]?) hmap
  simp only [List.getElem?_map,List.getElem?_eq_getElem hk,
    List.getElem?_eq_getElem k.isLt,Option.map_some,Option.some.injEq] at hp
  dsimp only [parentBits,SemiprimeD1LeafCounter.localAssignment]
  simp only [List.getElem_map]
  change (tagBits net.leftCount net.rows.length r a (arity net.rows) (owner net.rows) x y tag) =
    ((List.ofFn (if v.val < net.leftCount then y else x))[
      (SemiprimeD1ChildNetwork.parentVertex net v).ports[k.val]]?).getD false
  rw [← hp]
  change _ = ((List.ofFn (if v.val < net.leftCount then y else x))[edgeID net.rows tag.1]?).getD false
  rw [read_position]
  simp only [tagBits,hside]
  by_cases hv : v.val < net.leftCount
  · simp only [hv,decide_true,ite_true]
  · simp only [hv,decide_false,Bool.false_eq_true,ite_false]

end
end RiemannGaussian.SemiprimeD1ParentOriginalAssignment
