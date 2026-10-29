/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecursiveCallState

/-! # Actual branching multiplicities and finite controller depth
The child counts are the acquired mode lengths times the literal64 groups,
with the original grid and branch tests retained. The schedule itself stops
branching beyond the original logarithmic depth, independently of fuel.
-/
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1RecursiveCallInventory
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1RecursiveCallTree SemiprimeD1RecursiveCallState SemiprimeD1WireKernelOriginal
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire

/-- Literal phase branching count, under precisely its executed original guard. -/
theorem phaseChildren_length (parent : Call) (a u : ℕ) (t : Fin (size a))
    (hi : (SemiprimeD1RecoveryScalarRun.orderFuel
      (SemiprimeD1RecoveryWeightRun.geometry a t.val).size
      (SemiprimeD1RecoveryWeightRun.geometry a t.val).point.natAbs).value < a ∧
      (SemiprimeD1RecoveryScalarRun.orderFuel
      (SemiprimeD1RecoveryWeightRun.geometry a t.val).size
      (SemiprimeD1RecoveryWeightRun.geometry a t.val).point.natAbs).value < u ∧
      (SemiprimeD1RecoveryWeightRun.geometry a t.val).point ≠ 0) :
    (phaseChildren parent a u t).length =
      (SemiprimeD1OriginalModeAcquisition.acquire parent.net.leftCount parent.net.rows.length 64 a u
        (SemiprimeD1RecoveryScalarRun.orderFuel
          (SemiprimeD1RecoveryWeightRun.geometry a t.val).size
          (SemiprimeD1RecoveryWeightRun.geometry a t.val).point.natAbs).value
        parent.ctx.precision (arity parent.net.rows) (owner parent.net.rows)).modes.values.length*64 := by
  dsimp only [phaseChildren]
  rw [dite_eq_left hi]
  simp only [List.length_flatMap,List.length_map,List.length_finRange,List.map_const',List.sum_replicate,smul_eq_mul]

/-- The actual active grid count is the sum of actual per-phase child counts. -/
theorem children_length (s : ℕ) (parent : Call)
    (ha : activeTest s (SemiprimeD1PackingReady.logarithm s) parent.depth (edgeCount parent.net)=true) :
    (children s parent).length =
      ((List.finRange (size (SemiprimeD1Schedule.exponent (SemiprimeD1PackingReady.logarithm s) parent.depth))).map
        (fun t => (phaseChildren parent
          (SemiprimeD1Schedule.exponent (SemiprimeD1PackingReady.logarithm s) parent.depth)
          (SemiprimeD1Schedule.levels (SemiprimeD1PackingReady.logarithm s) parent.depth) t).length)).sum := by
  dsimp only [children]
  rw [ite_eq_left ha,List.length_flatMap]

/-- Reachability composes using only literal actual-child steps. -/
theorem reach_trans (s : ℕ) (root middle last : Call)
    (hm : Reach s root middle) (hl : Reach s middle last) : Reach s root last := by
  induction hl with
  | root => exact hm
  | step h hmem ih => exact Reach.step ih hmem

/-- Every inventoried call is genuinely reachable from this literal root. -/
theorem trace_reach (s fuel : ℕ) (root next : Call) (hm : next ∈ trace s fuel root) :
    Reach s root next := by
  induction fuel generalizing root with
  | zero =>
    have he : next=root := by simpa only [trace,List.mem_singleton] using hm
    subst next
    exact Reach.root
  | succ fuel ih =>
    rcases List.mem_cons.mp hm with he | hm
    · subst next;exact Reach.root
    · obtain ⟨middle,hmid,hnext⟩ := List.mem_flatMap.mp hm
      exact reach_trans s root middle next (Reach.step Reach.root hmid) (ih middle hnext)

/-- Actual trace depth never exceeds its literal root depth plus supplied fuel. -/
theorem trace_depth (s fuel : ℕ) (root next : Call) (hm : next ∈ trace s fuel root) :
    next.depth ≤ root.depth+fuel := by
  induction fuel generalizing root with
  | zero =>
    have he : next=root := by simpa only [trace,List.mem_singleton] using hm
    subst next;omega
  | succ fuel ih =>
    rcases List.mem_cons.mp hm with he | hm
    · subst next;omega
    · obtain ⟨middle,hmid,hnext⟩ := List.mem_flatMap.mp hm
      have hd := mem_children_depth s root middle hmid
      have ht := ih middle hnext
      omega

/-- The original schedule stops all actual branching beyond its logarithmic depth. -/
theorem children_nil_of_depth (s : ℕ) (parent : Call)
    (hd : SemiprimeD1PackingReady.logarithm s < parent.depth) : children s parent = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro next hm
  have ha := (activeTest_correct _ _ _ _).mp ((mem_children s parent next).mp hm).1
  have hu := SemiprimeD1Schedule.active_positive _ _ _ _ ha
  have hb := SemiprimeD1Schedule.depth_le _ _ hu
  omega

/-- Such a call executes no recursive child, for every supplied fuel. -/
theorem count_one_of_depth (s fuel : ℕ) (parent : Call)
    (hd : SemiprimeD1PackingReady.logarithm s < parent.depth) : count s fuel parent=1 := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [count,children_nil_of_depth s parent hd,List.map_nil,List.sum_nil,Nat.add_zero]

/-- Increasing fuel beyond the actual schedule-depth cap adds no calls. -/
theorem count_stable (s fuel extra : ℕ) (parent : Call)
    (hd : SemiprimeD1PackingReady.logarithm s+1 ≤ parent.depth+fuel) :
    count s (fuel+extra) parent = count s fuel parent := by
  induction fuel generalizing parent with
  | zero =>
    have hb : SemiprimeD1PackingReady.logarithm s < parent.depth := by omega
    rw [count_one_of_depth s _ parent hb,count_one_of_depth s _ parent hb]
  | succ fuel ih =>
    simp only [Nat.succ_add,count,Nat.zero_add]
    apply congrArg Nat.succ
    apply congrArg List.sum
    apply List.map_congr_left
    intro next hm
    have hn := mem_children_depth s parent next hm
    exact ih next (by omega)

/-- The actual total inventory has a universal original-input fuel cap. -/
theorem count_fuel_cap (s fuel : ℕ) (parent : Call) :
    count s fuel parent = count s (min fuel (SemiprimeD1PackingReady.logarithm s+1)) parent := by
  by_cases hf : fuel ≤ SemiprimeD1PackingReady.logarithm s+1
  · rw [Nat.min_eq_left hf]
  · have hle : SemiprimeD1PackingReady.logarithm s+1 ≤ fuel := by omega
    rw [Nat.min_eq_right hle]
    have h := count_stable s (SemiprimeD1PackingReady.logarithm s+1)
      (fuel-(SemiprimeD1PackingReady.logarithm s+1)) parent (by omega)
    simpa only [Nat.add_sub_of_le hle] using h

end RiemannGaussian.SemiprimeD1RecursiveCallInventory
