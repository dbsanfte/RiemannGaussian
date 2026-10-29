/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecursiveCallTree

/-! # Inherited structural state of actual recursive calls
All membership premises refer to the literal child list of the closed
controller. Fresh-axis positivity, original history precision and scope shrink
are derived from that membership, not supplied as a child solution or label.
-/
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1RecursiveCallState
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1RecursiveCallTree SemiprimeD1WireKernelOriginal

/-- Actual positive active scope gives a positive original tapered height. -/
theorem height_positive (M u : ℕ) (hu : 0 < u) (huM : u ≤ M) :
    0 < SemiprimeD1ModeRate.jetHeight M u := by
  have hn : u ≤ 3*M+u-1 := by omega
  have hd : 1 ≤ (3*M+u-1)/u :=
    (Nat.le_div_iff_mul_le hu).mpr (by simpa only [one_mul] using hn)
  exact lt_of_lt_of_le Nat.zero_lt_one hd

/-- Every stored child preserves all old axes and adds one positive fresh axis. -/
theorem child_positive (parent : Call) (a u : ℕ) (t : Fin (size a)) (i : Fin a)
    (beta : List ℕ) (g : Fin 64) (hp : parent.ctx.Positive)
    (hq : 0 < SemiprimeD1ModeRate.jetHeight (edgeCount parent.net) u * (u-i.val)) :
    (child parent a u t i beta g).ctx.Positive := by
  intro k hk
  rcases List.mem_cons.mp hk with rfl | hk
  · exact hq
  · exact hp k hk

/-- Actual child scalar precision is the literal D.11 history update. -/
theorem child_precision (parent : Call) (a u : ℕ) (t : Fin (size a)) (i : Fin a)
    (beta : List ℕ) (g : Fin 64) :
    (child parent a u t i beta g).ctx.precision =
      SemiprimeD1ModeRate.workingPrecision (edgeCount parent.net) u a i.val parent.ctx.precision := by
  exact SemiprimeD1RecursivePhaseBounds.source_precision parent.net a u i.val parent.ctx.precision

/-- Actual fromSource rows are precisely the original acquired child rows used
by the already proved scope contraction theorem. -/
theorem child_rows (parent : Call) (a u : ℕ) (t : Fin (size a)) (i : Fin a)
    (beta : List ℕ) (g : Fin 64) :
    (child parent a u t i beta g).net.rows =
      SemiprimeD1TensorNetworkRecursion.child parent.net a i g := by
  change (SemiprimeD1ChildNetwork.fromSource _ _ _ _ _ _ _ _ _ _).network.rows = _
  rw [SemiprimeD1ChildNetwork.fromSource_rows]
  rfl

/-- Both original degree guards imply actual child scope shrink; beta and the
fresh words do not change the actually constructed child graph. -/
theorem child_shrink (parent : Call) (a u degree : ℕ) (t : Fin (size a)) (i : Fin a)
    (beta : List ℕ) (g : Fin 64) (hw : WellFormed parent.net)
    (hd : SemiprimeD1TensorNetworkRecursion.DegreeBound parent.net degree)
    (hsmall : 2*(64^(2*a))^2*degree ≤ edgeCount parent.net) :
    edgeCount (child parent a u t i beta g).net * 8 ≤ edgeCount parent.net := by
  change scope (child parent a u t i beta g).net.rows * 8 ≤ _
  rw [child_rows]
  exact SemiprimeD1TensorNetworkRecursion.child_shrink_eight parent.net hw degree a hd hsmall i g

/-- Every actual child has exactly the next schedule depth. -/
theorem mem_children_depth (s : ℕ) (parent next : Call) (hm : next ∈ children s parent) :
    next.depth = parent.depth+1 := by
  obtain ⟨_,t,ht⟩ := (mem_children s parent next).mp hm
  obtain ⟨hi,beta,_,g,rfl⟩ := (mem_phaseChildren parent _ _ t next).mp ht
  rfl

/-- Actual child membership inherits positive axes, canonical original ports
and actual canonical table data from the parent. -/
theorem mem_children_shape (s : ℕ) (parent next : Call) (hm : next ∈ children s parent)
    (hp : parent.ctx.Positive) (hg : Good parent.ctx parent.net) :
    next.ctx.Positive ∧ WellFormed next.net ∧ Good next.ctx next.net := by
  obtain ⟨ha,t,ht⟩ := (mem_children s parent next).mp hm
  obtain ⟨hi,beta,_,g,rfl⟩ := (mem_phaseChildren parent _ _ t next).mp ht
  have hactive := (activeTest_correct _ _ _ _).mp ha
  have hu := SemiprimeD1Schedule.active_positive _ _ _ _ hactive
  have hh := height_positive _ _ hu hactive.2.2
  have hq := Nat.mul_pos hh (Nat.sub_pos_of_lt hi.2.1)
  exact ⟨child_positive parent _ _ t _ beta g hp hq,
    child_wellFormed parent _ _ t _ beta g,child_good parent _ _ t _ beta g hg hq⟩

/-- No reachable call needs a shape, positivity or well-formedness oracle. -/
theorem reach_shape (s : ℕ) (root next : Call) (hr : Reach s root next)
    (hp : root.ctx.Positive) (hw : WellFormed root.net) (hg : Good root.ctx root.net) :
    next.ctx.Positive ∧ WellFormed next.net ∧ Good next.ctx next.net := by
  induction hr with
  | root => exact ⟨hp,hw,hg⟩
  | step hr hm ih => exact mem_children_shape s _ _ hm ih.1 ih.2.2

/-- Every reachable depth is at least the literal root depth. -/
theorem reach_depth (s : ℕ) (root next : Call) (hr : Reach s root next) : root.depth ≤ next.depth := by
  induction hr with
  | root => exact le_rfl
  | step hr hm ih => rw [mem_children_depth s _ _ hm];omega

/-- Every actual child inherits a genuine original valuation level and the
literal D.11 update at that level. -/
theorem mem_children_precision (s : ℕ) (parent next : Call) (hm : next ∈ children s parent) :
    ∃ i < SemiprimeD1Schedule.levels (SemiprimeD1PackingReady.logarithm s) parent.depth,
    next.ctx.precision = SemiprimeD1ModeRate.workingPrecision (edgeCount parent.net)
      (SemiprimeD1Schedule.levels (SemiprimeD1PackingReady.logarithm s) parent.depth)
      (SemiprimeD1Schedule.exponent (SemiprimeD1PackingReady.logarithm s) parent.depth)
      i parent.ctx.precision := by
  obtain ⟨_,t,ht⟩ := (mem_children s parent next).mp hm
  obtain ⟨hi,beta,_,g,rfl⟩ := (mem_phaseChildren parent _ _ t next).mp ht
  exact ⟨_,hi.2.1,child_precision parent _ _ t _ beta g⟩

/-- Uniform original-scale packing acceptance derives shrink on EVERY actual
active child, conditional only on the parent's actual stored degree cap. -/
theorem eventually_mem_children_shrink : ∀ᶠ s : ℕ in Filter.atTop,
    ∀ parent next : Call, next ∈ children s parent → WellFormed parent.net →
      SemiprimeD1TensorNetworkRecursion.DegreeBound parent.net (SemiprimeD1PackingReady.degreeCap s) →
      edgeCount next.net*8 ≤ edgeCount parent.net := by
  filter_upwards [SemiprimeD1PackingReady.eventually_all_depths] with s hs
  intro parent next hm hw hd
  obtain ⟨ha,t,ht⟩ := (mem_children s parent next).mp hm
  obtain ⟨hi,beta,_,g,rfl⟩ := (mem_phaseChildren parent _ _ t next).mp ht
  have hactive := (activeTest_correct _ _ _ _).mp ha
  have hpacking := hs parent.depth (edgeCount parent.net) _ hactive le_rfl
  exact child_shrink parent _ _ _ t _ beta g hw hd hpacking.1.le

end RiemannGaussian.SemiprimeD1RecursiveCallState
