/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecursiveCallInventory
import RiemannGaussian.SemiprimeD1ChildStateResources

/-! # Original-input bounds on every actual controller path
Reachability uses the controller's literal acquired child list. The global
stored-degree cap, geometric edge decay and computed precision envelope are
inherited by induction; no arbitrary edge history or accepted mode bound is
supplied. Root numerical premises concern only actual input dimensions.
-/
set_option autoImplicit false
set_option maxHeartbeats 120000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1RecursiveCallPath
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1RecursiveCallTree SemiprimeD1RecursiveCallState
open SemiprimeD1TensorNetworkRecursion SemiprimeD1Schedule SemiprimeD1PrecisionEnvelope

/-- Every actual child preserves a stored degree cap that pays new packet scopes. -/
theorem mem_children_degree (s : ℕ) (parent next : Call) (hm : next ∈ children s parent)
    (D : ℕ) (hw : WellFormed parent.net) (hd : DegreeBound parent.net D)
    (hslots : 2*2^(exponent (SemiprimeD1PackingReady.logarithm s) parent.depth) ≤ D) :
    DegreeBound next.net D := by
  obtain ⟨_,t,ht⟩ := (mem_children s parent next).mp hm
  obtain ⟨hi,beta,_,g,rfl⟩ := (mem_phaseChildren parent _ _ t next).mp ht
  exact SemiprimeD1ChildStateResources.child_degree parent.net hw D _ _ hd hslots
    _ g parent.ctx _ _ _ t beta

/-- Exact child membership propagates the original computed precision cap. -/
theorem mem_children_precision_cap (s : ℕ) (parent next : Call)
    (hm : next ∈ children s parent) (hM : edgeCount parent.net ≤ s)
    (hp : parent.ctx.precision ≤ pathCap s (SemiprimeD1PackingReady.logarithm s)
      parent.depth (previous (SemiprimeD1PackingReady.logarithm s) parent.depth)) :
    next.ctx.precision ≤ pathCap s (SemiprimeD1PackingReady.logarithm s)
      next.depth (previous (SemiprimeD1PackingReady.logarithm s) next.depth) := by
  have hactive := (activeTest_correct _ _ _ _).mp ((mem_children s parent next).mp hm).1
  obtain ⟨i,_,hi⟩ := mem_children_precision s parent next hm
  rw [hi,mem_children_depth s parent next hm,previous_succ]
  exact update_cap s _ parent.depth _ (edgeCount parent.net) _ _ i parent.ctx.precision
    hM hactive.2.2 (exponent_le_lam _ _) (Nat.le_add_right _ _) hp

/-- The scaled edge bound implies the unscaled bound without an input oracle. -/
theorem edges_le_of_scaled (s : ℕ) (call : Call) (h : edgeCount call.net*8^call.depth ≤ s) :
    edgeCount call.net ≤ s := by
  have hpow : 1 ≤ (8:ℕ)^call.depth := Nat.one_le_pow _ _ (by decide)
  have hm : edgeCount call.net ≤ edgeCount call.net*8^call.depth := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (edgeCount call.net) hpow
  exact hm.trans h

/-- ALL actual reachable calls inherit the original degree, scope-decay and
working-precision invariants. Only actual root dimensions and stored data are premises. -/
theorem eventually_reach_invariant : ∀ᶠ s : ℕ in Filter.atTop,
    ∀ root next : Call, root.depth=0 → edgeCount root.net ≤ s → root.ctx.precision ≤ s →
      root.ctx.Positive → WellFormed root.net → Good root.ctx root.net →
      DegreeBound root.net (SemiprimeD1PackingReady.degreeCap s) → Reach s root next →
      DegreeBound next.net (SemiprimeD1PackingReady.degreeCap s) ∧
      edgeCount next.net*8^next.depth ≤ s ∧
      next.ctx.precision ≤ pathCap s (SemiprimeD1PackingReady.logarithm s)
        next.depth (previous (SemiprimeD1PackingReady.logarithm s) next.depth) := by
  filter_upwards [SemiprimeD1PackingReady.eventually_all_depths,
    eventually_mem_children_shrink] with s hs hshrink
  intro root next hroot hM hp hpos hw hg hd hr
  induction hr with
  | root =>
    refine ⟨hd,?_,?_⟩
    · simpa only [hroot,pow_zero,Nat.mul_one] using hM
    · simpa only [hroot,previous,Finset.sum_range_zero,Nat.mul_zero,root_cap] using hp
  | @step parent next hr hm ih =>
    have hshape := reach_shape s root parent hr hpos hw hg
    have hactive := (activeTest_correct _ _ _ _).mp ((mem_children s parent next).mp hm).1
    have hpacking := hs parent.depth (edgeCount parent.net) _ hactive le_rfl
    have hslots := (le_max_right _ _).trans hpacking.2.2
    have hdegree := mem_children_degree s parent next hm _ hshape.2.1 ih.1 hslots
    have hsh := hshrink parent next hm hshape.2.1 ih.1
    have hedge : edgeCount next.net*8^next.depth ≤ s := by
      rw [mem_children_depth s parent next hm,pow_succ]
      calc
        _ = (edgeCount next.net*8)*8^parent.depth := by ring
        _ ≤ edgeCount parent.net*8^parent.depth := Nat.mul_le_mul_right _ hsh
        _ ≤ s := ih.2.1
    exact ⟨hdegree,hedge,mem_children_precision_cap s parent next hm
      (edges_le_of_scaled s parent ih.2.1) ih.2.2⟩

end RiemannGaussian.SemiprimeD1RecursiveCallPath
