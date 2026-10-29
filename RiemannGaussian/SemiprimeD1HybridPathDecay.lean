/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecursiveCallPath

/-! # Factor-sixteen decay along every actual recursive child
The original stored-degree and packing hypotheses already prove the stronger
shrink. This file preserves all actual grid/mode/group choices and inherits
shape from the unchanged controller. It changes analysis, not the program.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1HybridPathDecay
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1RecursiveCallTree SemiprimeD1RecursiveCallState
open SemiprimeD1TensorNetworkRecursion (DegreeBound)
open SemiprimeD1Schedule SemiprimeD1WireKernelOriginal
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire

/-- The literal child rows satisfy the original factor-sixteen theorem. -/
theorem child_shrink_sixteen (parent : Call) (a u degree : ℕ)
    (t : Fin (size a)) (i : Fin a) (beta : List ℕ) (g : Fin 64)
    (hw : WellFormed parent.net) (hd : DegreeBound parent.net degree)
    (hsmall : 2*(64^(2*a))^2*degree ≤ edgeCount parent.net) :
    edgeCount (child parent a u t i beta g).net*16 ≤ edgeCount parent.net := by
  change scope (child parent a u t i beta g).net.rows*16 ≤ _
  rw [child_rows]
  rw [Nat.mul_comm]
  exact SemiprimeD1TensorNetworkRecursion.child_shrink parent.net hw degree a hd hsmall i g

/-- Eventual original-scale packing pays factor-sixteen shrink for every member
of the actual child list, with no selected-mode or supplied-size premise. -/
theorem eventually_mem_children_shrink : ∀ᶠ s : ℕ in Filter.atTop,
    ∀ parent next : Call, next ∈ children s parent → WellFormed parent.net →
      DegreeBound parent.net (SemiprimeD1PackingReady.degreeCap s) →
      edgeCount next.net*16 ≤ edgeCount parent.net := by
  filter_upwards [SemiprimeD1PackingReady.eventually_all_depths] with s hs
  intro parent next hm hw hd
  obtain ⟨ha,t,ht⟩ := (mem_children s parent next).mp hm
  obtain ⟨hi,beta,_,g,rfl⟩ := (mem_phaseChildren parent _ _ t next).mp ht
  have hactive := (activeTest_correct _ _ _ _).mp ha
  have hpacking := hs parent.depth (edgeCount parent.net) _ hactive le_rfl
  exact child_shrink_sixteen parent _ _ _ t _ beta g hw hd hpacking.1.le

/-- All genuinely reachable calls satisfy factor-sixteen scaled decay, under
exactly the old root-state assumptions. The precision and degree invariants
are reused without altering their statements or any source program. -/
theorem eventually_reach_sixteen : ∀ᶠ s : ℕ in Filter.atTop,
    ∀ root next : Call, root.depth=0 → edgeCount root.net ≤ s → root.ctx.precision ≤ s →
      root.ctx.Positive → WellFormed root.net → Good root.ctx root.net →
      DegreeBound root.net (SemiprimeD1PackingReady.degreeCap s) → Reach s root next →
      edgeCount next.net*16^next.depth ≤ s := by
  filter_upwards [SemiprimeD1HybridPathDecay.eventually_mem_children_shrink,
    SemiprimeD1RecursiveCallPath.eventually_reach_invariant] with s hshrink hinv
  intro root next hroot hM hp hpos hw hg hd hr
  induction hr with
  | root => simpa only [hroot,pow_zero,Nat.mul_one] using hM
  | @step parent next hr hm ih =>
    have hshape := reach_shape s root parent hr hpos hw hg
    have hdegree := (hinv root parent hroot hM hp hpos hw hg hd hr).1
    have hsh := hshrink parent next hm hshape.2.1 hdegree
    rw [mem_children_depth s parent next hm,pow_succ]
    calc
      _ = (edgeCount next.net*16)*16^parent.depth := by ring
      _ ≤ edgeCount parent.net*16^parent.depth := Nat.mul_le_mul_right _ hsh
      _ ≤ s := ih

end RiemannGaussian.SemiprimeD1HybridPathDecay
