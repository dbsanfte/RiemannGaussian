/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecursiveCallPath

/-! # Uniform literal data bounds at actual reachable recursive calls
The relation is the real controller's child list. No network history, packet
count, inherited precision or storage answer is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1RecursiveStateResources
open SemiprimeD1RecursiveCallTree SemiprimeD1RecursiveCallState
open SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkRecursion
open SemiprimeD1NetworkStateResources SemiprimeD1Schedule
open SemiprimeD1JetAxes

/-- Every actual child adds at most3M observed packet vertices. -/
theorem mem_children_vertex_growth (s : ℕ) (parent next : Call) (hm : next∈children s parent)
    (D : ℕ) (hw : WellFormed parent.net) (hd : DegreeBound parent.net D)
    (hsmall : 2*(64^(2*exponent (SemiprimeD1PackingReady.logarithm s) parent.depth))^2*D ≤ edgeCount parent.net)
    (hsize : 64^(2*exponent (SemiprimeD1PackingReady.logarithm s) parent.depth)*
      2^exponent (SemiprimeD1PackingReady.logarithm s) parent.depth ≤ edgeCount parent.net) :
    vertexCount next.net ≤ vertexCount parent.net+3*edgeCount parent.net := by
  obtain ⟨_,t,ht⟩:=(mem_children s parent next).mp hm
  obtain ⟨hi,beta,_,g,rfl⟩:=(mem_phaseChildren parent _ _ t next).mp ht
  exact SemiprimeD1ChildStateResources.child_vertex_growth parent.net hw D _ _ hd hsmall hsize
    _ g parent.ctx _ _ _ t beta

/-- The actual fresh dimension is at most4M; old axes are literally retained. -/
theorem mem_children_axes (s : ℕ) (parent next : Call) (hm : next∈children s parent) :
    ∃q ≤ 4*edgeCount parent.net,next.ctx.axes=q::parent.ctx.axes := by
  obtain ⟨ha,t,ht⟩:=(mem_children s parent next).mp hm
  obtain ⟨hi,beta,_,g,rfl⟩:=(mem_phaseChildren parent _ _ t next).mp ht
  have hactive:=(SemiprimeD1RecursiveCounter.activeTest_correct _ _ _ _).mp ha
  refine ⟨_,?_,rfl⟩
  exact (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans
    (SemiprimeD1ModeRate.jetHeight_mul_le _ _ hactive.2.2)

/-- Every genuinely reachable child is born by depth lambda+1, including leaves. -/
theorem reach_depth_le (s : ℕ) (root next : Call) (hroot : root.depth=0)
    (hr : Reach s root next) : next.depth ≤ SemiprimeD1PackingReady.logarithm s+1 := by
  induction hr with
  | root => rw [hroot];omega
  | @step parent next hr hm ih =>
    have ha:=(SemiprimeD1RecursiveCounter.activeTest_correct _ _ _ _).mp ((mem_children s parent next).mp hm).1
    have hd:=SemiprimeD1Schedule.depth_le _ _ (SemiprimeD1Schedule.active_positive _ _ _ _ ha)
    rw [mem_children_depth s parent next hm]
    omega

/-- The same201 quadratic precision reserve also covers terminal children at
lambda+1; it does not require incorrectly treating those leaves as active. -/
theorem precision_cap_leaf (s lam depth prev : ℕ) (hd : depth ≤ lam+1) :
    SemiprimeD1PrecisionEnvelope.pathCap s lam depth prev ≤ s*(201*(lam+1)^2)*2^prev := by
  have h : SemiprimeD1PrecisionEnvelope.pathFactor lam depth ≤ 201*(lam+1)^2 := by
    unfold SemiprimeD1PrecisionEnvelope.pathFactor
    have hm:=Nat.mul_le_mul_right (40*(4*lam+1)) hd
    nlinarith
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h)

/-- The actual recursive-data envelope. Root premises refer to its literal
stored data; the original binary-input instance discharges them separately. -/
theorem eventually_reach_resources : ∀ᶠ s : ℕ in Filter.atTop,
    ∀ root next : Call, root.depth=0 → root.ctx.axes=[] → edgeCount root.net ≤ s →
      root.ctx.precision ≤ s → root.ctx.Positive → WellFormed root.net → Good root.ctx root.net →
      DegreeBound root.net (SemiprimeD1PackingReady.degreeCap s) → Reach s root next →
      vertexCount next.net+4*edgeCount next.net ≤ vertexCount root.net+4*edgeCount root.net ∧
      next.depth ≤ SemiprimeD1PackingReady.logarithm s+1 ∧
      next.ctx.axes.length=next.depth ∧
      (∀q∈next.ctx.axes,q ≤ 4*s) ∧
      next.ctx.rank ≤ (4*s)^(SemiprimeD1PackingReady.logarithm s+1) ∧
      next.ctx.precision ≤ s*(201*(SemiprimeD1PackingReady.logarithm s+1)^2)*
        2^(previous (SemiprimeD1PackingReady.logarithm s) next.depth) := by
  filter_upwards [SemiprimeD1RecursiveCallPath.eventually_reach_invariant,
    SemiprimeD1PackingReady.eventually_all_depths,eventually_mem_children_shrink,
    Filter.eventually_ge_atTop (1:ℕ)] with s hinv hpack hshrink hs
  intro root next hroot haxes hM hp hpos hw hg hd hr
  have hdata : vertexCount next.net+4*edgeCount next.net ≤ vertexCount root.net+4*edgeCount root.net ∧
      next.ctx.axes.length=next.depth ∧ (∀q∈next.ctx.axes,q ≤ 4*s) := by
    induction hr with
    | root => simp [haxes,hroot]
    | @step parent next hr hm ih =>
      have hshape:=reach_shape s root parent hr hpos hw hg
      have hparent:=hinv root parent hroot hM hp hpos hw hg hd hr
      have ha:=(SemiprimeD1RecursiveCounter.activeTest_correct _ _ _ _).mp ((mem_children s parent next).mp hm).1
      have hpk:=hpack parent.depth (edgeCount parent.net) _ ha le_rfl
      have hNF:=mem_children_vertex_growth s parent next hm _ hshape.2.1 hparent.1 hpk.1.le hpk.2.1.le
      have hMchild:=hshrink parent next hm hshape.2.1 hparent.1
      have hNFpotential:=vertex_potential parent.net next.net hNF (by omega)
      obtain ⟨q,hq,hqaxes⟩:=mem_children_axes s parent next hm
      have hparentM:=SemiprimeD1RecursiveCallPath.edges_le_of_scaled s parent hparent.2.1
      refine ⟨hNFpotential.trans ih.1,?_,?_⟩
      · rw [hqaxes,List.length_cons,ih.2.1,mem_children_depth s parent next hm]
      · intro k hk
        rw [hqaxes] at hk
        rcases List.mem_cons.mp hk with rfl|hk
        · omega
        · exact ih.2.2 k hk
  have hdepth:=reach_depth_le s root next hroot hr
  have hrank : next.ctx.rank ≤ (4*s)^next.depth := by
    simpa only [Context.rank,hdata.2.1] using List.prod_le_pow_length next.ctx.axes (4*s) hdata.2.2
  have hprecision:=(hinv root next hroot hM hp hpos hw hg hd hr).2.2
  exact ⟨hdata.1,hdepth,hdata.2.1,hdata.2.2,
    hrank.trans (Nat.pow_le_pow_right (by omega) hdepth),
    hprecision.trans (precision_cap_leaf s _ _ _ hdepth)⟩

end RiemannGaussian.SemiprimeD1RecursiveStateResources
