/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecursiveCallPath

/-! # Actual acquired branching from original reachable-call invariants
No arbitrary network history, menu size, precision or packing acceptance is
supplied. The original root bounds propagate through actual Reach, then imply
the D.11 guards at every literal acquired phase.
-/
set_option autoImplicit false
set_option maxHeartbeats 160000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1RecursiveCallModes
open scoped BigOperators
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1RecursiveCallTree SemiprimeD1RecursiveCallState SemiprimeD1RecursiveCallInventory
open SemiprimeD1RecursiveCallPath SemiprimeD1Schedule SemiprimeD1PrecisionEnvelope
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire

/-- Original computed precision cap implies all actual mode guards at this call. -/
theorem state_guards (s : ℕ) (call : Call)
    (ha : Active s (SemiprimeD1PackingReady.logarithm s) call.depth (edgeCount call.net))
    (hp : call.ctx.precision ≤ pathCap s (SemiprimeD1PackingReady.logarithm s)
      call.depth (previous (SemiprimeD1PackingReady.logarithm s) call.depth))
    (i : ℕ) (hi : i < levels (SemiprimeD1PackingReady.logarithm s) call.depth) :
    i ≤ exponent (SemiprimeD1PackingReady.logarithm s) call.depth ∧
    call.ctx.precision*levels (SemiprimeD1PackingReady.logarithm s) call.depth ≤
      edgeCount call.net*2^(exponent (SemiprimeD1PackingReady.logarithm s) call.depth-i) ∧
    (exponent (SemiprimeD1PackingReady.logarithm s) call.depth+1)*
      levels (SemiprimeD1PackingReady.logarithm s) call.depth ≤
      2^(exponent (SemiprimeD1PackingReady.logarithm s) call.depth-i) := by
  have hu := active_positive _ _ _ _ ha
  have hd := depth_le _ _ hu
  refine ⟨hi.le.trans (SemiprimeD1RecursivePhaseControl.schedule_levels_le_exponent _ _),?_,?_⟩
  · exact input_guard s _ call.depth _ _ _ _ i _ hp hd
      (active_size _ _ _ _ ha) (levels_le _ _) ha.2.1 (by rfl) hi.le
  · exact evaluation_guard _ _ _ i (levels_le _ _) ha.2.1 (exponent_le_lam _ _)
      (by unfold exponent;omega) hi.le

/-- All actual acquired menus on all reachable active calls have the original
48M/sqrt(u) exponent, with input scale and precision premises only at the root. -/
theorem eventually_reach_menu : ∀ᶠ s : ℕ in Filter.atTop,
    ∀ root call : Call, root.depth=0 → edgeCount root.net ≤ s → root.ctx.precision ≤ s →
      root.ctx.Positive → WellFormed root.net → Good root.ctx root.net →
      SemiprimeD1TensorNetworkRecursion.DegreeBound root.net (SemiprimeD1PackingReady.degreeCap s) →
      Reach s root call →
      Active s (SemiprimeD1PackingReady.logarithm s) call.depth (edgeCount call.net) →
      ∀ i < levels (SemiprimeD1PackingReady.logarithm s) call.depth,
      ((SemiprimeD1OriginalModeAcquisition.acquire call.net.leftCount call.net.rows.length 64
        (exponent (SemiprimeD1PackingReady.logarithm s) call.depth)
        (levels (SemiprimeD1PackingReady.logarithm s) call.depth) i call.ctx.precision
        (arity call.net.rows) (owner call.net.rows)).modes.values.length : ℝ) ≤
      Real.exp (48*(edgeCount call.net : ℝ)/
        Real.sqrt (levels (SemiprimeD1PackingReady.logarithm s) call.depth : ℕ)) := by
  filter_upwards [eventually_reach_invariant,SemiprimeD1PackingReady.eventually_all_depths] with s hinv hpack
  intro root call hr hM hp hpos hw hg hd hreach ha i hi
  have hin := hinv root call hr hM hp hpos hw hg hd hreach
  have hshape := reach_shape s root call hreach hpos hw hg
  have hpck := hpack call.depth (edgeCount call.net) _ ha le_rfl
  have hdegrees := SemiprimeD1TensorNetworkRecursion.original_degree_contract call.net
    hshape.2.1 _ (exponent (SemiprimeD1PackingReady.logarithm s) call.depth) hin.1
  have hguards := state_guards s call ha hin.2.2 i hi
  have hports : (SemiprimeD1CollisionOriginal.ports call.net.leftCount call.net.rows.length
      (exponent (SemiprimeD1PackingReady.logarithm s) call.depth) (arity call.net.rows)).length =
      edgeCount call.net := by
    rw [SemiprimeD1TensorNetworkLayout.original_ports]
    rfl
  have hbound := SemiprimeD1OriginalModeAcquisition.menu_bound call.net.leftCount call.net.rows.length 64
    (exponent (SemiprimeD1PackingReady.logarithm s) call.depth)
    (levels (SemiprimeD1PackingReady.logarithm s) call.depth) i call.ctx.precision
    (arity call.net.rows) (owner call.net.rows) (SemiprimeD1PackingReady.degreeCap s)
    hdegrees.1 hdegrees.2 (by rw [hports];exact hpck.1.le)
    (by rw [hports];exact hpck.2.1.le) hguards.1 (active_positive _ _ _ _ ha)
    (by rw [hports];exact ha.2.2) (by rw [hports];exact hguards.2.1) hguards.2.2
  rw [hports] at hbound
  exact hbound

end RiemannGaussian.SemiprimeD1RecursiveCallModes
