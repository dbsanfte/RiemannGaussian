/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryPartitionOriginalRate
import RiemannGaussian.SemiprimeD1BoundaryNetworkDegree
import RiemannGaussian.SemiprimeD1LeafReady
import RiemannGaussian.SemiprimeD1RecursiveLeafBounds

/-! # Actual reachable stopped boundary leaves have the half exponent -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1BoundaryPartitionReachRate
open Filter SemiprimeD1TensorNetwork SemiprimeD1JetAxes
open SemiprimeD1RecursiveCounter SemiprimeD1RecursiveCallTree
open SemiprimeD1RecursiveCallState SemiprimeD1RecursiveCallPath
open SemiprimeD1BoundaryPlan SemiprimeD1PackingReady
open SemiprimeD1BoundaryPartitionOriginalRate

/-- Every actually reachable stopped leaf has half the original leaf exponent,
including edgeless leaves; its colour count and partition are both executed. -/
theorem eventually_reach_stopped_width_half (e : Real) (he : 0 < e) :
    ∀ᶠ s : Nat in atTop, ∀ root call : Call,
      root.depth = 0 → edgeCount root.net ≤ s → root.ctx.precision ≤ s →
      root.ctx.Positive → WellFormed root.net → Good root.ctx root.net →
      SemiprimeD1TensorNetworkRecursion.DegreeBound root.net (degreeCap s) →
      Reach s root call →
      activeTest s (logarithm s) call.depth (edgeCount call.net) = false →
      (SemiprimeD1BoundaryLeafReport.width call.ctx call.net : Real) ≤
        (1 / 2 + e) * ((s : Real) / Real.sqrt (logarithm s : Real)) := by
  filter_upwards [eventually_acquired_width_half_all e he,
    SemiprimeD1LeafReady.eventually_rootReady, eventually_reach_invariant] with s hs hready hinv
  intro root call hr hM hp hpos hw hgood hd hreach hstop
  have hin := hinv root call hr hM hp hpos hw hgood hd hreach
  have hshape := reach_shape s root call hreach hpos hw hgood
  have hstopped : ¬ SemiprimeD1Schedule.Active s (logarithm s) call.depth (edgeCount call.net) := by
    intro ha
    have ht := (activeTest_correct _ _ _ _).mpr ha
    rw [hstop] at ht
    exact Bool.false_ne_true ht
  have hedge := SemiprimeD1LeafRate.inactive_real_leaf s (logarithm s) call.depth
    (edgeCount call.net) hready hin.2.1 hstopped
  have hgraph : ((graph call.net).edges.length : Real) ≤
      (s : Real) / Real.sqrt (logarithm s : Real) + 1 := by
    simpa only [graph_edges_length] using hedge
  have hdegree := SemiprimeD1BoundaryNetworkDegree.maxDegree_le call.net hshape.2.1
    (degreeCap s) hin.1
  have hplan := hs (graph call.net) (SemiprimeD1BoundaryPotential.graph_valid call.net)
    hgraph hdegree
  have hleaf := SemiprimeD1BoundaryLeafLoad.width_le_plan call.ctx call.net hshape.2.1
  have hleafR : (SemiprimeD1BoundaryLeafReport.width call.ctx call.net : Real) ≤
      ((acquire (graph call.net)).width : Real) := by exact_mod_cast hleaf
  exact hleafR.trans hplan

/-- Exhausting the actual original logarithmic fuel yields the same half exponent. -/
theorem eventually_reach_zero_fuel_width_half (e : Real) (he : 0 < e) :
    ∀ᶠ s : Nat in atTop, ∀ root call : Call,
      root.depth = 0 → edgeCount root.net ≤ s → root.ctx.precision ≤ s →
      root.ctx.Positive → WellFormed root.net → Good root.ctx root.net →
      SemiprimeD1TensorNetworkRecursion.DegreeBound root.net (degreeCap s) →
      Reach s root call → logarithm s + 1 ≤ call.depth + 0 →
      (SemiprimeD1BoundaryLeafReport.width call.ctx call.net : Real) ≤
        (1 / 2 + e) * ((s : Real) / Real.sqrt (logarithm s : Real)) := by
  filter_upwards [eventually_reach_stopped_width_half e he] with s hs
  intro root call hr hM hp hpos hw hgood hd hreach hf
  exact hs root call hr hM hp hpos hw hgood hd hreach
    (SemiprimeD1RecursiveLeafBounds.zero_fuel_inactive s call.depth hf (edgeCount call.net))

end RiemannGaussian.SemiprimeD1BoundaryPartitionReachRate
