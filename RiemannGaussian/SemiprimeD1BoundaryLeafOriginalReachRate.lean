/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryCheckedOriginalRate
import RiemannGaussian.SemiprimeD1BoundaryPartitionReachRate

/-! # Half exponent of actual original-reachable checked boundary leaves -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryLeafOriginalReachRate
open Filter SemiprimeD1PackingReady SemiprimeD1OriginalStateResources
open SemiprimeD1RecursiveCallTree SemiprimeD1RecursiveCallState SemiprimeD1RecursiveCallPath
open SemiprimeD1RootStateResources SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimePublicAcquiredExecution SemiprimeMacroParameters

/-- Every actually reached stopped checked leaf has the uniform leading half
exponent. All context, degree, graph and literal table resources come from the
original binary input; no resource inequality is supplied by the caller. -/
theorem eventually_original_stopped_half (e : Real) (he : 0<e) :
    ∀ᶠ ell : Nat in atTop, ∀ (N : Nat) (hN : 0<N), bitLength N=ell →
    ∀ (fixed : List (Fin (wireCount N) × Bool)) (next : Call),
    Reach (SemiprimeD1PublicPackingReady.scale ell) (originalCall N hN fixed) next →
    activeTest (SemiprimeD1PublicPackingReady.scale ell)
      (logarithm (SemiprimeD1PublicPackingReady.scale ell)) next.depth (edgeCount next.net)=false →
    ((SemiprimeD1BoundaryLeaf.checked next.ctx next.net).clock:Real)≤
      (2:Real)^((1/2+e)*((SemiprimeD1PublicPackingReady.scale ell:Real)/
        Real.sqrt (logarithm (SemiprimeD1PublicPackingReady.scale ell):Real))) := by
  filter_upwards [eventually_original,
    scale_tendsto.eventually (SemiprimeD1BoundaryCheckedOriginalRate.eventually_checked_uniform_half e he),
    scale_tendsto.eventually eventually_reach_invariant,
    scale_tendsto.eventually SemiprimeD1LeafReady.eventually_rootReady] with ell hres hhalf hinv hready
  intro N hN hEll fixed next hreach hstop
  subst ell
  let s:=SemiprimeD1PublicPackingReady.scale (bitLength N)
  have hb:=hres N hN rfl fixed next hreach
  have hroot:=original_shape N hN fixed
  have hrootM:=root_edges_le_scale N hN fixed
  have hrootD:=root_global_degree N hN fixed
  have hi:=hinv (originalCall N hN fixed) next rfl hrootM hroot.2.2.2
    hroot.1 hroot.2.1 hroot.2.2.1 hrootD hreach
  have hshape:=reach_shape s (originalCall N hN fixed) next hreach hroot.1 hroot.2.1 hroot.2.2.1
  have hnot : ¬SemiprimeD1Schedule.Active s (logarithm s) next.depth (edgeCount next.net) := by
    intro ha
    have ht:=(activeTest_correct _ _ _ _).mpr ha
    rw [hstop] at ht
    exact Bool.false_ne_true ht
  have hleaf:=SemiprimeD1LeafRate.inactive_leaf s (logarithm s) next.depth (edgeCount next.net)
    hready hi.2.1 hnot
  apply hhalf next.ctx next.net hshape.2.1 hshape.2.2
  · simpa only [SemiprimeD1BoundaryPlan.graph,SemiprimeD1NetworkStateResources.vertices_length] using hb.vertex_count
  · simpa only [SemiprimeD1BoundaryPlan.graph_edges_length] using hleaf
  · exact hb.axes_length.le.trans hb.depth
  · exact hb.axes
  · exact hb.rank
  · exact hb.precision
  · exact hb.degree

/-- Exhausting the actual original logarithmic fuel has the same checked-leaf
half exponent; the schedule itself implies the inactive guard. -/
theorem eventually_original_zero_fuel_half (e : Real) (he : 0<e) :
    ∀ᶠ ell : Nat in atTop, ∀ (N : Nat) (hN : 0<N), bitLength N=ell →
    ∀ (fixed : List (Fin (wireCount N) × Bool)) (next : Call),
    Reach (SemiprimeD1PublicPackingReady.scale ell) (originalCall N hN fixed) next →
    logarithm (SemiprimeD1PublicPackingReady.scale ell)+1≤next.depth+0 →
    ((SemiprimeD1BoundaryLeaf.checked next.ctx next.net).clock:Real)≤
      (2:Real)^((1/2+e)*((SemiprimeD1PublicPackingReady.scale ell:Real)/
        Real.sqrt (logarithm (SemiprimeD1PublicPackingReady.scale ell):Real))) := by
  filter_upwards [eventually_original_stopped_half e he] with ell hs
  intro N hN hEll fixed next hreach hf
  exact hs N hN hEll fixed next hreach
    (SemiprimeD1RecursiveLeafBounds.zero_fuel_inactive _ next.depth hf (edgeCount next.net))

end RiemannGaussian.SemiprimeD1BoundaryLeafOriginalReachRate
