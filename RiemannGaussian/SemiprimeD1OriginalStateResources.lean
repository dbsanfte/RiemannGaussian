/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootStateResources
import RiemannGaussian.SemiprimeD1RecursiveStateResources

/-! # Original binary-input envelopes for EVERY actual recursive state
The root and every reachable child are literal acquired networks. Root size,
degree, shape and inherited precision are derived, never supplied as answers.
The conclusion bounds stored network data, not all auxiliary heap/tape states.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1OriginalStateResources
open SemiprimeD1RecursiveCallTree SemiprimeD1RecursiveCallState
open SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkRecursion
open SemiprimeD1NetworkStateResources SemiprimeD1Schedule
open SemiprimeD1JetAxes SemiprimeMacroParameters SemiprimePublicAcquiredExecution
open SemiprimeD1RootStateResources

/-- Exactly the root call passed to the original binary-input prefix controller. -/
def originalCall (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) : Call :=
  ⟨0,SemiprimeD1RootOwnerTables.rootContext,root N hN fixed⟩

/-- Uniform dense-rank envelope for the ACTUAL original-scale schedule. -/
def rankCap (s : ℕ) : ℕ := (4*s)^(SemiprimeD1PackingReady.logarithm s+1)

/-- Uniform scalar word-width envelope, including terminal children. -/
def precisionCap (s : ℕ) : ℕ :=
  s*(201*(SemiprimeD1PackingReady.logarithm s+1)^2)*2^(4*SemiprimeD1PackingReady.logarithm s)

/-- Literal full-network inventory envelope; the table exponential is2^delta,
not2^s, and rank retains every acquired axis. -/
def inventoryCap (s : ℕ) : ℕ :=
  5*s*((rankCap s*(3*precisionCap s+4)+3)*2^(SemiprimeD1PackingReady.degreeCap s)+
    SemiprimeD1PackingReady.degreeCap s)+s+5*s+1

/-- Output data invariants of an actual reachable call, all from original input. -/
structure Bound (s : ℕ) (call : Call) : Prop where
  /-- Both literal vertex families, including isolated old vertices. -/
  vertex_count : vertexCount call.net  ≤  5*s
  /-- Actual real occurrence count. -/
  edge_count : edgeCount call.net  ≤  s
  /-- Every stored original or packet table has the single global scope cap. -/
  degree : DegreeBound call.net (SemiprimeD1PackingReady.degreeCap s)
  /-- Real recursive depth, including last generated leaves. -/
  depth : call.depth  ≤  SemiprimeD1PackingReady.logarithm s+1
  /-- All old coordinates are retained, one new axis per generation. -/
  axes_length : call.ctx.axes.length=call.depth
  /-- Actual fresh dimensions are bounded by4s. -/
  axes : ∀q∈call.ctx.axes,q ≤ 4*s
  /-- Actual dense coordinate rank. -/
  rank : call.ctx.rank  ≤  rankCap s
  /-- Computed scalar precision, including all earlier phase increments. -/
  precision : call.ctx.precision  ≤  precisionCap s
  /-- All literal table payload, branch tags, port and row cells. -/
  inventory : SemiprimeD1NetworkStateResources.inventory call.net  ≤  inventoryCap s

/-- Original fixed scale tends to infinity with actual binary input length. -/
theorem scale_tendsto : Filter.Tendsto SemiprimeD1PublicPackingReady.scale Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.mpr (fun b=>?_)
  filter_upwards [Filter.eventually_ge_atTop b] with ell hb
  unfold SemiprimeD1PublicPackingReady.scale
  norm_num
  omega

/-- The root supplies all inherited shape/precision conditions from N itself. -/
theorem original_shape (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    (originalCall N hN fixed).ctx.Positive ∧
    WellFormed (originalCall N hN fixed).net ∧
    Good (originalCall N hN fixed).ctx (originalCall N hN fixed).net ∧
    (originalCall N hN fixed).ctx.precision ≤ SemiprimeD1PublicPackingReady.scale (bitLength N) := by
  refine ⟨?_,SemiprimeD1RootNetwork.acquirePositive_wellFormed N hN fixed,
    SemiprimeD1RootNetwork.acquirePositive_good N hN fixed,?_⟩
  · intro q hq
    simp only [originalCall,SemiprimeD1RootOwnerTables.rootContext,List.not_mem_nil] at hq
  · change 2 ≤ SemiprimeD1PublicPackingReady.scale (bitLength N)
    have hp:=bitLength_pos hN
    unfold SemiprimeD1PublicPackingReady.scale
    norm_num
    omega

/-- CLOSED original-N family endpoint: every actual recursive state has the
uniform envelope. No root/child sizes, precision sequence, table height, degree,
packet count or native count is supplied as an input premise. -/
theorem eventually_original : ∀ᶠ ell : ℕ in Filter.atTop,
    ∀ (N : ℕ) (hN : 0<N), bitLength N=ell →
      ∀ (fixed : List (Fin (wireCount N)×Bool)) (next : Call),
      Reach (SemiprimeD1PublicPackingReady.scale ell) (originalCall N hN fixed) next →
      Bound (SemiprimeD1PublicPackingReady.scale ell) next := by
  filter_upwards [scale_tendsto.eventually SemiprimeD1RecursiveStateResources.eventually_reach_resources,
    scale_tendsto.eventually SemiprimeD1RecursiveCallPath.eventually_reach_invariant] with ell hresources hinvariant
  intro N hN hEll fixed next hr
  subst ell
  let s:=SemiprimeD1PublicPackingReady.scale (bitLength N)
  have hshape:=original_shape N hN fixed
  have hM:=root_edges_le_scale N hN fixed
  have hd:=root_global_degree N hN fixed
  have hb:=hresources (originalCall N hN fixed) next rfl rfl hM hshape.2.2.2
    hshape.1 hshape.2.1 hshape.2.2.1 hd hr
  have hi:=hinvariant (originalCall N hN fixed) next rfl hM hshape.2.2.2
    hshape.1 hshape.2.1 hshape.2.2.1 hd hr
  have hcount:=root_vertices_le_edges N hN fixed
  have hNF : vertexCount next.net ≤ 5*s := by
    have hpotential:=hb.1
    change vertexCount next.net+4*edgeCount next.net ≤ vertexCount (root N hN fixed)+4*edgeCount (root N hN fixed) at hpotential
    omega
  have hEdge:=SemiprimeD1RecursiveCallPath.edges_le_of_scaled s next hi.2.1
  have hprev : previous (SemiprimeD1PackingReady.logarithm s) next.depth ≤ 4*SemiprimeD1PackingReady.logarithm s := by
    have he:=exponent_le_lam (SemiprimeD1PackingReady.logarithm s) next.depth
    unfold exponent at he
    omega
  have hP : next.ctx.precision ≤ precisionCap s := by
    exact hb.2.2.2.2.2.trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hprev))
  have hGood:=(reach_shape s (originalCall N hN fixed) next hr hshape.1 hshape.2.1 hshape.2.2.1).2.2
  have hInv:=inventory_bound next.ctx next.net (SemiprimeD1PackingReady.degreeCap s) hGood hi.1
  have hRows : next.net.rows.length ≤ 5*s := by unfold vertexCount at hNF;omega
  refine ⟨hNF,hEdge,hi.1,hb.2.1,hb.2.2.1,hb.2.2.2.1,hb.2.2.2.2.1,hP,?_⟩
  have hR : next.ctx.rank ≤ rankCap s:=hb.2.2.2.2.1
  exact hInv.trans (by
    unfold inventoryCap
    gcongr)

end RiemannGaussian.SemiprimeD1OriginalStateResources
