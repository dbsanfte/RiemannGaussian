/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OriginalStateResources
import RiemannGaussian.SemiprimeD1RecursiveTreeRate
import RiemannGaussian.SemiprimeD1RecursiveLeafBounds

/-! # Closed original-input call and leaf report bounds
All root dimensions, degrees, shapes, inherited precisions and leaf sizes are
derived from the actual acquired original-N network. These family statements
have no root-state, child-count or stopped-leaf-size supplier. Full local active
work and primitive-machine lowering remain separate costs.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1OriginalCallBounds
open SemiprimeD1RecursiveCallTree SemiprimeD1OriginalStateResources
open SemiprimeD1RootStateResources SemiprimeD1TensorNetwork
open SemiprimeD1RecursiveLeafBounds SemiprimeD1Schedule
open SemiprimeD1RecursiveCounter
open SemiprimePublicAcquiredExecution SemiprimeMacroParameters

/-- One explicit original-resource cofactor, before choosing any reachable call. -/
def leafCofactorCap (s : ℕ) : ℕ :=
  SemiprimeD1PackingReady.logarithm s+1+rankCap s+precisionCap s+s+
    (s+1)*(5*s+1)+1

/-- Actual state invariants bound the complete eager leaf cofactor. -/
theorem cofactor_le (s : ℕ) (call : Call) (hb : Bound s call) :
    cofactorSize call.ctx call.net ≤ leafCofactorCap s := by
  have ha : call.ctx.axes.length ≤ SemiprimeD1PackingReady.logarithm s+1 :=
    hb.axes_length.trans_le hb.depth
  have hv : (vertices call.net).length ≤ 5*s := by
    rw [SemiprimeD1NetworkStateResources.vertices_length]
    exact hb.vertex_count
  unfold cofactorSize leafCofactorCap
  gcongr
  all_goals first | exact ha | exact hb.rank | exact hb.precision | exact hb.edge_count

/-- The actual all-input root caller inherits the complete finite-fuel call
bound without any supplied branching, degree, precision or packing answers. -/
theorem eventually_original_count : ∀ᶠ ell : ℕ in Filter.atTop,
    ∀ (N : ℕ) (hN : 0 < N), bitLength N=ell →
      ∀ (fixed : List (Fin (wireCount N) × Bool)) (fuel : ℕ),
        (count (SemiprimeD1PublicPackingReady.scale ell) fuel (originalCall N hN fixed):ℝ) ≤
          (SemiprimeD1PackingReady.logarithm (SemiprimeD1PublicPackingReady.scale ell)+2:ℕ)*
            Real.exp (98304*(SemiprimeD1PublicPackingReady.scale ell:ℝ)/
              Real.sqrt (SemiprimeD1PackingReady.logarithm (SemiprimeD1PublicPackingReady.scale ell):ℕ)+
              (((4*SemiprimeD1PackingReady.logarithm (SemiprimeD1PublicPackingReady.scale ell)+7)*
                (SemiprimeD1PackingReady.logarithm (SemiprimeD1PublicPackingReady.scale ell)+1):ℕ):ℝ)) := by
  filter_upwards [scale_tendsto.eventually SemiprimeD1RecursiveTreeRate.eventually_count_le] with ell hcount
  intro N hN hEll fixed fuel
  subst ell
  have hs := original_shape N hN fixed
  exact hcount (originalCall N hN fixed) fuel rfl (root_edges_le_scale N hN fixed)
    hs.2.2.2 hs.1 hs.2.1 hs.2.2.1 (root_global_degree N hN fixed)

/-- Uniform original-input family bound for every actual failed-guard leaf,
including its complete eager coefficient-table evaluation and accumulation. -/
theorem eventually_original_stopped_leaf : ∀ᶠ ell : ℕ in Filter.atTop,
    ∀ (N : ℕ) (hN : 0 < N), bitLength N=ell →
      ∀ (fixed : List (Fin (wireCount N) × Bool)) (call : Call),
        Reach (SemiprimeD1PublicPackingReady.scale ell) (originalCall N hN fixed) call →
        activeTest (SemiprimeD1PublicPackingReady.scale ell)
          (SemiprimeD1PackingReady.logarithm (SemiprimeD1PublicPackingReady.scale ell))
          call.depth (edgeCount call.net)=false →
        edgeCount call.net ≤ leafSize (SemiprimeD1PublicPackingReady.scale ell)
          (SemiprimeD1PackingReady.logarithm (SemiprimeD1PublicPackingReady.scale ell)) ∧
        (leaf call.ctx call.net).clock ≤
          100000*(leafCofactorCap (SemiprimeD1PublicPackingReady.scale ell)+1)^8*
            2^leafSize (SemiprimeD1PublicPackingReady.scale ell)
              (SemiprimeD1PackingReady.logarithm (SemiprimeD1PublicPackingReady.scale ell)) := by
  filter_upwards [eventually_original,
    scale_tendsto.eventually SemiprimeD1RecursiveCallPath.eventually_reach_invariant,
    scale_tendsto.eventually SemiprimeD1LeafReady.eventually_rootReady] with ell hstate hpath hready
  intro N hN hEll fixed call hreach hstop
  have hb := hstate N hN hEll fixed call hreach
  subst ell
  have hs := original_shape N hN fixed
  have hi := hpath (originalCall N hN fixed) call rfl (root_edges_le_scale N hN fixed)
    hs.2.2.2 hs.1 hs.2.1 hs.2.2.1 (root_global_degree N hN fixed) hreach
  have hshape := SemiprimeD1RecursiveCallState.reach_shape _ _ _ hreach hs.1 hs.2.1 hs.2.2.1
  refine ⟨stopped_edges _ call hready hi.2.1 hstop,?_⟩
  exact (stopped_leaf_clock _ call hready hi.2.1 hstop hshape.2.1 hshape.2.2).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (Nat.add_le_add_right (cofactor_le _ call hb) 1) 8)))

/-- Every actual fuel-zero call reached with the original remaining-fuel
invariant also has the same closed original-input leaf bound. -/
theorem eventually_original_zero_leaf : ∀ᶠ ell : ℕ in Filter.atTop,
    ∀ (N : ℕ) (hN : 0 < N), bitLength N=ell →
      ∀ (fixed : List (Fin (wireCount N) × Bool)) (call : Call),
        Reach (SemiprimeD1PublicPackingReady.scale ell) (originalCall N hN fixed) call →
        SemiprimeD1PackingReady.logarithm (SemiprimeD1PublicPackingReady.scale ell)+1 ≤ call.depth+0 →
        (leaf call.ctx call.net).clock ≤
          100000*(leafCofactorCap (SemiprimeD1PublicPackingReady.scale ell)+1)^8*
            2^leafSize (SemiprimeD1PublicPackingReady.scale ell)
              (SemiprimeD1PackingReady.logarithm (SemiprimeD1PublicPackingReady.scale ell)) := by
  filter_upwards [eventually_original_stopped_leaf] with ell hleaf
  intro N hN hEll fixed call hreach hf
  exact (hleaf N hN hEll fixed call hreach
    (zero_fuel_inactive _ call.depth hf (edgeCount call.net))).2

end RiemannGaussian.SemiprimeD1OriginalCallBounds
