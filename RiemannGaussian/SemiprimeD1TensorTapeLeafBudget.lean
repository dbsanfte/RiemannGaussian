/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorTapeLeaf
import RiemannGaussian.SemiprimeD1OriginalCallBounds

/-! # Original stopped-state bounds for the tape-backed eager leaf
Only numerical state/leaf-size facts are reused. The clock belongs to the new
executed tape backend; it is not identified with the older native-lookup clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1TensorTapeLeafBudget
open SemiprimeD1TensorTapeLeaf SemiprimeD1TensorNetwork SemiprimeD1JetAxes
open SemiprimeD1LeafCounterBounds SemiprimeD1NetworkStateResources
open SemiprimeD1RecursiveCallTree SemiprimeD1OriginalStateResources
open SemiprimeD1Schedule SemiprimeD1RecursiveCounter

/-- One fixed polynomial in actual enumeration, arithmetic and input-storage sizes. -/
def polynomial (M axes N p V L I : ℕ) : ℕ :=
  (9*p+3*N+8)+L*(3*M+4)+V*(8*(I+1)*I+4+
    SemiprimeD1JetRingBounds.mulBudget axes N p p+7)+
    (N*(3*p+4)+1)+(N*(6*N+11*p+9*p+17)+10*N+5)+13

/-- All dimension arguments are genuinely polynomial resources, including inventory. -/
theorem polynomial_mono {M axes N p V L I M' axes' N' p' V' L' I' : ℕ}
    (hM : M ≤ M') (ha : axes ≤ axes') (hN : N ≤ N') (hp : p ≤ p')
    (hV : V ≤ V') (hL : L ≤ L') (hI : I ≤ I') :
    polynomial M axes N p V L I ≤ polynomial M' axes' N' p' V' L' I' := by
  unfold polynomial SemiprimeD1JetRingBounds.mulBudget
    SemiprimeD1JetRingBounds.mulAtBudget SemiprimeD1JetRingBounds.termBudget
  gcongr

/-- The literal network's full port-list length is covered by its input inventory. -/
theorem scope_le_inventory (net : Network) : scopeSize (vertices net) ≤ inventory net := by
  have h : ∀xs : List SemiprimeD1LeafCounter.Vertex,
      scopeSize xs ≤ (xs.map (fun v => SemiprimeD1TensorTables.storage v.table+v.ports.length+1)).sum := by
    intro xs
    induction xs with
    | nil => simp [scopeSize]
    | cons v vs ih => simp only [scopeSize,List.map_cons,List.sum_cons] at *;omega
  have hs:=h (vertices net)
  unfold inventory
  omega

/-- Actual whole leaf report, with no externally supplied table or lookup budget. -/
theorem leaf_clock (ctx : Context) (net : Network) (hg : Good ctx net) :
    (SemiprimeD1TensorTapeLeaf.leaf ctx net).clock ≤
      polynomial (edgeCount net) ctx.axes.length ctx.rank ctx.precision
        (vertices net).length (scopeSize (vertices net)) (inventory net)*2^(edgeCount net) :=
  SemiprimeD1TensorTapeLeaf.leaf_clock ctx net hg

/-- Original resource cofactor fixed before choosing any reachable leaf. -/
def originalPolynomial (s : ℕ) : ℕ :=
  polynomial s (SemiprimeD1PackingReady.logarithm s+1) (rankCap s) (precisionCap s)
    (5*s) (inventoryCap s) (inventoryCap s)

/-- Actual reachable-state bounds give the entire new cofactor internally. -/
theorem bound_polynomial (s : ℕ) (call : Call) (hb : Bound s call) :
    polynomial (edgeCount call.net) call.ctx.axes.length call.ctx.rank call.ctx.precision
      (vertices call.net).length (scopeSize (vertices call.net)) (inventory call.net) ≤
        originalPolynomial s := by
  have ha : call.ctx.axes.length ≤ SemiprimeD1PackingReady.logarithm s+1 :=
    hb.axes_length.trans_le hb.depth
  have hv : (vertices call.net).length ≤ 5*s := by
    rw [vertices_length]
    exact hb.vertex_count
  exact polynomial_mono hb.edge_count ha hb.rank hb.precision hv
    ((scope_le_inventory call.net).trans hb.inventory) hb.inventory

/-- Every actual failed-guard original leaf executes the new tape backend at
2^leafSize times a fixed polynomial in inherited original state resources. -/
theorem eventually_original_stopped : ∀ᶠ ell : ℕ in Filter.atTop,
    ∀ (N : ℕ) (hN : 0<N), SemiprimeMacroParameters.bitLength N=ell →
      ∀ (fixed : List (Fin (SemiprimePublicAcquiredExecution.wireCount N)×Bool)) (call : Call),
      Reach (SemiprimeD1PublicPackingReady.scale ell) (originalCall N hN fixed) call →
      activeTest (SemiprimeD1PublicPackingReady.scale ell)
        (SemiprimeD1PackingReady.logarithm (SemiprimeD1PublicPackingReady.scale ell))
        call.depth (edgeCount call.net)=false →
      (SemiprimeD1TensorTapeLeaf.leaf call.ctx call.net).clock ≤
        originalPolynomial (SemiprimeD1PublicPackingReady.scale ell)*
          2^leafSize (SemiprimeD1PublicPackingReady.scale ell)
            (SemiprimeD1PackingReady.logarithm (SemiprimeD1PublicPackingReady.scale ell)) := by
  filter_upwards [SemiprimeD1OriginalStateResources.eventually_original,
    SemiprimeD1OriginalCallBounds.eventually_original_stopped_leaf] with ell hstate hsize
  intro N hN hEll fixed call hr hstop
  have hb:=hstate N hN hEll fixed call hr
  have hm:=(hsize N hN hEll fixed call hr hstop).1
  have hs:=original_shape N hN fixed
  have hg:=(SemiprimeD1RecursiveCallState.reach_shape _ _ _ hr hs.1 hs.2.1 hs.2.2.1).2.2
  exact (leaf_clock call.ctx call.net hg).trans
    (Nat.mul_le_mul (bound_polynomial _ call hb)
      (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hm))

/-- Actual original exhausted-fuel calls use the same executed tape leaf bound. -/
theorem eventually_original_zero : ∀ᶠ ell : ℕ in Filter.atTop,
    ∀ (N : ℕ) (hN : 0<N), SemiprimeMacroParameters.bitLength N=ell →
      ∀ (fixed : List (Fin (SemiprimePublicAcquiredExecution.wireCount N)×Bool)) (call : Call),
      Reach (SemiprimeD1PublicPackingReady.scale ell) (originalCall N hN fixed) call →
      SemiprimeD1PackingReady.logarithm (SemiprimeD1PublicPackingReady.scale ell)+1 ≤ call.depth+0 →
      (SemiprimeD1TensorTapeLeaf.leaf call.ctx call.net).clock ≤
        originalPolynomial (SemiprimeD1PublicPackingReady.scale ell)*
          2^leafSize (SemiprimeD1PublicPackingReady.scale ell)
            (SemiprimeD1PackingReady.logarithm (SemiprimeD1PublicPackingReady.scale ell)) := by
  filter_upwards [eventually_original_stopped] with ell hleaf
  intro N hN hEll fixed call hr hf
  exact hleaf N hN hEll fixed call hr
    (SemiprimeD1RecursiveLeafBounds.zero_fuel_inactive _ call.depth hf (edgeCount call.net))

end RiemannGaussian.SemiprimeD1TensorTapeLeafBudget
