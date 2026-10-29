/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecursivePhaseBounds
import RiemannGaussian.SemiprimeD1HermiteNodes

/-! # The actual phase test covers every original retained Hermite node
The finite valuation loop is justified from the original signed grid itself.
Thus all original retained nodes, precisions and coefficient-block counts are
properties of the executed controller, not advice supplied to recovery.
-/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace RiemannGaussian.SemiprimeD1RecursivePhaseControl
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1WireKernelOriginal SemiprimeD1RecoveryWeightRun
open SemiprimeD1RecoveryScalarRun SemiprimeD1HermiteNodes SemiprimeD1JetRecoveryGrid
open SemiprimeD1TaperedLoss SemiprimeD1ModeRate
open SemiprimeD1JetAffineCoefficient (JetRun)

/-- The literal bounded modulo/division loop computes the original signed
node valuation. Original grid magnitude pays its fuel. -/
theorem order_value (a : ℕ) (t : Fin (size a)) :
    (orderFuel (geometry a t.val).size (geometry a t.val).point.natAbs).value =
      padicValInt 2 (point a t.val) := by
  rw [geometry_size,geometry_point]
  exact orderFuel_value _ _ (Or.inr
    ((Nat.padicValNat_le_self _).trans
      (SemiprimeD1JetRecoveryScalarHeight.point_abs_lt a t.val t.isLt).le))

/-- Original retained-node membership derives the controller's full actual
branch test. In particular the omitted centre cannot reach a child call. -/
theorem active_guard (net : Network) (a u : ℕ) (t : Fin (size a))
    (hua : u ≤ a) (ht : t.val ∈ active a (height (edgeCount net) u) u) :
    let i := (orderFuel (geometry a t.val).size (geometry a t.val).point.natAbs).value
    i < a ∧ i < u ∧ (geometry a t.val).point ≠ 0 := by
  dsimp only
  rw [order_value,geometry_point]
  have hq := active_positive a (height (edgeCount net) u) u t.val ht
  have hi : padicValInt 2 (point a t.val) < u := by
    unfold nodeMultiplicity SemiprimeD1TaperedLoss.multiplicity at hq
    exact Nat.sub_pos_iff_lt.mp (Nat.pos_of_mul_pos_left hq)
  exact ⟨hi.trans_le hua,hi,fun hz =>
    (Finset.mem_filter.mp ht).2.1 ((point_zero_iff a t.val).mp hz)⟩

/-- Every active recursive schedule produces an exponent large enough for
ALL retained valuation levels. No asymptotic readiness premise is needed. -/
theorem schedule_levels_le_exponent (lam depth : ℕ) :
    SemiprimeD1Schedule.levels lam depth ≤ SemiprimeD1Schedule.exponent lam depth := by
  unfold SemiprimeD1Schedule.exponent
  omega

/-- At every actual retained point, source precision agrees exactly with
the original recovery theorem's D.11 expression. -/
theorem active_precision (next : Context → Network → JetRun) (ctx : Context)
    (net : Network) (a u : ℕ) (t : Fin (size a)) (hua : u ≤ a)
    (ht : t.val ∈ active a (height (edgeCount net) u) u) :
    (phase next ctx net a u t).precision =
      SemiprimeD1WeightPrecision.precision a (edgeCount net) u ctx.precision t.val := by
  have hg := active_guard net a u t hua ht
  dsimp only at hg
  dsimp only [phase]
  rw [dite_eq_left hg]
  dsimp only
  rw [SemiprimeD1RecursivePhaseBounds.source_precision,order_value]
  rfl

/-- The actual phase stores exactly every coefficient required at that
retained Hermite node, in the original ascending order. -/
theorem active_blocks_size (next : Context → Network → JetRun) (ctx : Context)
    (net : Network) (a u : ℕ) (t : Fin (size a)) (hua : u ≤ a)
    (ht : t.val ∈ active a (height (edgeCount net) u) u) :
    (phase next ctx net a u t).blocks.size =
      nodeMultiplicity a (height (edgeCount net) u) u t.val := by
  have hg := active_guard net a u t hua ht
  dsimp only at hg
  dsimp only [phase]
  rw [dite_eq_left hg]
  simp only [List.size_toArray,List.length_map,List.length_range,order_value]
  rfl

/-- All actual fresh contexts on retained nodes have positive axes, derived
from the parent axes and the actual original multiplicity. -/
theorem active_context_positive (ctx : Context) (net : Network) (a u : ℕ)
    (t : Fin (size a)) (hpos : ctx.Positive)
    (ht : t.val ∈ active a (height (edgeCount net) u) u) :
    (⟨(jetHeight (edgeCount net) u *
      (u-(orderFuel (geometry a t.val).size (geometry a t.val).point.natAbs).value))::ctx.axes,
        workingPrecision (edgeCount net) u a
          (orderFuel (geometry a t.val).size (geometry a t.val).point.natAbs).value ctx.precision⟩ : Context).Positive := by
  rw [order_value]
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact active_positive a (height (edgeCount net) u) u t.val ht
  · exact hpos q hq

end RiemannGaussian.SemiprimeD1RecursivePhaseControl
