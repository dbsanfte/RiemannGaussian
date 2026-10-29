/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseGeometryGuardBounds
/-! # Same original WordTapeRecursivePhase.phase conjunction on the whole grid
Its i is the actual acquired orderFuel value; no separate caller order exists.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
namespace RiemannGaussian.SemiprimeD1StackPhaseGeometryGuardOriginal
open SemiprimeD1StackPhaseGeometryGuard SemiprimeD1StackPhaseGeometryGuardPrimitives
open SemiprimeD1StackPhaseGeometryGuardComponents SemiprimeD1StackPhaseGeometryGuardExecution
open SemiprimeBitArithmetic
namespace Old
export SemiprimeD1StackPhaseGeometryOriginal (orderFuel_original zero_original)
end Old
/-- The EXACT native conjunction occurring in original WordTapeRecursivePhase.phase. -/
def originalGuard (a u : Nat) (t : List Bool) : Prop :=
  let geometry:=SemiprimeD1RecoveryWeightRun.geometry a (bitValue t)
  let i:=(SemiprimeD1RecoveryScalarRun.orderFuel geometry.size geometry.point.natAbs).value
  i<a ∧ i<u ∧ geometry.point≠0
instance (a u : Nat) (t : List Bool) : Decidable (originalGuard a u t) :=inferInstanceAs (Decidable (_∧_∧_))
/-- ALL14 acquired geometry fields survive every comparison and the final halt literally. -/
theorem geometry_retained (a u : Nat) (t : List Bool) (j : G.Stack) :
    result a u t (geometryStack j)=cache a t j :=rfl
/-- Caller u remains the identical physical unary bounded-metadata operand. -/
theorem levels_retained (a u : Nat) (t : List Bool) :
    result a u t (aux .levels)=List.replicate u true :=rfl
/-- Every guard comparison/copy scratch role is physically empty at the actual halt. -/
theorem work_clear (a u : Nat) (t : List Bool) :
    result a u t (aux .left)=[] ∧ result a u t (aux .right)=[] ∧
    result a u t (aux .limit)=[] ∧ result a u t (aux .valid)=[] ∧ result a u t (aux .scratch)=[] :=⟨rfl,rfl,rfl,rfl,rfl⟩
/-- The physical order used in BOTH comparisons is the original grid's orderFuel value. -/
theorem order_original (a : Nat) (t : List Bool) (ht : bitValue t<2^(a+1)) :
    order a t=(SemiprimeD1RecoveryScalarRun.orderFuel (SemiprimeD1RecoveryWeightRun.geometry a (bitValue t)).size
      (SemiprimeD1RecoveryWeightRun.geometry a (bitValue t)).point.natAbs).value :=by
  have h:=congrArg List.length (Old.orderFuel_original (List.replicate a true) t
    (by simpa only [List.length_replicate] using ht))
  change (cache a t (G.aux .order)).length=_ at h
  rw [cache_order,List.length_replicate] at h
  simpa only [List.length_replicate] using h
/-- The retained actual zero flag tests the exact original signed point. -/
theorem zero_original (a : Nat) (t : List Bool) :
    zero a t=true ↔ (SemiprimeD1RecoveryWeightRun.geometry a (bitValue t)).point=0 :=by
  have h:=Old.zero_original (List.replicate a true) t
  change cache a t (G.aux .zero)=[true]↔_ at h
  rw [cache_zero,List.singleton_inj] at h
  simpa only [List.length_replicate] using h
/-- Full actual source's true branch is EXACTLY the original guard, for ALL original nodes. -/
theorem accepted_true (a u : Nat) (t : List Bool) (ht : bitValue t<2^(a+1)) :
    accepted a u t=true ↔ originalGuard a u t :=by
  unfold originalGuard
  dsimp only
  rw [←order_original a t ht]
  cases hz:zero a t with
  | true=>
    have hp:=(zero_original a t).mp hz
    simp only [accepted,hz,ite_true]
    constructor
    · intro h;cases h
    · intro h;exact (h.2.2 hp).elim
  | false=>
    have hp:(SemiprimeD1RecoveryWeightRun.geometry a (bitValue t)).point≠0:=by
      intro h
      have hh:=(zero_original a t).mpr h
      rw [hz] at hh
      cases hh
    simp only [accepted,hz,Bool.false_eq_true,ite_false]
    by_cases ha:order a t<a
    · simp only [ha,ite_true,decide_eq_true_eq]
      exact ⟨fun h=>⟨True.intro,h,hp⟩,fun h=>h.2.1⟩
    · simp only [ha,ite_false]
      constructor
      · intro h;cases h
      · intro h;exact h.1.elim
/-- Exact SINGLETON Boolean verdict, including both rejected and retained original nodes. -/
theorem verdict_original (a u : Nat) (t : List Bool) (ht : bitValue t<2^(a+1)) :
    result a u t (aux .output)=[decide (originalGuard a u t)] :=by
  change [accepted a u t]=_
  apply congrArg (fun b:Bool=>[b])
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  exact accepted_true a u t ht
/-- Whole source from ONLY original a/u/t has exactly the original retained-node branch. -/
theorem source_run_original (a u : Nat) (t : List Bool) (ht : bitValue t<2^(a+1)) :
    ∃q≤10000*(a+u+t.length+1),∃finish,
      SemiprimeD1StackCalls.run program q (initial a u t)=some finish ∧ finish=done a u t ∧
      finish.data (aux .output)=[decide (originalGuard a u t)] ∧
      finish.data (aux .levels)=List.replicate u true ∧
      ∀j:G.Stack,finish.data (geometryStack j)=cache a t j :=by
  obtain ⟨q,hq,hr⟩:=source_run a u t
  exact ⟨q,hq,done a u t,hr,rfl,verdict_original a u t ht,levels_retained a u t,geometry_retained a u t⟩
end RiemannGaussian.SemiprimeD1StackPhaseGeometryGuardOriginal
