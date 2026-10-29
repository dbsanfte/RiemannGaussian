/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseGeometryBounds
/-! # Exact original recovery geometry and finite-fuel dyadic order
The original exponent/index operands alone initialize the literal source.
Native geometry and orderFuel occur ONLY in these semantic proofs.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackPhaseGeometryOriginal
open SemiprimeD1StackPhaseGeometry SemiprimeD1StackPhaseGeometryArithmetic
open SemiprimeD1StackPhaseGeometryComponents SemiprimeD1StackPhaseGeometryExecution
open SemiprimeBitArithmetic
namespace G
export SemiprimeD1RecoveryWeightRun (geometry geometry_center geometry_size geometry_point geometry_alpha)
end G
/-- Both ORIGINAL physical operands are retained byte for byte. -/
theorem originals_retained (a t : List Bool) :
    result a t (aux .exponent)=a ∧ result a t (aux .index)=t :=⟨rfl,rfl⟩
/-- Every transient copied operand, subtraction scratch and scan word is physically empty. -/
theorem work_clear (a t : List Bool) :
    result a t (subStack .left)=[] ∧ result a t (subStack .right)=[] ∧
    result a t (subStack .scratch)=[] ∧ result a t (aux .counter)=[] ∧
    result a t (aux .scan)=[] ∧ result a t (aux .scratch)=[] :=⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
/-- Acquired binary center denotes the same original signed center. -/
theorem center_original (a t : List Bool) :
    (bitValue (result a t (aux .center)):Int)=(G.geometry a.length (bitValue t)).center :=by
  rw [G.geometry_center]
  change (bitValue (powerWord a.length):Int)=(2^a.length:Nat)
  rw [powerWord_value]
/-- The SAME binary alpha word denotes the exact original grid size. -/
theorem size_original (a t : List Bool) :
    bitValue (result a t (aux .alpha))=(G.geometry a.length (bitValue t)).size :=by
  rw [G.geometry_size]
  exact powerWord_value (a.length+1)
/-- Acquired binary alpha denotes the same original signed alpha. -/
theorem alpha_original (a t : List Bool) :
    (bitValue (result a t (aux .alpha)):Int)=(G.geometry a.length (bitValue t)).alpha :=by
  rw [G.geometry_alpha]
  change (bitValue (powerWord (a.length+1)):Int)=(2:Int)^(a.length+1)
  rw [powerWord_value,Nat.cast_pow]
  rfl
/-- Actual magnitude is the exact original signed point's absolute value for ALL t words. -/
theorem magnitude_original (a t : List Bool) :
    bitValue (result a t (subStack .output))=(G.geometry a.length (bitValue t)).point.natAbs :=by
  rw [G.geometry_point]
  exact magnitude_value a.length t
/-- The actual singleton sign comes from the exact original signed-point comparison. -/
theorem sign_original (a t : List Bool) :
    result a t (aux .sign)=[true] ↔ (G.geometry a.length (bitValue t)).point<0 :=by
  change [negative a.length t]=[true]↔_
  rw [List.singleton_inj,negative_true,G.geometry_point]
  change bitValue t<2^a.length↔(bitValue t:Int)-(2^a.length:Nat)<0
  omega
/-- The actual singleton zero flag tests the exact original point, including padded words. -/
theorem zero_original (a t : List Bool) :
    result a t (aux .zero)=[true] ↔ (G.geometry a.length (bitValue t)).point=0 :=by
  change [decide (bitValue (magnitude a.length t)=0)]=[true]↔_
  rw [List.singleton_inj,decide_eq_true_eq]
  have hm:=magnitude_original a t
  change bitValue (magnitude a.length t)=(G.geometry a.length (bitValue t)).point.natAbs at hm
  rw [hm,Int.natAbs_eq_zero]
/-- Actual bounded unary count is exactly the original dyadic valuation, including zero0. -/
theorem order_valuation (a t : List Bool) :
    result a t (aux .order)=List.replicate
      (padicValNat 2 (G.geometry a.length (bitValue t)).point.natAbs) true :=by
  change List.replicate (valuation (magnitude a.length t)) true=_
  rw [valuation_eq]
  have hm:=magnitude_original a t
  change bitValue (magnitude a.length t)=(G.geometry a.length (bitValue t)).point.natAbs at hm
  rw [hm]
/-- Entire ORIGINAL finite grid uses the exact old orderFuel value, without a supplied count. -/
theorem orderFuel_original (a t : List Bool)
    (ht : bitValue t<2^(a.length+1)) :
    result a t (aux .order)=List.replicate
      (SemiprimeD1RecoveryScalarRun.orderFuel (G.geometry a.length (bitValue t)).size
        (G.geometry a.length (bitValue t)).point.natAbs).value true :=by
  have hp:(G.geometry a.length (bitValue t)).point.natAbs≤(G.geometry a.length (bitValue t)).size:=by
    rw [G.geometry_point,G.geometry_size]
    exact (SemiprimeD1JetRecoveryScalarHeight.point_abs_lt a.length (bitValue t) ht).le
  have hv:padicValNat 2 (G.geometry a.length (bitValue t)).point.natAbs≤
      (G.geometry a.length (bitValue t)).size:=(Nat.padicValNat_le_self _).trans hp
  rw [SemiprimeD1RecoveryScalarRun.orderFuel_value _ _ (Or.inr hv)]
  exact order_valuation a t
/-- The physically counted order cannot exceed the ACTUAL paid absword byte length. -/
theorem order_bytes (a t : List Bool) :
    (result a t (aux .order)).length≤ max t.length (a.length+1) :=by
  change (List.replicate (valuation (magnitude a.length t)) true).length≤ _
  rw [List.length_replicate]
  exact (valuation_le _).trans (magnitude_length a.length t).le
/-- Entire actual source theorem and exact original geometry/orderFuel coincide. -/
theorem source_run_original (a t : List Bool) (ht : bitValue t<2^(a.length+1)) :
    ∃q≤1000*(a.length+t.length+1),∃finish,
      SemiprimeD1StackCalls.run program q (initial a t)=some finish ∧ finish=done a t ∧
      (bitValue (finish.data (aux .center)):Int)=(G.geometry a.length (bitValue t)).center ∧
      bitValue (finish.data (aux .alpha))=(G.geometry a.length (bitValue t)).size ∧
      bitValue (finish.data (subStack .output))=(G.geometry a.length (bitValue t)).point.natAbs ∧
      finish.data (aux .order)=List.replicate
        (SemiprimeD1RecoveryScalarRun.orderFuel (G.geometry a.length (bitValue t)).size
          (G.geometry a.length (bitValue t)).point.natAbs).value true :=by
  obtain ⟨q,hq,hr⟩:=source_run a t
  exact ⟨q,hq,done a t,hr,rfl,center_original a t,size_original a t,magnitude_original a t,orderFuel_original a t ht⟩
end RiemannGaussian.SemiprimeD1StackPhaseGeometryOriginal
