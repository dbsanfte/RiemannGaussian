/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataBounds
/-! # Exact original guarded height, block count and binary-stage operands
This closes bounded metadata acquisition. Binary D/P are the NEXT stage and
are not claimed here. Original precision p is retained as its identical BINARY word.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataOriginal
open SemiprimeD1StackPhaseWorkingPrecisionMetadata SemiprimeD1StackPhaseWorkingPrecisionMetadataPrimitives
open SemiprimeD1StackPhaseWorkingPrecisionMetadataArithmetic SemiprimeD1StackPhaseWorkingPrecisionMetadataExecution
namespace Old
export SemiprimeD1StackPhaseGeometryGuardOriginal (originalGuard accepted_true order_original)
end Old
/-- Entire ACTUALLY acquired original geometry/guard cache survives the real arithmetic stage. -/
theorem guard_retained (a u M : Nat) (t p : List Bool) (j : G.Stack) :
    result a u M t p (guardStack j)=SemiprimeD1StackPhaseGeometryGuardComponents.result a u t j :=rfl
/-- Original M and arbitrary-precision ORIGINAL binary p are retained literally. -/
theorem originals_retained (a u M : Nat) (t p : List Bool) :
    result a u M t p (aux .edges)=D.unary M ∧ result a u M t p (aux .precision)=p :=⟨rfl,rfl⟩
/-- Exact original accepted height comes from the actual divider's quotient field. -/
theorem height_original_word (a u M : Nat) (t p : List Bool) (ht : SemiprimeBitArithmetic.bitValue t<2^(a+1))
    (h : Old.originalGuard a u t) :
    result a u M t p (divStack .quotient)=D.unary (SemiprimeD1ModeRate.jetHeight M u) :=by
  have hacc:accepted a u t=true:=(Old.accepted_true a u t ht).mpr h
  simp only [result,resultCounts,hacc,ite_true]
  rfl
/-- The physical coefficient-block counter is EXACT h*(u-i) for original acquired i. -/
theorem blocks_original_word (a u M : Nat) (t p : List Bool) (ht : SemiprimeBitArithmetic.bitValue t<2^(a+1))
    (h : Old.originalGuard a u t) :
    result a u M t p (aux .q)=D.unary (SemiprimeD1ModeRate.jetHeight M u*
      (u-(SemiprimeD1RecoveryScalarRun.orderFuel (SemiprimeD1RecoveryWeightRun.geometry a
        (SemiprimeBitArithmetic.bitValue t)).size (SemiprimeD1RecoveryWeightRun.geometry a
        (SemiprimeBitArithmetic.bitValue t)).point.natAbs).value)) :=by
  have hacc:accepted a u t=true:=(Old.accepted_true a u t ht).mpr h
  simp only [result,resultCounts,hacc,ite_true]
  change D.unary (height M u*(u-order a t))=_
  have ho:=Old.order_original a t ht
  change order a t=_ at ho
  rw [ho]
  rfl
/-- Bounded actual r=M*(a+1) is ready for paid BINARY conversion, without numeric2^a expansion. -/
theorem product_original_word (a u M : Nat) (t p : List Bool) (ht : SemiprimeBitArithmetic.bitValue t<2^(a+1))
    (h : Old.originalGuard a u t) :result a u M t p (aux .r)=D.unary (M*(a+1)) :=by
  have hacc:accepted a u t=true:=(Old.accepted_true a u t ht).mpr h
  simp only [result,resultCounts,hacc,ite_true]
  rfl
/-- Actual a-i shift counter derives from physical paired subtraction of acquired i. -/
theorem delta_original_word (a u M : Nat) (t p : List Bool) (ht : SemiprimeBitArithmetic.bitValue t<2^(a+1))
    (h : Old.originalGuard a u t) :
    result a u M t p (aux .delta)=D.unary (a-(SemiprimeD1RecoveryScalarRun.orderFuel
      (SemiprimeD1RecoveryWeightRun.geometry a (SemiprimeBitArithmetic.bitValue t)).size
      (SemiprimeD1RecoveryWeightRun.geometry a (SemiprimeBitArithmetic.bitValue t)).point.natAbs).value) :=by
  have hacc:accepted a u t=true:=(Old.accepted_true a u t ht).mpr h
  simp only [result,resultCounts,hacc,ite_true]
  change D.unary (a-order a t)=_
  have ho:=Old.order_original a t ht
  change order a t=_ at ho
  rw [ho]
/-- Rejected original phase leaves EVERY new height/product/difference output empty. -/
theorem rejected_outputs (a u M : Nat) (t p : List Bool) (ht : SemiprimeBitArithmetic.bitValue t<2^(a+1))
    (h : ¬Old.originalGuard a u t) :
    result a u M t p (divStack .quotient)=[] ∧ result a u M t p (aux .q)=[] ∧
    result a u M t p (aux .r)=[] ∧ result a u M t p (aux .delta)=[] :=by
  have hacc:accepted a u t=false:=Bool.eq_false_of_not_eq_true (by intro hh;exact h ((Old.accepted_true a u t ht).mp hh))
  simp only [result,resultCounts,hacc,Bool.false_eq_true,ite_false]
  exact ⟨rfl,rfl,rfl,rfl⟩
/-- All actual arithmetic/copy work is physically clear in BOTH accepted and rejected paths. -/
theorem work_clear (a u M : Nat) (t p : List Bool) :
    result a u M t p (divStack .input)=[] ∧ result a u M t p (divStack .divisor)=[] ∧
    result a u M t p (divStack .copied)=[] ∧ result a u M t p (divStack .scratch)=[] ∧
    result a u M t p (divStack .remainder)=[] ∧ result a u M t p (aux .multiplier)=[] ∧
    result a u M t p (aux .multiplicand)=[] ∧ result a u M t p (aux .productScratch)=[] ∧
    result a u M t p (aux .subtractWork)=[] ∧ result a u M t p (aux .copyScratch)=[] :=by
  unfold result resultCounts
  cases accepted a u t <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataOriginal
