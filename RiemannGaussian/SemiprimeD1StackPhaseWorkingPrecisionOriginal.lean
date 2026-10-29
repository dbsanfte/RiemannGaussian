/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionBounds
/-! # Exact original BINARY workingPrecision and D on the actual whole source
Original a/u/M and BINARY t/p alone initialize the program. The acquired h/q,
order/guard/cache, BINARY D and BINARY precision are all retained literally.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionOriginal
open SemiprimeD1StackPhaseWorkingPrecision SemiprimeD1StackPhaseWorkingPrecisionArithmetic
open SemiprimeD1StackPhaseWorkingPrecisionComponents SemiprimeD1StackPhaseWorkingPrecisionExecution
open SemiprimeBitArithmetic
namespace Old
export SemiprimeD1StackPhaseGeometryGuardOriginal (originalGuard accepted_true order_original)
end Old
/-- Exact original acquired i from the original finite-fuel recovery loop. -/
def originalOrder (a : Nat) (t : List Bool) : Nat :=
  (SemiprimeD1RecoveryScalarRun.orderFuel (SemiprimeD1RecoveryWeightRun.geometry a (bitValue t)).size
    (SemiprimeD1RecoveryWeightRun.geometry a (bitValue t)).point.natAbs).value
/-- ENTIRE actual37-role metadata/geometry/guard bank survives EVERY binary operation. -/
theorem metadata_retained (a u edges : Nat) (t p : List Bool) (j : M.Stack) :
    result a u edges t p (metadataStack j)=old a u edges t p j :=rfl
/-- Original arbitrary-precision p is retained as the IDENTICAL BINARY input word. -/
theorem original_precision_retained (a u edges : Nat) (t p : List Bool) :
    result a u edges t p (metadataStack (M.aux .precision))=p :=rfl
/-- Exact physical branch agrees with the original whole phase's conjunction. -/
theorem accepted_original (a u : Nat) (t : List Bool) (ht : bitValue t<2^(a+1)) :
    accepted a u t=true ↔ Old.originalGuard a u t :=Old.accepted_true a u t ht
/-- Exact acquired i agrees with original orderFuel on EVERY original grid word. -/
theorem order_original (a : Nat) (t : List Bool) (ht : bitValue t<2^(a+1)) :
    order a t=originalOrder a t :=Old.order_original a t ht
/-- Exact BINARY D=2^(a-i), with NO numeric power-to-unary conversion. -/
theorem power_original (a u edges : Nat) (t p : List Bool) (ht : bitValue t<2^(a+1))
    (h : Old.originalGuard a u t) :
    bitValue (result a u edges t p (aux .power))=2^(a-originalOrder a t) :=by
  have hacc:accepted a u t=true:=(accepted_original a u t ht).mpr h
  simp only [result,hacc,ite_true]
  change bitValue (shift (delta a t) [true])=_
  have ho:=order_original a t ht
  have hd:delta a t=a-originalOrder a t:=by unfold delta;rw [ho]
  calc
    _=2^(delta a t)*1:=shift_value (delta a t) [true]
    _=2^(delta a t):=Nat.mul_one _
    _=_:=by rw [hd]
/-- Exact original workingPrecision from the WHOLE real binary shift/add source.
P and original p NEVER become unary numerical precision counters. -/
theorem precision_original (a u edges : Nat) (t p : List Bool) (ht : bitValue t<2^(a+1))
    (h : Old.originalGuard a u t) :
    bitValue (result a u edges t p (aux .output))=
      SemiprimeD1ModeRate.workingPrecision edges u a (originalOrder a t) (bitValue p) :=by
  have hacc:accepted a u t=true:=(accepted_original a u t ht).mpr h
  simp only [result,hacc,ite_true]
  change bitValue (precisionWord (height edges u) (product a edges) (delta a t) p)=_
  rw [precisionWord_value]
  have ho:=order_original a t ht
  change bitValue p+8*SemiprimeD1ModeRate.jetHeight edges u*2^(a-order a t)+8*(edges*(a+1))=
    bitValue p+8*SemiprimeD1ModeRate.jetHeight edges u*2^(a-originalOrder a t)+8*edges*(a+1)
  rw [ho,Nat.mul_assoc 8 edges (a+1)]
/-- Exact original acquired height remains physically present after the binary P source. -/
theorem height_retained (a u edges : Nat) (t p : List Bool) (ht : bitValue t<2^(a+1))
    (h : Old.originalGuard a u t) :
    result a u edges t p (metadataStack (M.divStack .quotient))=
      List.replicate (SemiprimeD1ModeRate.jetHeight edges u) true :=
  SemiprimeD1StackPhaseWorkingPrecisionMetadataOriginal.height_original_word a u edges t p ht h
/-- Exact original q=h*(u-i) remains physically present with the BINARY P/D outputs. -/
theorem blocks_retained (a u edges : Nat) (t p : List Bool) (ht : bitValue t<2^(a+1))
    (h : Old.originalGuard a u t) :
    result a u edges t p (metadataStack (M.aux .q))=
      List.replicate (SemiprimeD1ModeRate.jetHeight edges u*(u-originalOrder a t)) true :=
  SemiprimeD1StackPhaseWorkingPrecisionMetadataOriginal.blocks_original_word a u edges t p ht h
/-- Original rejected phase leaves NEW binary P/D empty, without any conversion/adder stage. -/
theorem rejected_outputs (a u edges : Nat) (t p : List Bool) (ht : bitValue t<2^(a+1))
    (h : ¬Old.originalGuard a u t) :
    result a u edges t p (aux .output)=[] ∧ result a u edges t p (aux .power)=[] :=by
  have hacc:accepted a u t=false:=Bool.eq_false_of_not_eq_true (by intro hh;exact h ((accepted_original a u t ht).mp hh))
  simp only [result,hacc,Bool.false_eq_true,ite_false]
  exact ⟨rfl,rfl⟩
/-- Every binary accumulator, counter, copy, allocation and shift work word is physically clear. -/
theorem binary_work_clear (a u edges : Nat) (t p : List Bool) :
    result a u edges t p (aux .left)=[] ∧ result a u edges t p (aux .right)=[] ∧
    result a u edges t p (aux .scratch)=[] ∧ result a u edges t p (aux .counter)=[] ∧
    result a u edges t p (aux .next)=[] ∧ result a u edges t p (aux .todo)=[] ∧
    result a u edges t p (aux .zeroTodo)=[] ∧ result a u edges t p (aux .shiftTodo)=[] ∧
    result a u edges t p (aux .copyScratch)=[] :=⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
/-- SAME actual whole source and exact original P/D/h/q hold together for ALL original active nodes. -/
theorem source_run_original (a u edges : Nat) (t p : List Bool) (ht : bitValue t<2^(a+1))
    (h : Old.originalGuard a u t) :
    ∃q≤1000000000000*(edges+a+u+t.length+p.length+1)^4,
      SemiprimeD1StackCalls.run program q (initial a u edges t p)=some (done a u edges t p) ∧
      bitValue ((done a u edges t p).data (aux .output))=
        SemiprimeD1ModeRate.workingPrecision edges u a (originalOrder a t) (bitValue p) ∧
      bitValue ((done a u edges t p).data (aux .power))=2^(a-originalOrder a t) ∧
      (done a u edges t p).data (metadataStack (M.divStack .quotient))=
        List.replicate (SemiprimeD1ModeRate.jetHeight edges u) true ∧
      (done a u edges t p).data (metadataStack (M.aux .q))=
        List.replicate (SemiprimeD1ModeRate.jetHeight edges u*(u-originalOrder a t)) true :=by
  obtain ⟨q,hq,hr⟩:=source_run a u edges t p
  exact ⟨q,hq,hr,precision_original a u edges t p ht h,power_original a u edges t p ht h,
    height_retained a u edges t p ht h,blocks_retained a u edges t p ht h⟩
/-- SAME whole source also closes every original rejected phase with EMPTY new outputs. -/
theorem source_run_rejected (a u edges : Nat) (t p : List Bool) (ht : bitValue t<2^(a+1))
    (h : ¬Old.originalGuard a u t) :
    ∃q≤1000000000000*(edges+a+u+t.length+p.length+1)^4,
      SemiprimeD1StackCalls.run program q (initial a u edges t p)=some (done a u edges t p) ∧
      (done a u edges t p).data (aux .output)=[] ∧ (done a u edges t p).data (aux .power)=[] :=by
  obtain ⟨q,hq,hr⟩:=source_run a u edges t p
  exact ⟨q,hq,hr,(rejected_outputs a u edges t p ht h).1,(rejected_outputs a u edges t p ht h).2⟩
end RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionOriginal
