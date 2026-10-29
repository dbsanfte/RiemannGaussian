/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootScaleLeafDoubling
import RiemannGaussian.SemiprimeD1StackRootScaleLeafDivision
/-! # Real acquired-width scaling and exact square-root/leaf composition -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
namespace RiemannGaussian.SemiprimeD1StackRootScaleLeafComponents
open SemiprimeD1StackRootScaleLeaf SemiprimeD1StackRootScaleLeafPrimitives
open SemiprimeD1StackRootScaleLeafArithmetic SemiprimeD1StackProcedureTrace
/-- ONLY the actual acquired old cache and ten physically empty fresh roles. -/
def base (bits : List Bool) : Stack→List Bool :=(ready bits).data
/-- Reached actual materialized scale, retaining the ENTIRE old cache. -/
def scaled (bits : List Bool) : Stack→List Bool :=
  store (SemiprimeD1StackRootScheduleExecution.result bits) (D.contents [] [] [] [] [] [])
    (metadata (D.unary (scale bits.length)) [] [] [])
/-- Every one of twenty physical doublings starts with the ACTUALLY acquired width;
no prepared scale or width is supplied to this ready entry. -/
theorem acquire_scale (bits : List Bool) :
    Runs program (5*bits.length+4+SemiprimeD1StackRootScaleLeafDoubling.runTime bits.length 20)
      .ready (base bits) (.double 20) (scaled bits) :=by
  have h0:=copy_call 0 .ready (.double 0) rfl (base bits) rfl
  have hl:(base bits (copySource 0)).length=bits.length:=by
    change (List.replicate bits.length true).length=bits.length
    simp only [List.length_replicate]
  rw [hl] at h0
  have he0:Function.update (base bits) (copyTarget 0) (base bits (copySource 0)++base bits (copyTarget 0))=
      SemiprimeD1StackRootScaleLeafDoubling.data (base bits) bits.length 0:=by
    funext j;rcases j with j|j
    · rfl
    · rcases j with j|j
      · cases j <;> rfl
      · cases j <;> first | rfl | (change D.unary bits.length++[]=D.unary bits.length;exact List.append_nil _)
  rw [he0] at h0
  have h1:=SemiprimeD1StackRootScaleLeafDoubling.rounds (base bits) 20 (by omega) bits.length
  have hi:SemiprimeD1StackRootScaleLeafDoubling.index 20 (by omega)=(0:Fin 21):=by apply Fin.ext;rfl
  rw [hi] at h1
  have he1:SemiprimeD1StackRootScaleLeafDoubling.data (base bits) (2^20*bits.length) 0=scaled bits:=by
    funext j;rcases j with j|j
    · rfl
    · rcases j with j|j
      · cases j <;> rfl
      · cases j <;> rfl
  rw [he1] at h1
  exact join h0 h1
/-- The ACTUALLY acquired lambda is physically copied, and the first odd block
is really seeded by one marker push. All old cache fields stay byte-identical. -/
theorem prepare_square (bits : List Bool) :
    Runs program (5*SemiprimeD1StackRootScheduleArithmetic.lambda bits.length+5)
      (.double 20) (scaled bits) .squareCopy
      (SemiprimeD1StackRootScaleLeafSqrt.data (SemiprimeD1StackRootScheduleExecution.result bits)
        (D.unary (scale bits.length)) (SemiprimeD1StackRootScheduleArithmetic.lambda bits.length) 0 0) :=by
  let copied:=store (SemiprimeD1StackRootScheduleExecution.result bits)
    (D.contents (D.unary (SemiprimeD1StackRootScheduleArithmetic.lambda bits.length)) [] [] [] [] [])
    (metadata (D.unary (scale bits.length)) [] [] [])
  have h0:=copy_call 1 (.double 20) .seedOdd rfl (scaled bits) rfl
  have hl:(scaled bits (copySource 1)).length=SemiprimeD1StackRootScheduleArithmetic.lambda bits.length:=by
    change (List.replicate (SemiprimeD1StackRootScheduleArithmetic.lambda bits.length) true).length=_
    simp only [List.length_replicate]
  rw [hl] at h0
  have he0:Function.update (scaled bits) (copyTarget 1) (scaled bits (copySource 1)++scaled bits (copyTarget 1))=copied:=by
    funext j;rcases j with j|j
    · rfl
    · rcases j with j|j
      · cases j <;> first | rfl | (change D.unary (SemiprimeD1StackRootScheduleArithmetic.lambda bits.length)++[]=_;exact List.append_nil _)
      · cases j <;> rfl
  rw [he0] at h0
  have h1:=push .seedOdd .squareCopy (divStack .divisor) copied rfl
  have he1:Function.update copied (divStack .divisor) (true::copied (divStack .divisor))=
      SemiprimeD1StackRootScaleLeafSqrt.data (SemiprimeD1StackRootScheduleExecution.result bits)
        (D.unary (scale bits.length)) (SemiprimeD1StackRootScheduleArithmetic.lambda bits.length) 0 0:=by
    funext j;rcases j with j|j
    · rfl
    · rcases j with j|j
      · cases j <;> rfl
      · cases j <;> rfl
  rw [he1] at h1
  have h:=join h0 h1
  have ht:(5*SemiprimeD1StackRootScheduleArithmetic.lambda bits.length+4)+1=
      5*SemiprimeD1StackRootScheduleArithmetic.lambda bits.length+5:=by omega
  rw [ht] at h
  exact h
/-- Exact acquired scale/root/leaf result, including the retained positive
leaf divisor; all ten fresh roles and all fifteen old roles are explicit. -/
def result (bits : List Bool) : Stack→List Bool :=
  SemiprimeD1StackRootScaleLeafDivision.context (SemiprimeD1StackRootScheduleExecution.result bits)
    (scale bits.length) (root bits.length) (leaf bits.length) 0 (root bits.length+1) 0 0
/-- Fixed polynomial ready-stage allowance, with NO repeated N/root acquisition. -/
def readyBound (bits : List Bool) : Nat :=1000000000000*(bits.length+1)^3
/-- All actual scaling, square-root and quotient transitions obey this numeric envelope. -/
theorem arithmetic_bound (n lam k ts tl : Nat) (hl : lam≤n+20) (hk : k≤lam)
    (hs : ts≤100000*(2*lam+1)^2) (hq : tl≤120*(2^20*n+k+2)) :
    (5*n+4+SemiprimeD1StackRootScaleLeafDoubling.runTime n 20)+(5*lam+5)+ts+tl+1≤
      1000000000000*(n+1)^3 :=by
  have hd:=SemiprimeD1StackRootScaleLeafDoubling.twenty_time n
  have hb:2*lam+1≤41*(n+1):=by omega
  have hp:(2*lam+1)^2≤1681*(n+1)^2:=by
    have h:=Nat.pow_le_pow_left hb 2
    simpa only [mul_pow,show (41:Nat)^2=1681 by decide] using h
  have hp3:(n+1)^2≤(n+1)^3:=Nat.pow_le_pow_right (by omega) (by decide)
  norm_num at hq
  nlinarith
/-- Complete READY entry: genuine acquired cache → twenty physical doubles →
exact physical integer sqrt → real divider/+1. No arithmetic supplier premise. -/
theorem ready_trace (bits : List Bool) :
    ∃t,t+1≤readyBound bits ∧ Runs program t .ready (base bits) .done (result bits) :=by
  have h0:=acquire_scale bits
  have h1:=prepare_square bits
  obtain ⟨ts,ht,hs⟩:=SemiprimeD1StackRootScaleLeafSqrt.square_root
    (SemiprimeD1StackRootScheduleExecution.result bits) (D.unary (scale bits.length))
    (SemiprimeD1StackRootScheduleArithmetic.lambda bits.length) 0
  change Runs program ts .squareCopy
    (SemiprimeD1StackRootScaleLeafSqrt.data (SemiprimeD1StackRootScheduleExecution.result bits)
      (D.unary (scale bits.length)) (SemiprimeD1StackRootScheduleArithmetic.lambda bits.length) 0 0)
    .copyRoot (SemiprimeD1StackRootScaleLeafSqrt.result (SemiprimeD1StackRootScheduleExecution.result bits)
      (D.unary (scale bits.length)) (root bits.length)) at hs
  obtain ⟨tl,hl,h2⟩:=SemiprimeD1StackRootScaleLeafDivision.leaf_stage
    (SemiprimeD1StackRootScheduleExecution.result bits) (scale bits.length) (root bits.length)
  have h:=join (join (join h0 h1) hs) h2
  refine ⟨((5*bits.length+4+SemiprimeD1StackRootScaleLeafDoubling.runTime bits.length 20)+
    (5*SemiprimeD1StackRootScheduleArithmetic.lambda bits.length+5))+ts+tl,?_,h⟩
  have hk:root bits.length≤SemiprimeD1StackRootScheduleArithmetic.lambda bits.length:=Nat.sqrt_le_self _
  exact arithmetic_bound bits.length (SemiprimeD1StackRootScheduleArithmetic.lambda bits.length)
    (root bits.length) ts tl (SemiprimeD1StackRootScheduleArithmetic.lambda_le bits.length) hk ht hl
end RiemannGaussian.SemiprimeD1StackRootScaleLeafComponents
