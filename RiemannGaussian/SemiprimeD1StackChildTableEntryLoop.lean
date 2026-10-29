/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildTableEntryOld
import RiemannGaussian.SemiprimeD1StackChildTableEntryZeros
import RiemannGaussian.SemiprimeD1StackChildTableEntryFinish
/-! # Whole actual individual integer lift coefficient loop
The only loop drivers are actual parsed parent vector fields and acquired rank
markers. Counts below describe those existing words only in proof statements.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildTableEntryLoop
open SemiprimeD1StackChildTableEntry SemiprimeD1StackChildTableEntryEncoding
open SemiprimeD1StackChildTableEntryPrimitives SemiprimeD1StackChildTableEntryScalar
open SemiprimeD1StackChildTableEntryRows SemiprimeD1StackChildTableEntryFinish
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
namespace Old
export SemiprimeD1StackChildTableEntryOld (budget old_run)
end Old
namespace Zero
export SemiprimeD1StackChildTableEntryZeros (budget zeros_run)
end Zero
local notation "ctl"=>Label.local
/-- Literal old-word followed by zero-word individual reduction interpretation. -/
theorem lifted_eq (p:List Bool) (ws:List (List Bool)) (zeros:Nat):
    lifted p ws zeros=ws.map (fun word=>SR.result word p)++List.replicate zeros (SR.result [] p):=by
  simp only [lifted,List.map_append,List.map_replicate]
  rfl
/-- Actual old and zero loops are composed before any final output/history projection. -/
theorem coefficient_run (old child:J.Stack→List Bool) (assignment path table order entry p:List Bool)
    (ws:List (List Bool)) (zeros:Nat) (hp:child J.precisionBits=p):
    Runs program (Old.budget p ws+Zero.budget p zeros) (ctl .header)
      (state old child assignment path table order entry (vectorBits ws) (unary ws.length) (unary (ws.length+zeros)) [])
      (ctl .clearPath) (state old child assignment path table order entry [] [] [] (history (lifted p ws zeros)).reverse):=by
  have h0:=Old.old_run old child assignment path table order entry [] p ws zeros hp
  simp only [List.append_nil] at h0
  have h1:=Zero.zeros_run old child assignment path table order entry (history (ws.map (fun word=>SR.result word p))).reverse p zeros hp
  have h:=join h0 h1
  have he:(history (lifted p ws zeros)).reverse=
      (history (List.replicate zeros (SR.result [] p))).reverse++(history (ws.map (fun word=>SR.result word p))).reverse:=by
    rw [lifted_eq,history,List.flatMap_append,List.reverse_append]
    rfl
  rw [he]
  exact h
/-- Exact loop/output clock includes every original/zero coefficient, all real returns, path cleanup and final actual halt. -/
def timeBound (p:List Bool) (ws:List (List Bool)) (zeros:Nat) (path:List Bool):Nat:=
  Old.budget p ws+Zero.budget p zeros+path.length+2*(history (lifted p ws zeros)).length+7
/-- Actual loop, final physical vector reverse and success push reach all61 specified words before the real final halt. -/
theorem loop_trace (old child:J.Stack→List Bool) (assignment path table order entry p:List Bool)
    (ws:List (List Bool)) (zeros:Nat) (hp:child J.precisionBits=p):
    Runs program (timeBound p ws zeros path-1) (ctl .header)
      (state old child assignment path table order entry (vectorBits ws) (unary ws.length) (unary (ws.length+zeros)) [])
      (ctl .done) (finishBank old child assignment table order entry (vectorBits (lifted p ws zeros))):=by
  have h0:=coefficient_run old child assignment path table order entry p ws zeros hp
  have h1:=finish_run old child assignment path table order entry (history (lifted p ws zeros)).reverse
  rw [List.reverse_reverse,history_vector] at h1
  have h:=join h0 h1
  unfold timeBound
  convert h using 1; simp only [List.length_reverse];omega
end RiemannGaussian.SemiprimeD1StackChildTableEntryLoop
