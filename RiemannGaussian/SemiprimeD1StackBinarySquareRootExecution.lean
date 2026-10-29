/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBinarySquareRootFinish
import RiemannGaussian.SemiprimeD1StackBinarySquareRootCost
/-! # Whole original-binary sqrt source, SAME ready entry and fixed quartic clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackBinarySquareRootExecution
open SemiprimeD1StackBinarySquareRoot SemiprimeD1StackBinarySquareRootEncoding
open SemiprimeD1StackBinarySquareRootPrimitives SemiprimeD1StackBinarySquareRootLoop
open SemiprimeD1StackBinarySquareRootFinish SemiprimeD1StackBinarySquareRootCost
open SemiprimeD1StackProcedureTrace
/-- Own actual ready-path clock includes the whole bit loop, two final traversals and halt. -/
def readyBound (bits : List Bool) : ℕ :=
  loopTime bits bits.length []+finishTime (E.wordLoop bits bits.length [])+1
/-- Whole source pays exactly one real original-input metadata source before the same continuation. -/
def runBound (bits : List Bool) : ℕ :=
  SemiprimeD1StackPackedRootMetadataExecution.polynomial bits+1+readyBound bits
/-- Actual same-cache continuation, with all33 words and the real outer return frames. -/
theorem ready_trace (bits : List Bool) :
    ∃t,t+1 ≤ readyBound bits ∧ Runs program t (ctl .rootCopy) (ready bits).data (ctl .done) (result bits) := by
  have h0:=loop_run bits [] bits.length
  have h1:=finish_run bits (E.wordLoop bits bits.length [])
  exact ⟨_,Nat.le_refl _,join h0 h1⟩
/-- Actual original-binary front door composes the real metadata trace and real greedy loop. -/
theorem source_trace (bits : List Bool) :
    ∃t,t+1 ≤ runBound bits ∧ Runs program t (ctl .start) (input bits) (ctl .done) (result bits) := by
  obtain ⟨tm,hm,h0⟩:=metadata_call bits
  obtain ⟨tr,hr,h1⟩:=ready_trace bits
  exact ⟨tm+tr,by unfold runBound;omega,join h0 h1⟩
/-- Whole source cleanly halts; no private reset or return-frame erasure is assumed. -/
theorem source_run (bits : List Bool) :
    ∃t ≤ runBound bits,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) := by
  obtain ⟨t,ht,h⟩:=source_trace bits
  obtain ⟨out,he,ha⟩:=h [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result bits) [] out ha
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,he,Option.bind_some];exact hh⟩
/-- Same physically acquired metadata-cache entry also has an actual clean halt. -/
theorem ready_run (bits : List Bool) :
    ∃t ≤ readyBound bits,SemiprimeD1StackCalls.run program t (ready bits)=some (done bits) := by
  obtain ⟨t,ht,h⟩:=ready_trace bits
  obtain ⟨out,he,ha⟩:=h [] (ready bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result bits) [] out ha
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,he,Option.bind_some];exact hh⟩
/-- A fixed quartic bit-time bound, chosen before ALL original binary inputs. -/
def polynomial (bits : List Bool) : ℕ := 100000000*(bits.length+1)^4
/-- All final reverse/trim work is linear in the actual raw root width. -/
theorem finishTime_le (r : List Bool) : finishTime r ≤ 4*r.length+6 := by
  have h:=SemiprimeD1StackReduceExecution.trimTime_le r.reverse
  rw [List.length_reverse] at h
  unfold finishTime
  omega
/-- All actual original-source work fits the one fixed quartic, with no unary input expansion. -/
theorem runBound_le (bits : List Bool) : runBound bits ≤ polynomial bits := by
  have hl:=original_loopTime_le bits
  have hr:=SemiprimeD1StackBinarySquareRootArithmetic.original_word_length bits
  have hf:=finishTime_le (E.wordLoop bits bits.length [])
  have hp:=Nat.pow_le_pow_left (show 2*(bits.length+1)+2 ≤ 4*(bits.length+1) by omega) 3
  have hb:=hl.trans (Nat.mul_le_mul_left (bits.length+1) (Nat.mul_le_mul_left 4000 hp))
  unfold runBound readyBound polynomial SemiprimeD1StackPackedRootMetadataExecution.polynomial
  nlinarith
/-- Actual whole binary source and its OWN fixed quartic bound. -/
theorem source_run_bounded (bits : List Bool) :
    ∃t ≤ polynomial bits,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) := by
  obtain ⟨t,ht,h⟩:=source_run bits
  exact ⟨t,ht.trans (runBound_le bits),h⟩
/-- Actual same-cache ready entry and its OWN proved bound, without metadata replay. -/
theorem ready_run_bounded (bits : List Bool) :
    ∃t ≤ polynomial bits,SemiprimeD1StackCalls.run program t (ready bits)=some (done bits) := by
  obtain ⟨t,ht,h⟩:=ready_run bits
  have hr : readyBound bits ≤ runBound bits := by unfold runBound;omega
  exact ⟨t,ht.trans (hr.trans (runBound_le bits)),h⟩
end RiemannGaussian.SemiprimeD1StackBinarySquareRootExecution
