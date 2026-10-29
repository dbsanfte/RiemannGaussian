/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootMetadataLoop
/-! # Whole original-N source and actual acquired-bootstrap ready entry -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPackedRootMetadataExecution
open SemiprimeD1StackPackedRootMetadata SemiprimeD1StackPackedRootMetadataEncoding
open SemiprimeD1StackPackedRootMetadataPrimitives SemiprimeD1StackPackedRootMetadataCalls
open SemiprimeD1StackPackedRootMetadataLoop SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Explicit five-role empty boundary, before any output is constructed. -/
theorem empty_words : words [] [] [] [] []=(fun _ => []) := by funext k;cases k <;> rfl
/-- The SAME ready entry pays the base seed, actual width copy, whole loop and halt. -/
def readyBound (bits : List Bool) : ℕ := 5*bits.length+6+loopTime 0 bits.length
/-- Whole original-input budget adds the ONE actual bootstrap call. -/
def runBound (bits : List Bool) : ℕ := 5*bits.length+5+readyBound bits
/-- Complete real acquired-cache continuation; the input width was physically
obtained by the actual bootstrap and is retained throughout. -/
theorem ready_trace (bits : List Bool) :
    ∃t,t+1 ≤ readyBound bits ∧ Runs program t (ctl .seedBase) (ready bits).data (ctl .done) (result bits) := by
  let b := (B.done bits).store
  let before := bank b (fun _ => []) (words [] [] [] [] [])
  have h0 := push_run .seedBase (ctl .copyWidth) (aux .base) true before rfl
  dsimp only [before] at h0
  rw [update_aux,words_update] at h0
  let middle := bank b (fun _ => []) (words [] [] [] [true] [])
  have h1 := copy_call .width .copyWidth .read rfl middle (List.replicate bits.length true) [] rfl rfl rfl
  rw [List.append_nil] at h1
  dsimp only [middle] at h1
  change Runs program _ _ _ _ (Function.update _ (aux .reader) (List.replicate bits.length true)) at h1
  rw [update_aux,words_update] at h1
  change Runs program _ _ _ (ctl .read) (loop b 0 bits.length) at h1
  have h2 := loop_run b 0 bits.length
  have h := join (join h0 h1) h2
  have hstart : before=(ready bits).data := by
    dsimp only [before,ready]
    rw [empty_words]
  dsimp only [before] at hstart
  rw [hstart,Nat.zero_add] at h
  change Runs program _ _ _ (ctl .done) (result bits) at h
  refine ⟨_,?_,h⟩
  unfold readyBound
  simp only [List.length_replicate]
  omega
/-- Whole N-only source actually performs width acquisition before reusing its
exact stopped four-role cache in the SAME program. -/
theorem source_trace (bits : List Bool) :
    ∃t,t+1 ≤ runBound bits ∧ Runs program t (ctl .start) (input bits) (ctl .done) (result bits) := by
  have h0 := boot_call bits
  obtain ⟨t,ht,h1⟩ := ready_trace bits
  have h := join h0 h1
  exact ⟨_,by unfold runBound;omega,h⟩
/-- Actual source halt clears both transient flags and retains every real output. -/
theorem source_run (bits : List Bool) :
    ∃t ≤ runBound bits,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) := by
  obtain ⟨t,ht,h⟩ := source_trace bits
  obtain ⟨out,he,ha⟩ := h [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh := halt_run program (ctl .done) rfl (result bits) [] out ha
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,he,Option.bind_some];exact hh⟩
/-- The SAME actual ready entry also halts, without repeating the width acquisition. -/
theorem ready_run (bits : List Bool) :
    ∃t ≤ readyBound bits,SemiprimeD1StackCalls.run program t (ready bits)=some (done bits) := by
  obtain ⟨t,ht,h⟩ := ready_trace bits
  obtain ⟨out,he,ha⟩ := h [] (ready bits) ⟨rfl,rfl,rfl⟩
  have hh := halt_run program (ctl .done) rfl (result bits) [] out ha
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,he,Option.bind_some];exact hh⟩
/-- Fixed own bit-source polynomial, before ALL original words. -/
def polynomial (bits : List Bool) : ℕ := 1000*(bits.length+1)^2
/-- Whole source includes every bootstrap/copy/add/shift/cleanup and actual return. -/
theorem runBound_le (bits : List Bool) : runBound bits ≤ polynomial bits := by
  have h := loopTime_le 0 bits.length
  unfold runBound readyBound polynomial
  nlinarith only [h]
/-- Original-input source runs within its OWN fixed quadratic. -/
theorem source_run_bounded (bits : List Bool) :
    ∃t ≤ polynomial bits,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) := by
  obtain ⟨t,ht,h⟩ := source_run bits
  exact ⟨t,ht.trans (runBound_le bits),h⟩
/-- SAME cache-ready source shares the OWN whole polynomial, without clock transport. -/
theorem ready_run_bounded (bits : List Bool) :
    ∃t ≤ polynomial bits,SemiprimeD1StackCalls.run program t (ready bits)=some (done bits) := by
  obtain ⟨t,ht,h⟩ := ready_run bits
  have hr : readyBound bits ≤ runBound bits := by unfold runBound;omega
  exact ⟨t,ht.trans (hr.trans (runBound_le bits)),h⟩
end RiemannGaussian.SemiprimeD1StackPackedRootMetadataExecution
