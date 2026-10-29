/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootContextCalls
/-! # Complete actual original-N root context source and own bit-time bounds -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPackedRootContextExecution
open SemiprimeD1StackPackedRootContext SemiprimeD1StackPackedRootContextEncoding
open SemiprimeD1StackPackedRootContextPrimitives SemiprimeD1StackPackedRootContextCalls
open SemiprimeD1StackProcedureTrace
local notation "ctl" => (Sum.inl : Control→Label)
/-- SAME actual metadata-ready continuation pays the copy, literal header,
entire context source and true final halt, with precision VALUE included. -/
def readyBound (bits : List Bool) : ℕ :=
  (5*(M.precisionWord bits.length).length+4)+1+
    (SemiprimeD1StackJetContextCorrectness.budget [] (M.precisionWord bits.length)+1)+1
/-- Whole original-input clock adds the ONE actually executed metadata call. -/
def runBound (bits : List Bool) : ℕ :=
  SemiprimeD1StackPackedRootMetadataExecution.polynomial bits+1+readyBound bits
/-- Complete acquired-cache path performs the REAL handoff, header seed and
context source, with every metadata word and real caller return preserved. -/
theorem ready_trace (bits : List Bool) :
    ∃t,t+1 ≤ readyBound bits ∧ Runs program t (ctl .copyPrecision) (ready bits).data (ctl .done) (result bits) := by
  have h0 := copy_call (ready bits).data (M.precisionWord bits.length) [] rfl rfl rfl
  rw [List.append_nil] at h0
  change Runs program _ _ _ _ (Function.update (ready bits).data (context J.precisionBits) (M.precisionWord bits.length)) at h0
  have he0 : Function.update (ready bits).data (context J.precisionBits) (M.precisionWord bits.length)=copied bits := by
    change Function.update (data (M.result bits) (fun _ => [])) (context J.precisionBits) (M.precisionWord bits.length)=
      data (M.result bits) (J.initial [] (M.precisionWord bits.length)).data
    rw [←empty_context,data_context,context_precision]
  rw [he0] at h0
  have h1 := axes_seed (copied bits)
  change Runs program 1 _ _ _ (Function.update (copied bits) (context J.axesCache) [false]) at h1
  have he1 : Function.update (copied bits) (context J.axesCache) [false]=prepared bits := by
    unfold copied prepared
    rw [data_context,context_axes]
  rw [he1] at h1
  obtain ⟨t,ht,h2⟩ := context_call (M.result bits) (M.precisionWord bits.length)
  have h := join (join h0 h1) h2
  refine ⟨_,?_,h⟩
  unfold readyBound
  omega
/-- Whole N-only path executes the actual metadata source ONCE, then the SAME
proved cache-ready continuation; no word equality transports a native clock. -/
theorem source_trace (bits : List Bool) :
    ∃t,t+1 ≤ runBound bits ∧ Runs program t (ctl .start) (input bits) (ctl .done) (result bits) := by
  obtain ⟨tm,hm,h0⟩ := metadata_call bits
  obtain ⟨tc,hc,h1⟩ := ready_trace bits
  exact ⟨tm+tc,by unfold runBound;omega,join h0 h1⟩
/-- Complete source halts with all real outputs, both flags cleared and no extra frame. -/
theorem source_run (bits : List Bool) :
    ∃t ≤ runBound bits,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) := by
  obtain ⟨t,ht,h⟩ := source_trace bits
  obtain ⟨out,he,ha⟩ := h [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh := halt_run program (ctl .done) rfl (result bits) [] out ha
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,he,Option.bind_some];exact hh⟩
/-- SAME actual metadata-ready continuation also has a clean real halt. -/
theorem ready_run (bits : List Bool) :
    ∃t ≤ readyBound bits,SemiprimeD1StackCalls.run program t (ready bits)=some (done bits) := by
  obtain ⟨t,ht,h⟩ := ready_trace bits
  obtain ⟨out,he,ha⟩ := h [] (ready bits) ⟨rfl,rfl,rfl⟩
  have hh := halt_run program (ctl .done) rfl (result bits) [] out ha
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,he,Option.bind_some];exact hh⟩
/-- Fixed whole-source quadratic is chosen before every N. -/
def polynomial (bits : List Bool) : ℕ := 2000*(bits.length+1)^2
/-- Actual cached-metadata reuse needs only a fixed linear clock. -/
def readyPolynomial (bits : List Bool) : ℕ := 1000*(bits.length+1)
/-- All ready operations, including acquired TRUE-width VALUE, have a linear cap. -/
theorem readyBound_le (bits : List Bool) : readyBound bits ≤ 62*bits.length+229 := by
  have h0 := context_budget bits
  have h1 := SemiprimeD1StackPackedRootMetadataEncoding.precision_length bits.length
  unfold readyBound
  omega
/-- Complete N-only source is quadratic, with neither rank nor width advice. -/
theorem runBound_le (bits : List Bool) : runBound bits ≤ polynomial bits := by
  have h := readyBound_le bits
  unfold runBound polynomial SemiprimeD1StackPackedRootMetadataExecution.polynomial
  nlinarith only [h]
/-- The ready entry's OWN physical bound is linear in original input size. -/
theorem readyBound_le_polynomial (bits : List Bool) : readyBound bits ≤ readyPolynomial bits := by
  have h := readyBound_le bits
  unfold readyPolynomial
  omega
/-- Whole actual source and its OWN fixed quadratic time. -/
theorem source_run_bounded (bits : List Bool) :
    ∃t ≤ polynomial bits,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) := by
  obtain ⟨t,ht,h⟩ := source_run bits
  exact ⟨t,ht.trans (runBound_le bits),h⟩
/-- SAME program, ACTUALLY acquired metadata cache, and OWN linear time. -/
theorem ready_run_bounded (bits : List Bool) :
    ∃t ≤ readyPolynomial bits,SemiprimeD1StackCalls.run program t (ready bits)=some (done bits) := by
  obtain ⟨t,ht,h⟩ := ready_run bits
  exact ⟨t,ht.trans (readyBound_le_polynomial bits),h⟩
end RiemannGaussian.SemiprimeD1StackPackedRootContextExecution
