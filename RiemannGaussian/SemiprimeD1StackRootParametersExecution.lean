/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootParameters
import RiemannGaussian.SemiprimeD1StackRootScaleLeafOriginal

/-! # Same-program acquisition of every original root scheduling operand -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackRootParametersExecution
open SemiprimeD1StackRootParameters SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
namespace LR
export SemiprimeD1StackRootScaleLeafComponents (result readyBound)
export SemiprimeD1StackRootScaleLeafExecution (done)
end LR
local notation "ctl" => (Sum.inl : Control→Label)
/-- All98 already acquired cells survive; the ten new cells are the actual threshold result. -/
def result (bits:List Bool) : Stack→List Bool :=
  data (M.result bits) (fun k=>LR.result bits (.inr k))
/-- Exact complete actual halt with no pending real component return frames. -/
def done (bits:List Bool) : C.State Stack Label := ⟨none,none,none,result bits,[]⟩
/-- The leaf program sees its actually acquired old cache and physically empty fresh roles. -/
theorem ready_projection (bits:List Bool) (k:L.Stack) :
    afterMetadata bits (leafStack k)=(L.ready bits).data k := by
  cases k with
  | inl k=>exact SemiprimeD1StackRootControllerMetadataOriginal.schedule_projection bits k
  | inr k=>cases k <;> rfl
/-- Its final projection is exact because the threshold program preserves every old-cache field. -/
theorem result_projection (bits:List Bool) (k:L.Stack) : result bits (leafStack k)=LR.result bits k := by
  cases k with
  | inl k=>
    exact (SemiprimeD1StackRootControllerMetadataOriginal.schedule_projection bits k).trans
      (SemiprimeD1StackRootScaleLeafOriginal.retained_cache bits k).symm
  | inr k=>rfl
/-- One real included call performs all actual N-only graph/count/schedule acquisition. -/
theorem metadata_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t≤M.runBound bits,Runs program (t+1) (ctl .start) (input bits) (ctl .leaf) (afterMetadata bits) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackRootControllerMetadataExecution.source_run bits hc hN
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program metadataStack metadataLabel Sum.inl_injective
    M.program (.inl .start) (fun _=>rfl) (ctl .start) (ctl .leaf) rfl t
    (M.initial bits) (M.done bits) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;cases k with
      | inl k=>exact (hk k rfl).elim
      | inr k=>rfl
/-- Reuse an actually acquired old15 cache inside any retained metadata bank. -/
theorem prepared_leaf_call (bits:List Bool) (cached:M.Stack→List Bool)
    (hcache:∀k,cached (M.scheduleStack k)=SemiprimeD1StackRootScheduleExecution.result bits k) :
    ∃t≤LR.readyBound bits,Runs program (t+1) (ctl .leaf) (data cached (fun _=>[])) (ctl .done)
      (data cached (fun k=>LR.result bits (.inr k))) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackRootScaleLeafExecution.ready_run bits
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program leafStack leafLabel leaf_injective
    L.program .ready (fun _=>rfl) (ctl .leaf) (ctl .done) rfl t
    (L.ready bits) (LR.done bits) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;cases k with
      | inl k=>exact hcache k
      | inr k=>cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k with
      | inl k=>exact (hcache k).trans (SemiprimeD1StackRootScaleLeafOriginal.retained_cache bits k).symm
      | inr k=>rfl
    · intro k hk;cases k with
      | inl k=>rfl
      | inr k=>exact (hk (.inr k) rfl).elim
/-- Real scale/exact-sqrt/division work reuses the original acquired cache without another N acquisition. -/
theorem leaf_call (bits:List Bool) :
    ∃t≤LR.readyBound bits,Runs program (t+1) (ctl .leaf) (afterMetadata bits) (ctl .done) (result bits) :=
  prepared_leaf_call bits (M.result bits) (SemiprimeD1StackRootControllerMetadataOriginal.schedule_projection bits)
/-- The entire root source executes in one literal fixed program with its own combined clock. -/
theorem source_trace (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t,t+1≤runBound bits ∧ Runs program t (ctl .start) (input bits) (ctl .done) (result bits) := by
  obtain ⟨m,hm,h0⟩:=metadata_call bits hc hN
  obtain ⟨l,hl,h1⟩:=leaf_call bits
  refine ⟨(m+1)+(l+1),?_,runs_trans program _ _ _ _ _ _ _ _ h0 h1⟩
  change l≤10^12*(bits.length+1)^3 at hl
  unfold runBound
  omega
/-- Complete actual N-only execution pays both calls, all threshold work and the final halt. -/
theorem source_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t≤runBound bits,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) := by
  obtain ⟨t,ht,h⟩:=source_trace bits hc hN
  obtain ⟨finish,hf,hs⟩:=h [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result bits) [] finish hs
  refine ⟨t+1,ht,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hh
end RiemannGaussian.SemiprimeD1StackRootParametersExecution
