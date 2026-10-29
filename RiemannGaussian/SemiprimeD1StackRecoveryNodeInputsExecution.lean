/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsCalls
import RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsReadyCall
/-! # Entire real Grid→affine→inverse→powers source, and SAME actual Grid-cache ready entry -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsExecution
open SemiprimeD1StackRecoveryNodeInputs SemiprimeD1StackRecoveryNodeInputsEncoding
open SemiprimeD1StackRecoveryNodeInputsCalls SemiprimeD1StackRecoveryNodeInputsReadyCall
open SemiprimeD1StackProcedureTrace
/-- Entire real inverse and powers calls, including BOTH actual caller/return overheads. -/
def tailBound (a M u : ℕ) (selected : Fin (2^(a+1))) (width : List Bool) : ℕ :=
  (SemiprimeD1StackNormalizedInverseBounds.polynomial (E.array a M u selected width) (E.retained a M u selected) width+1)+
    (SemiprimeD1StackRecoveryPowersExecution.timeBound (argument a M u selected width) width (E.retained a M u selected)+1)
/-- Own whole elapsed cap is the sum of the three real source calls, three returns and final true halt. -/
def runBound (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) : ℕ :=
  (SemiprimeD1StackRecoveryAffineExecution.timeBound a M u selected t width+1)+tailBound a M u selected width+1
/-- SAME program ready budget contains NO Grid call, only actual remaining affine/inverse/powers work. -/
def readyBound (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) : ℕ :=
  (SemiprimeD1StackRecoveryNodeInputsAffineReady.timeBound a M u selected t width+1)+tailBound a M u selected width+1
/-- Inverse and powers come from actual direct-alias caches left by the complete real affine source. -/
theorem tail_trace (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) :
    ∃s≤tailBound a M u selected width,Runs program s (ctl .inverse) (afterAffine a M u selected t width)
      (ctl .done) (result a M u selected t width) := by
  obtain ⟨s0,hs0,h0⟩:=inverse_call a M u selected t width
  obtain ⟨s1,hs1,h1⟩:=powers_call a M u selected t width
  exact ⟨s0+s1,Nat.add_le_add hs0 hs1,runs_trans program _ _ _ _ _ _ _ _ h0 h1⟩
/-- Whole actual fixed140-role trace begins with ONLY the five original phase words. -/
theorem source_trace (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) :
    ∃s≤runBound a M u selected t width-1,
      Runs program s (ctl .start)
        (input (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)
        (ctl .done) (result a M u selected t width) := by
  obtain ⟨s0,hs0,h0⟩:=affine_call a M u selected t width ht
  obtain ⟨s1,hs1,h1⟩:=tail_trace a M u selected t width
  refine ⟨s0+s1,?_,runs_trans program _ _ _ _ _ _ _ _ h0 h1⟩
  simp only [runBound,Nat.add_sub_cancel]
  omega
/-- Actual already acquired Grid cache feeds the SAME remaining program, without replay or coefficient/q/power advice. -/
theorem ready_trace (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) :
    ∃s≤readyBound a M u selected t width-1,
      Runs program s (ctl .readyGrid) (gridReady a M u selected t width).data
        (ctl .done) (result a M u selected t width) := by
  obtain ⟨s0,hs0,h0⟩:=ready_call a M u selected t width ht
  obtain ⟨s1,hs1,h1⟩:=tail_trace a M u selected t width
  refine ⟨s0+s1,?_,runs_trans program _ _ _ _ _ _ _ _ h0 h1⟩
  simp only [readyBound,Nat.add_sub_cancel]
  omega
/-- One whole actual source acquires BOTH complete arrays and truehalts; every old112 field is retained. -/
theorem source_run (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) :
    ∃s≤runBound a M u selected t width,SemiprimeD1StackCalls.run program s
      (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)=some (done a M u selected t width) := by
  obtain ⟨s,hs,h⟩:=source_trace a M u selected t width ht
  obtain ⟨finish,hfinish,hAt⟩:=h []
    (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width) ⟨rfl,rfl,rfl⟩
  refine ⟨s+1,?_,?_⟩
  · simp only [runBound,Nat.add_sub_cancel] at hs ⊢
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some]
    exact halt_run program (ctl .done) rfl _ [] finish hAt
/-- Honest same-program ready execution from ACTUAL Grid acquisition; BOTH arrays are subsequently computed by real calls. -/
theorem ready_run (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) :
    ∃s≤readyBound a M u selected t width,SemiprimeD1StackCalls.run program s
      (gridReady a M u selected t width)=some (done a M u selected t width) := by
  obtain ⟨s,hs,h⟩:=ready_trace a M u selected t width ht
  obtain ⟨finish,hfinish,hAt⟩:=h [] (gridReady a M u selected t width) ⟨rfl,rfl,rfl⟩
  refine ⟨s+1,?_,?_⟩
  · simp only [readyBound,Nat.add_sub_cancel] at hs ⊢
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some]
    exact halt_run program (ctl .done) rfl _ [] finish hAt
end RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsExecution
