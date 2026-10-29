/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryNodeCalls
/-! # Complete actual original-phase to full native local weights, including same-Grid-ready entry -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryNodeExecution
open SemiprimeD1StackRecoveryNode SemiprimeD1StackRecoveryNodeEncoding
open SemiprimeD1StackRecoveryNodeCalls SemiprimeD1StackProcedureTrace
/-- Whole actual coefficient source runs on its physically acquired operand bytes. -/
def weightBound (a M u:ℕ) (selected:Fin (2^(a+1))) (width:List Bool):ℕ:=
  SemiprimeD1StackRecoveryWeightsExecution.timeBound (Old.inverse width a M u selected)
    (Old.powers width a M u selected) (scalar a M u selected width) (q a M u selected) width
/-- TWO actual whole calls, both real caller/returns, then real final halt. -/
def runBound (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool):ℕ:=
  SemiprimeD1StackRecoveryNodeInputsExecution.runBound a M u selected t width+weightBound a M u selected width+3
/-- SAME already-acquired Grid-cache continuation has no Grid replay in its own clock. -/
def readyBound (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool):ℕ:=
  SemiprimeD1StackRecoveryNodeInputsExecution.readyBound a M u selected t width+weightBound a M u selected width+3
/-- Every coefficient comes from real acquired arrays/scalar; no per-coefficient or aggregate supplier exists. -/
theorem source_trace (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    ∃s≤runBound a M u selected t width-1,Runs program s (ctl .start)
      (input (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)
      (ctl .done) (result a M u selected t width):=by
  obtain ⟨s0,hs0,h0⟩:=node_call a M u selected t width ht
  obtain ⟨s1,hs1,h1⟩:=weights_call a M u selected t width
  refine ⟨s0+s1,?_,runs_trans program _ _ _ _ _ _ _ _ h0 h1⟩
  unfold runBound weightBound
  omega
/-- SAME program receives only the ACTUAL whole Grid cache, then actually acquires remaining arrays and all weights. -/
theorem ready_trace (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    ∃s≤readyBound a M u selected t width-1,Runs program s (ctl .readyGrid)
      (gridReady a M u selected t width).data (ctl .done) (result a M u selected t width):=by
  obtain ⟨s0,hs0,h0⟩:=ready_call a M u selected t width ht
  obtain ⟨s1,hs1,h1⟩:=weights_call a M u selected t width
  refine ⟨s0+s1,?_,runs_trans program _ _ _ _ _ _ _ _ h0 h1⟩
  unfold readyBound weightBound
  omega
/-- Whole true halt with all140 retained old cache words and complete canonical-weight output. -/
theorem source_run (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    ∃s≤runBound a M u selected t width,SemiprimeD1StackCalls.run program s
      (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)=some (done a M u selected t width):=by
  obtain ⟨s,hs,h⟩:=source_trace a M u selected t width ht
  obtain ⟨finish,hfinish,hAt⟩:=h []
    (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width) ⟨rfl,rfl,rfl⟩
  refine ⟨s+1,?_,?_⟩
  · unfold runBound at hs ⊢;omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some]
    exact halt_run program (ctl .done) rfl _ [] finish hAt
/-- Actual Grid-cache same-program continuation, with all later coefficients genuinely acquired before true halt. -/
theorem ready_run (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    ∃s≤readyBound a M u selected t width,SemiprimeD1StackCalls.run program s
      (gridReady a M u selected t width)=some (done a M u selected t width):=by
  obtain ⟨s,hs,h⟩:=ready_trace a M u selected t width ht
  obtain ⟨finish,hfinish,hAt⟩:=h [] (gridReady a M u selected t width) ⟨rfl,rfl,rfl⟩
  refine ⟨s+1,?_,?_⟩
  · unfold readyBound at hs ⊢;omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some]
    exact halt_run program (ctl .done) rfl _ [] finish hAt
end RiemannGaussian.SemiprimeD1StackRecoveryNodeExecution
