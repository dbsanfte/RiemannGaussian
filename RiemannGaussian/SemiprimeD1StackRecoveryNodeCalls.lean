/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryNodeEncoding
/-! # Real complete Node140 and whole-weight calls, preserving actual outer returns -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryNodeCalls
open SemiprimeD1StackRecoveryNode SemiprimeD1StackRecoveryNodeInventory
open SemiprimeD1StackRecoveryNodeEncoding SemiprimeD1StackProcedureTrace
/-- Whole original five-word acquisition executes all Grid/affine/inverse/powers sources ONCE. -/
theorem node_call (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    ∃s≤SemiprimeD1StackRecoveryNodeInputsExecution.runBound a M u selected t width+1,
      Runs program s (ctl .start) (input (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)
        (ctl .weights) (afterNode a M u selected t width):=by
  obtain ⟨s,hs,hr⟩:=SemiprimeD1StackRecoveryNodeInputsExecution.source_run a M u selected t width ht
  refine ⟨s+1,Nat.add_le_add_right hs 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program node nodeLabel node_injective N.program
    (N.ctl .start) (fun _=>rfl) (ctl .start) (ctl .weights) rfl s
    (N.initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)
    (SemiprimeD1StackRecoveryNodeInputsEncoding.done a M u selected t width) _ _ rfl rfl rfl rfl hr
  · exact ⟨fun _=>rfl,fun _ _=>rfl⟩
  · constructor
    · intro role;rfl
    · intro role hrole;rcases role with role|role
      · exact (hrole role rfl).elim
      · rfl
/-- SAME actual whole Grid-cache ready entry omits Grid replay; no q/array/scalar advice enters. -/
theorem ready_call (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    ∃s≤SemiprimeD1StackRecoveryNodeInputsExecution.readyBound a M u selected t width+1,
      Runs program s (ctl .readyGrid) (gridReady a M u selected t width).data
        (ctl .weights) (afterNode a M u selected t width):=by
  obtain ⟨s,hs,hr⟩:=SemiprimeD1StackRecoveryNodeInputsExecution.ready_run a M u selected t width ht
  refine ⟨s+1,Nat.add_le_add_right hs 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program node nodeLabel node_injective N.program
    (N.ctl .readyGrid) (fun _=>rfl) (ctl .readyGrid) (ctl .weights) rfl s
    (SemiprimeD1StackRecoveryNodeInputsEncoding.gridReady a M u selected t width)
    (SemiprimeD1StackRecoveryNodeInputsEncoding.done a M u selected t width) _ _ rfl rfl rfl rfl hr
  · exact ⟨fun _=>rfl,fun _ _=>rfl⟩
  · constructor
    · intro role;rfl
    · intro role hrole;rcases role with role|role
      · exact (hrole role rfl).elim
      · rfl
/-- Actual acquired inverse/powers/Ezero/q/W feed the real WHOLE coefficient source, no caller replay. -/
theorem weights_call (a M u:ℕ) (selected:Fin (2^(a+1))) (t width:List Bool):
    ∃s≤SemiprimeD1StackRecoveryWeightsExecution.timeBound (Old.inverse width a M u selected)
        (Old.powers width a M u selected) (scalar a M u selected width) (q a M u selected) width+1,
      Runs program s (ctl .weights) (afterNode a M u selected t width) (ctl .done) (result a M u selected t width):=by
  let inv:=Old.inverse width a M u selected
  let pow:=Old.powers width a M u selected
  let sc:=scalar a M u selected width
  let count:=q a M u selected
  obtain ⟨s,hs,hr⟩:=SemiprimeD1StackRecoveryWeightsExecution.source_run inv pow sc count width
  have hin:=weight_initial a M u selected t width
  refine ⟨s+1,Nat.add_le_add_right hs 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program weight weightLabel weight_injective W.program
    (.local .start) (fun _=>rfl) (ctl .weights) (ctl .done) rfl s
    (W.initial (SemiprimeD1StackNormalizedInverse.tape inv) (SemiprimeD1StackNormalizedInverse.tape pow)
      (SemiprimeD1StackNormalizedInverse.signed sc) sc.denominator (List.replicate count true) width)
    (SemiprimeD1StackRecoveryWeightsExecution.done inv pow sc count width) _ _ rfl rfl rfl rfl hr hin
  change SemiprimeD1StackMultiplierLink.DataRel weight (afterNode a M u selected t width)
    (SemiprimeD1StackRecoveryWeightsExecution.result inv pow sc count width) (result a M u selected t width)
  rw [SemiprimeD1StackRecoveryNodeView.weight_result]
  exact SemiprimeD1StackMultiplierLink.data_update weight weight_injective _ _ _ hin
    (W.aux .output) (tape a M u selected width)
end RiemannGaussian.SemiprimeD1StackRecoveryNodeCalls
