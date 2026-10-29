/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceLookup
/-! # Actual finite classifier continuations after parsed lookup flags -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceEdgeFinish
open SemiprimeD1StackSourceIncidence SemiprimeD1StackSourceIncidencePrimitives
open SemiprimeD1StackSourceIncidenceView SemiprimeD1StackSourceIncidenceCalls
open SemiprimeD1StackProcedureTrace
open SemiprimeD1StackSourceIncidenceSpec (Status possible drop)
/-- One literal finite jump preserves every47 actual word and real caller return. -/
theorem jump_run (pc next:Label) (words:Stack→List Bool) (hc:program pc=.base (.jump next)) :
    Runs program 1 pc words next words:=one_base program pc next (.jump next) words words hc rfl rfl
/-- An actual missing first endpoint returns free only after both lookup fields have been physically cleared. -/
theorem first_missing (ids:List (List Bool)) (chosen pfx:List Bool) (words:Aux→List Bool) (kind:Edge) :
    Runs program 3 (.afterLookup kind false false) (view ids chosen pfx words [] [] [] [] [] []) .edgeReturn
      (view ids chosen pfx words [] [] [] [true,true] [] []) :=by
  exact join (jump_run (.afterLookup kind false false) (.status .free) _ rfl) (status_run ids chosen pfx words .free)
/-- A second missing endpoint physically clears the first fixed ID before reporting a free edge. -/
theorem second_missing (ids:List (List Bool)) (chosen pfx:List Bool) (words:Aux→List Bool)
    (kind:Edge) (left:List Bool) :
    Runs program (1+(left.length+1)+2) (.afterLookup kind true false)
      (view ids chosen pfx words [] left [] [] [] []) .edgeReturn
      (view ids chosen pfx words [] [] [] [true,true] [] []) :=by
  have h0:=jump_run (.afterLookup kind true false) .clearFreeLeft (view ids chosen pfx words [] left [] [] [] []) rfl
  have h1:=drain_loop .clearFreeLeft (.status .free) (aux .eqLeft) rfl
    (view ids chosen pfx words [] left [] [] [] []) left rfl
  rw [update_left] at h1
  exact join (join h0 h1) (status_run ids chosen pfx words .free)
/-- Both actual fixed IDs are compared numerically, their copied bytes consumed, and the result physically emitted. -/
theorem compare_ids (ids:List (List Bool)) (chosen pfx:List Bool) (words:Aux→List Bool)
    (left right:List Bool) (hs:words .eqScratch=[]) :
    Runs program (SemiprimeD1StackWordEqualExecution.executionTime left right+1+1+2) .compareIDs
      (view ids chosen pfx words [] left right [] [] []) .edgeReturn
      (view ids chosen pfx words [] [] []
        (if SemiprimeBitArithmetic.bitValue left=SemiprimeBitArithmetic.bitValue right then [true,false] else [false,false]) [] []) :=by
  have h0:=equal_call .compareIDs .idsEqual rfl (view ids chosen pfx words [] left right [] [] []) hs rfl
  change Runs program _ _ _ _ (Function.update (Function.update (Function.update
    (view ids chosen pfx words [] left right [] [] []) (aux .eqLeft) []) (aux .eqRight) []) (aux .eqOutput)
    [decide (SemiprimeBitArithmetic.bitValue left=SemiprimeBitArithmetic.bitValue right)]) at h0
  rw [update_left,update_right,update_comparison] at h0
  have h1:=pop_run .idsEqual .abort (.status .reject) (.status .stable) (aux .eqOutput)
    (view ids chosen pfx words [] [] [] [decide (SemiprimeBitArithmetic.bitValue left=SemiprimeBitArithmetic.bitValue right)] [] [])
    [decide (SemiprimeBitArithmetic.bitValue left=SemiprimeBitArithmetic.bitValue right)] rfl rfl
  change Runs program 1 _ _ _ (Function.update
    (view ids chosen pfx words [] [] [] [decide (SemiprimeBitArithmetic.bitValue left=SemiprimeBitArithmetic.bitValue right)] [] [])
    (aux .eqOutput) []) at h1
  rw [update_comparison] at h1
  by_cases he:SemiprimeBitArithmetic.bitValue left=SemiprimeBitArithmetic.bitValue right
  · simp only [he,decide_true,ite_true,SemiprimeD1StackBytecode.choose] at h0 h1 ⊢
    exact join (join h0 h1) (status_run ids chosen pfx words .stable)
  · simp only [he,decide_false,ite_false,SemiprimeD1StackBytecode.choose] at h0 h1 ⊢
    exact join (join h0 h1) (status_run ids chosen pfx words .reject)
/-- The second successful lookup jumps into the real fixed-ID comparison, never a supplied equality bit. -/
theorem second_present (ids:List (List Bool)) (chosen pfx:List Bool) (words:Aux→List Bool)
    (kind:Edge) (left right:List Bool) (hs:words .eqScratch=[]) :
    Runs program (1+(SemiprimeD1StackWordEqualExecution.executionTime left right+1+1+2))
      (.afterLookup kind true true) (view ids chosen pfx words [] left right [] [] []) .edgeReturn
      (view ids chosen pfx words [] [] []
        (if SemiprimeBitArithmetic.bitValue left=SemiprimeBitArithmetic.bitValue right then [true,false] else [false,false]) [] []) :=by
  exact join (jump_run (.afterLookup kind true true) .compareIDs _ rfl) (compare_ids ids chosen pfx words left right hs)
end RiemannGaussian.SemiprimeD1StackSourceIncidenceEdgeFinish
