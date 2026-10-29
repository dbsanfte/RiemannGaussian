/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalNormalizeEncoding
import RiemannGaussian.SemiprimeD1StackRationalNormalizePrimitives
/-! # Actual whole GCD and reused positive-divider calls, with all caller cells retained -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRationalNormalizeCalls
open SemiprimeD1StackRationalNormalize SemiprimeD1StackRationalNormalizeEncoding
open SemiprimeD1StackProcedureTrace
namespace P
export SemiprimeD1StackRationalNormalizePrimitives (join copy_call push_run pop_run peek_run drain_loop)
end P
/-- Whole actual GCD18 acquisition, preserving every caller output/sign word and all genuine outer returns. -/
theorem gcd_call (before:Stack→List Bool) (num den:List Bool)
    (hi:∀k,before (gcdStack k)=SemiprimeD1StackEuclidGCD.input num den k) :
    Runs program (SemiprimeD1StackEuclidGCDExecution.runBound num den+1) .gcdCall before (.copyInput false)
      (Sum.elim (SemiprimeD1StackEuclidGCDEncoding.result num den) (fun k=>before (aux k))) :=by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program gcdStack Label.gcd gcd_injective G.program .start
    (fun _=>rfl) .gcdCall (.copyInput false) rfl (SemiprimeD1StackEuclidGCDExecution.runBound num den)
    (SemiprimeD1StackEuclidGCD.initial num den) (SemiprimeD1StackEuclidGCDEncoding.done num den) _ _ rfl rfl rfl rfl
    (SemiprimeD1StackEuclidGCDExecution.source_run num den)
  · exact ⟨hi,fun _ _=>rfl⟩
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- A literal reused Divider11 call consumes two acquired operands and retains every other actual word. -/
theorem divide_call (den:Bool) (before:Stack→List Bool) (xs ys:List Bool)
    (hi:∀k,before (dividerStack k)=SemiprimeD1StackDivider.payload xs ys [] [] [] [] [] [] [] [] [] k) :
    Runs program (SemiprimeD1StackDividerExecution.executionTime xs ys+1) (.divide den) before (.save den)
      (Function.update (Function.update (Function.update (Function.update before x []) y []) remainder
        (SemiprimeBitDivision.divideLoop xs ys).remainder) quotient (SemiprimeBitDivision.divideLoop xs ys).quotient) :=by
  let start:=SemiprimeD1StackDivider.state (some (.control .start)) none none xs ys [] [] [] [] [] [] [] [] []
  let stop:=SemiprimeD1StackDivider.state none none none [] [] [] [] [] [] []
    (SemiprimeBitDivision.divideLoop xs ys).remainder (SemiprimeBitDivision.divideLoop xs ys).quotient [] []
  have hin:SemiprimeD1StackMultiplierLink.DataRel dividerStack before start.data before:=⟨hi,fun _ _=>rfl⟩
  have h0:=SemiprimeD1StackMultiplierLink.data_update dividerStack divider_injective before start.data before hin (.inr .input) []
  have h1:=SemiprimeD1StackMultiplierLink.data_update dividerStack divider_injective before _ _ h0 (.inr .divisor) []
  have h2:=SemiprimeD1StackMultiplierLink.data_update dividerStack divider_injective before _ _ h1 (.inr .remainder)
    (SemiprimeBitDivision.divideLoop xs ys).remainder
  have h3:=SemiprimeD1StackMultiplierLink.data_update dividerStack divider_injective before _ _ h2 (.inr .quotient)
    (SemiprimeBitDivision.divideLoop xs ys).quotient
  have he:Function.update (Function.update (Function.update (Function.update start.data (.inr .input) [])
      (.inr .divisor) []) (.inr .remainder) (SemiprimeBitDivision.divideLoop xs ys).remainder)
      (.inr .quotient) (SemiprimeBitDivision.divideLoop xs ys).quotient=stop.data:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  rw [he] at h3
  exact SemiprimeD1StackProcedureCallsTrace.included_call program dividerStack Label.divider divider_injective D.code
    (.control .start) (fun _=>rfl) (.divide den) (.save den) rfl (SemiprimeD1StackDividerExecution.executionTime xs ys)
    start stop before _ rfl rfl rfl rfl (SemiprimeD1StackDividerExecution.source_run xs ys) hin h3
end RiemannGaussian.SemiprimeD1StackRationalNormalizeCalls
