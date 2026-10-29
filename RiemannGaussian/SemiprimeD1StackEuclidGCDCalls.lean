/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEuclidGCDEncoding
import RiemannGaussian.SemiprimeD1StackEuclidGCDPrimitives
/-! # Real complete Divider11 call inside the eighteen-role Euclid bank -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackEuclidGCDCalls
open SemiprimeD1StackEuclidGCD SemiprimeD1StackEuclidGCDEncoding
open SemiprimeD1StackProcedureTrace
namespace P
export SemiprimeD1StackEuclidGCDPrimitives (join copy_call reverse_call trim_call push_run pop_run peek_run drain_loop)
end P
/-- Real restoring division consumes both actual current operands, returns its two literal output words,
and preserves every original/fuel/backup/caller word and every actual outer return. -/
theorem divide_call (left right fuel xs ys saved:List Bool) :
    Runs program (SemiprimeD1StackDividerExecution.executionTime xs ys+1) .divide
      (bank {originalLeft:=left,originalRight:=right,fuel:=fuel,x:=xs,y:=ys,next:=saved}) .clearQuotient
      (bank {originalLeft:=left,originalRight:=right,fuel:=fuel,next:=saved, remainder:=(SemiprimeBitDivision.divideLoop xs ys).remainder, quotient:=(SemiprimeBitDivision.divideLoop xs ys).quotient}) :=by
  let before:=bank {originalLeft:=left,originalRight:=right,fuel:=fuel,x:=xs,y:=ys,next:=saved}
  let start:=SemiprimeD1StackDivider.state (some (.control .start)) none none xs ys [] [] [] [] [] [] [] [] []
  let stop:=SemiprimeD1StackDivider.state none none none [] [] [] [] [] [] []
    (SemiprimeBitDivision.divideLoop xs ys).remainder (SemiprimeBitDivision.divideLoop xs ys).quotient [] []
  have hi:SemiprimeD1StackMultiplierLink.DataRel dividerStack before start.data before:=by
    constructor
    · intro k;rcases k with k|k <;> cases k <;> rfl
    · intro k _;rfl
  have h0:=SemiprimeD1StackMultiplierLink.data_update dividerStack divider_injective before start.data before hi (.inr .input) []
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
  have h:=SemiprimeD1StackProcedureCallsTrace.included_call program dividerStack Label.divider divider_injective D.code (.control .start)
    (fun _=>rfl) .divide .clearQuotient rfl (SemiprimeD1StackDividerExecution.executionTime xs ys)
    start stop before _ rfl rfl rfl rfl (SemiprimeD1StackDividerExecution.source_run xs ys) hi h3
  change Runs _ _ _ (bank _) _ (Function.update (Function.update (Function.update (Function.update (bank _)
    (dividerStack (.inr .input)) []) (dividerStack (.inr .divisor)) [])
    (dividerStack (.inr .remainder)) _) (dividerStack (.inr .quotient)) _) at h
  rw [update_x,update_y,update_remainder,update_quotient] at h
  exact h
end RiemannGaussian.SemiprimeD1StackEuclidGCDCalls
