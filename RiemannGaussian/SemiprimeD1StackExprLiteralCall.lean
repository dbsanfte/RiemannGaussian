/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprWiring
/-! # Actual literal body inclusion without rereading constructor tags -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackExprLiteralCall
open SemiprimeD1StackExpr SemiprimeD1StackExprWiring SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- The literal branch calls the real already-dispatched parser/fitter body.
Its code tail/cache and arbitrary older saved-value suffix remain physical. -/
theorem literal_call (word tail cached saved : List Bool) :
    Runs program (SemiprimeD1StackExprLiteralExecution.readyTime word cached+1)
      .literalCall (bank (frame word tail) cached saved [] [] [] [] []) .returnPC
      (bank tail cached saved (SemiprimeMacroEntryBitPrimitives.execute cached (.literal word)).bits [] [] [] []) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program literalStack Label.literal literal_injective
    Lit.program (Lit.ctl .fieldCall) (fun _=>rfl) .literalCall .returnPC rfl
    (SemiprimeD1StackExprLiteralExecution.readyTime word cached)
    (⟨some (Lit.ctl .fieldCall),none,none,SemiprimeD1StackExprLiteralExecution.beforeField word tail cached,[]⟩:
      C.State Lit.Stack Lit.Label)
    (SemiprimeD1StackExprLiteralExecution.done word tail cached) _ _ rfl rfl rfl rfl
    (SemiprimeD1StackExprLiteralExecution.ready_run word tail cached)
  · constructor
    · intro k
      rcases k with k|k
      · fin_cases k <;> rfl
      · rcases k with k|k <;> cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k
      rcases k with k|k
      · fin_cases k <;> rfl
      · rcases k with k|k <;> cases k <;> rfl
    · intro k hk
      cases k <;> first | rfl | exact (hk Lit.inputCode rfl).elim | exact (hk Lit.output rfl).elim
end RiemannGaussian.SemiprimeD1StackExprLiteralCall
