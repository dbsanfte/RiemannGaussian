/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprWiring
/-! # The complete evaluator's actual arithmetic procedure calls
These traces require only actual operand/cache bytes, not a result, height,
canonicality or clock supplier. Original canonicality is used later for meaning.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackExprArithmetic
open SemiprimeD1StackExpr SemiprimeD1StackExprWiring SemiprimeD1StackProcedureTrace

/-- Actual complete add call; both operator inputs are consumed and all private work clears. -/
theorem add_call (code cached saved left right : List Bool) :
    Runs program (SemiprimeD1StackResidueAddExecution.totalTime left right cached+1)
      (.applyOp .add) (bank code cached saved [] left right [] []) .returnPC
      (bank code cached saved (SemiprimeD1StackResidueAddExecution.residue left right cached) [] [] [] []) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program addStack Label.addition add_injective
    Add.program .start (fun _=>rfl) (.applyOp .add) .returnPC rfl
    (SemiprimeD1StackResidueAddExecution.totalTime left right cached)
    (Add.initial left right cached) (SemiprimeD1StackResidueAddExecution.done left right cached) _ _ rfl rfl rfl rfl
    (SemiprimeD1StackResidueAddExecution.source_run left right cached)
  · constructor
    · intro k
      rcases k with k|k
      · cases k <;> rfl
      · rcases k with k|k
        · rcases k with k|k <;> cases k <;> rfl
        · cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k
      rcases k with k|k
      · cases k <;> rfl
      · rcases k with k|k
        · rcases k with k|k <;> cases k <;> rfl
        · cases k <;> rfl
    · intro k hk
      cases k <;> first | rfl | exact (hk addLeft rfl).elim | exact (hk addRight rfl).elim | exact (hk Add.output rfl).elim

/-- Actual complete sub call; both operator inputs are consumed and all private work clears. -/
theorem sub_call (code cached saved left right : List Bool) :
    Runs program (SemiprimeD1StackResidueSubExecution.totalTime left right cached+1)
      (.applyOp .sub) (bank code cached saved [] left right [] []) .returnPC
      (bank code cached saved (SemiprimeD1StackResidueSubExecution.residue left right cached) [] [] [] []) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program subStack Label.subtraction sub_injective
    Sub.program .start (fun _=>rfl) (.applyOp .sub) .returnPC rfl
    (SemiprimeD1StackResidueSubExecution.totalTime left right cached)
    (Sub.initial left right cached) (SemiprimeD1StackResidueSubExecution.done left right cached) _ _ rfl rfl rfl rfl
    (SemiprimeD1StackResidueSubExecution.source_run left right cached)
  · constructor
    · intro k
      rcases k with k|k
      · cases k <;> rfl
      · rcases k with k|k
        · cases k <;> rfl
        · rcases k with k|k
          · rcases k with k|k <;> cases k <;> rfl
          · cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k
      rcases k with k|k
      · cases k <;> rfl
      · rcases k with k|k
        · cases k <;> rfl
        · rcases k with k|k
          · rcases k with k|k <;> cases k <;> rfl
          · cases k <;> rfl
    · intro k hk
      cases k <;> first | rfl | exact (hk subLeft rfl).elim | exact (hk subRight rfl).elim | exact (hk Sub.output rfl).elim

/-- Actual complete mul call; both operator inputs are consumed and all private work clears. -/
theorem mul_call (code cached saved left right : List Bool) :
    Runs program (SemiprimeD1StackResidueMulExecution.totalTime left right cached+1)
      (.applyOp .mul) (bank code cached saved [] left right [] []) .returnPC
      (bank code cached saved (SemiprimeD1StackResidueMulExecution.residue left right cached) [] [] [] []) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program mulStack Label.multiplication mul_injective
    Mul.program .start (fun _=>rfl) (.applyOp .mul) .returnPC rfl
    (SemiprimeD1StackResidueMulExecution.totalTime left right cached)
    (Mul.initial left right cached) (SemiprimeD1StackResidueMulExecution.done left right cached) _ _ rfl rfl rfl rfl
    (SemiprimeD1StackResidueMulExecution.source_run left right cached)
  · constructor
    · intro k
      rcases k with k|k
      · rcases k with k|k
        · cases k <;> rfl
        · rcases k with k|k
          · fin_cases k <;> rfl
          · cases k <;> rfl
      · rcases k with k|k
        · rcases k with k|k <;> cases k <;> rfl
        · cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k
      rcases k with k|k
      · rcases k with k|k
        · cases k <;> rfl
        · rcases k with k|k
          · fin_cases k <;> rfl
          · cases k <;> rfl
      · rcases k with k|k
        · rcases k with k|k <;> cases k <;> rfl
        · cases k <;> rfl
    · intro k hk
      cases k <;> first | rfl | exact (hk mulLeft rfl).elim | exact (hk mulRight rfl).elim | exact (hk Mul.output rfl).elim

/-- Actual executed arithmetic word, as a proof-side specification of returned cells. -/
def word : Op→List Bool→List Bool→List Bool→List Bool
  | .add,left,right,cached=>SemiprimeD1StackResidueAddExecution.residue left right cached
  | .sub,left,right,cached=>SemiprimeD1StackResidueSubExecution.residue left right cached
  | .mul,left,right,cached=>SemiprimeD1StackResidueMulExecution.residue left right cached
/-- Actual complete component trace length, never used by the instruction table. -/
def time : Op→List Bool→List Bool→List Bool→ℕ
  | .add,left,right,cached=>SemiprimeD1StackResidueAddExecution.totalTime left right cached
  | .sub,left,right,cached=>SemiprimeD1StackResidueSubExecution.totalTime left right cached
  | .mul,left,right,cached=>SemiprimeD1StackResidueMulExecution.totalTime left right cached

/-- Every operator uses its own literal complete physical arithmetic trace. -/
theorem arithmetic_call (op : Op) (code cached saved left right : List Bool) :
    Runs program (time op left right cached+1) (.applyOp op)
      (bank code cached saved [] left right [] []) .returnPC
      (bank code cached saved (word op left right cached) [] [] [] []) := by
  cases op
  · exact add_call code cached saved left right
  · exact sub_call code cached saved left right
  · exact mul_call code cached saved left right
end RiemannGaussian.SemiprimeD1StackExprArithmetic
