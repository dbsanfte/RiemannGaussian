/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprEquality
/-! # Complete actual two-expression equality trace -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackExprEqualityExecution
open SemiprimeD1StackExprEquality SemiprimeD1StackProcedureTrace
open SemiprimeMacroEntryBitPrimitives (Expr execute Valid residueEqualityBits)
open SemiprimeD1StackExprCodec (encode)
/-- Exact original accepted Boolean, specifying the actual returned output cell. -/
def answer (cached : List Bool) (left right : Expr) : Bool := (residueEqualityBits cached left right).accepted
/-- First actual evaluator result and still encoded second expression. -/
def afterLeft (cached : List Bool) (left right : Expr) (tail : List Bool) : Stack→List Bool :=
  store (SemiprimeD1StackExprExecution.finalData cached left (encode right tail)) (Q.store [] [] [] []) []
/-- The actual first result is copied to a separate physical left operand. -/
def afterCopy (cached : List Bool) (left right : Expr) (tail : List Bool) : Stack→List Bool :=
  store (SemiprimeD1StackExprExecution.finalData cached left (encode right tail))
    (Q.store (execute cached left).bits [] [] []) []
/-- The first result source is physically erased before the second evaluation. -/
def beforeRight (cached : List Bool) (left right : Expr) (tail : List Bool) : Stack→List Bool :=
  store (E.input (encode right tail) cached) (Q.store (execute cached left).bits [] [] []) []
/-- Both ACTUAL evaluator results are now the comparator's physical operands. -/
def beforeCompare (cached : List Bool) (left right : Expr) (tail : List Bool) : Stack→List Bool :=
  store (SemiprimeD1StackExprExecution.finalData cached right tail) (Q.store (execute cached left).bits [] [] []) []
/-- Only unconsumed code, raw cache and actual accepted Boolean remain. -/
def finalData (cached : List Bool) (left right : Expr) (tail : List Bool) : Stack→List Bool :=
  store (E.input tail cached) (Q.store [] [] [] [answer cached left right]) []
/-- Exact clean whole caller halt. -/
def done (cached : List Bool) (left right : Expr) (tail : List Bool) : C.State Stack Label :=
  ⟨none,none,none,finalData cached left right tail,[]⟩
/-- Actual complete transition count, never an executing clock supplier. -/
def totalTime (cached : List Bool) (left right : Expr) : ℕ :=
  (SemiprimeD1StackExprExecution.totalTime cached left+1)+
    (5*(execute cached left).bits.length+4)+((execute cached left).bits.length+1)+
    (SemiprimeD1StackExprExecution.totalTime cached right+1)+
    (SemiprimeD1StackWordEqualExecution.executionTime (execute cached left).bits (execute cached right).bits+1)+1

/-- The first real whole evaluator leaves the second encoded prefix untouched. -/
theorem evaluate_left (cached : List Bool) (left right : Expr) (tail : List Bool)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached) (hv : Valid cached left) :
    Runs program (SemiprimeD1StackExprExecution.totalTime cached left+1) .start
      (input (encode left (encode right tail)) cached) .copyLeft (afterLeft cached left right tail) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Sum.inl Label.expression Sum.inl_injective
    E.program .start (fun _=>rfl) .start .copyLeft rfl (SemiprimeD1StackExprExecution.totalTime cached left)
    (E.initial (encode left (encode right tail)) cached)
    (SemiprimeD1StackExprExecution.done cached left (encode right tail)) _ _ rfl rfl rfl rfl
    (SemiprimeD1StackExprExecution.source_run cached left (encode right tail) hm hv)
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · rfl

/-- Left-result saving is a complete actual Copy call, not a decoded assignment. -/
theorem copy_left (cached : List Bool) (left right : Expr) (tail : List Bool) :
    Runs program (5*(execute cached left).bits.length+4) .copyLeft (afterLeft cached left right tail)
      .clearLeft (afterCopy cached left right tail) := by
  apply included_call program copyStack Label.copy copy_injective SemiprimeD1StackCopy.code 0
    (fun _=>rfl) .copyLeft .clearLeft rfl (5*(execute cached left).bits.length+3)
    (SemiprimeD1StackCopy.state 0 none (execute cached left).bits [] [])
    (SemiprimeD1StackCopy.done (execute cached left).bits (execute cached left).bits)
    _ _ rfl rfl (by simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words (execute cached left).bits [] none)
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · cases k <;> first | rfl | exact (hk 1 rfl).elim
        · cases k;rfl

/-- Every source-result cell is physically drained before the next whole expression. -/
theorem clear_left (cached : List Bool) (left right : Expr) (tail : List Bool) :
    Runs program ((execute cached left).bits.length+1) .clearLeft (afterCopy cached left right tail)
      .evaluateRight (beforeRight cached left right tail) := by
  have h := SemiprimeD1StackPhysicalLoops.drain program .clearLeft .evaluateRight (.inl .result) rfl
    (beforeRight cached left right tail) (execute cached left).bits
  have hi : Function.update (beforeRight cached left right tail) (.inl .result) (execute cached left).bits=
      afterCopy cached left right tail := by
    funext k
    rcases k with k|k
    · cases k <;> rfl
    · rcases k with k|k <;> cases k <;> rfl
  have ho : Function.update (beforeRight cached left right tail) (.inl .result) []=
      beforeRight cached left right tail := Function.update_eq_self _ _
  rw [hi,ho] at h
  exact h

/-- The second real evaluator consumes the retained second prefix; saved left bytes persist. -/
theorem evaluate_right (cached : List Bool) (left right : Expr) (tail : List Bool)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached) (hv : Valid cached right) :
    Runs program (SemiprimeD1StackExprExecution.totalTime cached right+1) .evaluateRight
      (beforeRight cached left right tail) .compare (beforeCompare cached left right tail) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Sum.inl Label.expression Sum.inl_injective
    E.program .start (fun _=>rfl) .evaluateRight .compare rfl (SemiprimeD1StackExprExecution.totalTime cached right)
    (E.initial (encode right tail) cached) (SemiprimeD1StackExprExecution.done cached right tail)
    _ _ rfl rfl rfl rfl (SemiprimeD1StackExprExecution.source_run cached right tail hm hv)
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · rfl

/-- The complete actual numeric comparator consumes both real evaluated words. -/
theorem compare_results (cached : List Bool) (left right : Expr) (tail : List Bool) :
    Runs program (SemiprimeD1StackWordEqualExecution.executionTime (execute cached left).bits (execute cached right).bits+1)
      .compare (beforeCompare cached left right tail) .done (finalData cached left right tail) := by
  have hr := SemiprimeD1StackWordEqualExecution.source_run (execute cached left).bits (execute cached right).bits none
  rw [SemiprimeD1StackWordEqualBounds.original_answer] at hr
  apply included_call program equalStack Label.equality equal_injective Q.code .loop (fun _=>rfl)
    .compare .done rfl (SemiprimeD1StackWordEqualExecution.executionTime (execute cached left).bits (execute cached right).bits)
    (Q.state (some .loop) none (execute cached left).bits (execute cached right).bits [])
    (Q.state none none [] [] [answer cached left right]) _ _ rfl rfl hr
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · cases k <;> first | rfl | exact (hk .right rfl).elim
      · rcases k with k|k
        · cases k <;> first | rfl | exact (hk .left rfl).elim | exact (hk .output rfl).elim
        · cases k;rfl

/-- CLOSED original scalar equality: actual two Expr evaluations and real word
comparison, preserving physical tail/cache and clearing every operand/work/frame. -/
theorem source_run (cached : List Bool) (left right : Expr) (tail : List Bool)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached) (hl : Valid cached left) (hr : Valid cached right) :
    C.run program (totalTime cached left right) (initial (encode left (encode right tail)) cached)=
      some (done cached left right tail) := by
  have h1 := runs_trans program _ _ _ _ _ _ _ _ (evaluate_left cached left right tail hm hl) (copy_left cached left right tail)
  have h2 := runs_trans program _ _ _ _ _ _ _ _ h1 (clear_left cached left right tail)
  have h3 := runs_trans program _ _ _ _ _ _ _ _ h2 (evaluate_right cached left right tail hm hr)
  have h4 := runs_trans program _ _ _ _ _ _ _ _ h3 (compare_results cached left right tail)
  obtain ⟨finish,hfinish,hout⟩ := h4 [] (initial (encode left (encode right tail)) cached) ⟨rfl,rfl,rfl⟩
  have hh := halt_run program .done rfl (finalData cached left right tail) [] finish hout
  rw [totalTime,SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
  rfl
end RiemannGaussian.SemiprimeD1StackExprEqualityExecution
