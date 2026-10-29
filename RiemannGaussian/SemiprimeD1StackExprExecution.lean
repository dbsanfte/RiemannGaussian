/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprValueStack
import RiemannGaussian.SemiprimeD1StackExprLiteralCall
import RiemannGaussian.SemiprimeD1StackExprMeaning
/-! # Complete actual recursive expression trace
The only semantic premises at the closed entry are original modulus positivity
and original literal validity. Children are ACTUALLY called before their original
execute_bounds facts discharge operator width/canonicality obligations.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackExprExecution
open SemiprimeD1StackExpr SemiprimeD1StackExprWiring SemiprimeD1StackProcedureTrace
open SemiprimeD1StackExprValueStack SemiprimeD1StackExprLiteralCall SemiprimeD1StackExprMeaning
open SemiprimeD1StackExprArithmetic (arithmetic_call)
open SemiprimeMacroEntryBitPrimitives (Expr execute Valid execute_bounds)
open SemiprimeD1StackExprCodec (encode)
open SemiprimeSourceHistogramKeyBits (frame)

/-- Exact actual body transition count, used only as a proof specification.
It is not used by the fixed instruction table or supplied to an executing body. -/
def bodyTime (cached : List Bool) : Expr→ℕ
  | .literal word=>2+(SemiprimeD1StackExprLiteralExecution.readyTime word cached+1)
  | .add a b=>bodyTime cached a+bodyTime cached b+
      SemiprimeD1StackExprArithmetic.time .add (execute cached a).bits (execute cached b).bits cached+21*cached.length+26
  | .sub a b=>bodyTime cached a+bodyTime cached b+
      SemiprimeD1StackExprArithmetic.time .sub (execute cached a).bits (execute cached b).bits cached+21*cached.length+26
  | .mul a b=>bodyTime cached a+bodyTime cached b+
      SemiprimeD1StackExprArithmetic.time .mul (execute cached a).bits (execute cached b).bits cached+21*cached.length+26

/-- The finite physically dispatched operator has the exact body count. -/
theorem bodyTime_node (op : Op) (cached : List Bool) (a b : Expr) :
    bodyTime cached (node op a b)=bodyTime cached a+bodyTime cached b+
      SemiprimeD1StackExprArithmetic.time op (execute cached a).bits (execute cached b).bits cached+21*cached.length+26 := by
  cases op <;> rfl

/-- Actual body traces concatenate with every transition and physical frame retained. -/
theorem chain {m n : ℕ} {pc mid next : Label} {input middle output : Stack→List Bool}
    (h : Runs program m pc input mid middle) (g : Runs program n mid middle next output) :
    Runs program (m+n) pc input next output := runs_trans program m n pc mid next input middle output h g

/-- Internal induction connector for the literal recursive program, not a
runtime body supplier. Both child premises are actual traces of THIS .eval. -/
theorem branch_trace (op : Op) (cached : List Bool) (a b : Expr)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached) (ha : Valid cached a) (hb : Valid cached b)
    (hleft : ∀tail saved,Runs program (bodyTime cached a) .eval
      (bank (encode a tail) cached saved [] [] [] [] []) .returnPC
      (bank tail cached saved (execute cached a).bits [] [] [] []))
    (hright : ∀tail saved,Runs program (bodyTime cached b) .eval
      (bank (encode b tail) cached saved [] [] [] [] []) .returnPC
      (bank tail cached saved (execute cached b).bits [] [] [] []))
    (tail saved : List Bool) :
    Runs program (bodyTime cached (node op a b)) .eval
      (bank (encode (node op a b) tail) cached saved [] [] [] [] []) .returnPC
      (bank tail cached saved (execute cached (node op a b)).bits [] [] [] []) := by
  have h1 := SemiprimeD1StackExprDispatch.operator_tags op (encode a (encode b tail)) cached saved
  have h2 := SemiprimeD1StackRecursiveCallTrace.invoke program (.begin op) .eval .returnPC (.saveLeft op)
    rfl rfl (bodyTime cached a) _ _ (hleft (encode b tail) saved)
  have hA := execute_bounds cached hm a ha
  have h3 := save_left op (encode b tail) cached saved (execute cached a).bits
  have h4 := clear_left op (encode b tail) cached (frame (execute cached a).bits saved) (execute cached a).bits
  have h5 := SemiprimeD1StackRecursiveCallTrace.invoke program (.rightEval op) .eval .returnPC (.copyRight op)
    rfl rfl (bodyTime cached b) _ _ (hright tail (frame (execute cached a).bits saved))
  have hB := execute_bounds cached hm b hb
  have h6 := copy_right op tail cached (frame (execute cached a).bits saved) (execute cached b).bits
  have h7 := clear_right op tail cached (frame (execute cached a).bits saved) (execute cached b).bits
  have h8 := read_left op tail cached saved (execute cached a).bits (execute cached b).bits
  have h9 := check_left op tail cached saved (execute cached a).bits (execute cached b).bits
  have h10 := arithmetic_call op tail cached saved (execute cached a).bits (execute cached b).bits
  rw [arithmetic_original op cached a b hm ha hb] at h10
  have h := chain h1 (chain h2 (chain h3 (chain h4 (chain h5 (chain h6 (chain h7 (chain h8 (chain h9 h10))))))))
  simp only [hA.1,hB.1] at h
  have he : 2+(bodyTime cached a+2+(6*cached.length+5+(cached.length+1+
      (bodyTime cached b+2+(5*cached.length+4+(cached.length+1+(8*cached.length+7+
      (1+(SemiprimeD1StackExprArithmetic.time op (execute cached a).bits (execute cached b).bits cached+1)))))))))=
      bodyTime cached a+bodyTime cached b+
        SemiprimeD1StackExprArithmetic.time op (execute cached a).bits (execute cached b).bits cached+21*cached.length+26 := by omega
  rw [he] at h
  rw [bodyTime_node,encode_node]
  exact h

/-- Complete body refinement for every original valid expression and arbitrary
physical code/saved-value suffixes. No literal, arithmetic or clock answer is supplied. -/
theorem eval_trace (cached : List Bool) (hm : 0<SemiprimeBitArithmetic.bitValue cached)
    (expr : Expr) (hv : Valid cached expr) (tail saved : List Bool) :
    Runs program (bodyTime cached expr) .eval (bank (encode expr tail) cached saved [] [] [] [] [])
      .returnPC (bank tail cached saved (execute cached expr).bits [] [] [] []) := by
  induction expr generalizing tail saved with
  | literal word=>
    exact chain (SemiprimeD1StackExprDispatch.literal_tags (frame word tail) cached saved)
      (literal_call word tail cached saved)
  | add a b ia ib=>exact branch_trace .add cached a b hm hv.1 hv.2 (ia hv.1) (ib hv.2) tail saved
  | sub a b ia ib=>exact branch_trace .sub cached a b hm hv.1 hv.2 (ia hv.1) (ib hv.2) tail saved
  | mul a b ia ib=>exact branch_trace .mul cached a b hm hv.1 hv.2 (ia hv.1) (ib hv.2) tail saved

/-- Exact clean output bank; code tail and original raw modulus are retained. -/
def finalData (cached : List Bool) (expr : Expr) (tail : List Bool) : Stack→List Bool :=
  bank tail cached [] (execute cached expr).bits [] [] [] []
/-- Whole original-prefix evaluator halt, with every real return frame cleared. -/
def done (cached : List Bool) (expr : Expr) (tail : List Bool) : C.State Stack Label :=
  ⟨none,none,none,finalData cached expr tail,[]⟩
/-- Exact whole evaluator count, including its top real call/return and halt. -/
def totalTime (cached : List Bool) (expr : Expr) : ℕ := bodyTime cached expr+3

/-- CLOSED source execution: the program consumes only physical syntax/cache,
returns exactly original execute bits, preserves the actual tail/cache, and
clears every saved operand, parser/arith work cell and actual return frame. -/
theorem source_run (cached : List Bool) (expr : Expr) (tail : List Bool)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached) (hv : Valid cached expr) :
    C.run program (totalTime cached expr) (initial (encode expr tail) cached)=some (done cached expr tail) := by
  have hb := SemiprimeD1StackRecursiveCallTrace.invoke program .start .eval .returnPC .done rfl rfl
    (bodyTime cached expr) _ _ (eval_trace cached hm expr hv tail [])
  obtain ⟨finish,hfinish,hout⟩ := hb [] (initial (encode expr tail) cached) ⟨rfl,rfl,rfl⟩
  have hh := halt_run program .done rfl (finalData cached expr tail) [] finish hout
  rw [totalTime,show bodyTime cached expr+3=(bodyTime cached expr+2)+1 by omega,
    SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
  rfl
end RiemannGaussian.SemiprimeD1StackExprExecution
