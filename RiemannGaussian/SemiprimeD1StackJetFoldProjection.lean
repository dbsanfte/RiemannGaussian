/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetFoldState
/-! # Literal real-operator bank projections of the111-role fold store -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackJetFoldProjection
open SemiprimeD1StackJetFold SemiprimeD1StackJetFoldState
/-- The actual multiplier operands/caches; no target or coefficient answer is present. -/
def cache (v:Values):SemiprimeD1StackJetPointExecution.Cache:=
  ⟨v .left,v .product,v .axes,v .width,v .rank,[]⟩
/-- Every dedicated context work/shadow role is empty at an actual fold boundary. -/
theorem context_work_empty (v:Values) (k:X.Stack):data v (contextWork k)=[]:=by
  apply data_other
  intro s;cases s <;> intro h <;> cases h
/-- Every dedicated unit work/shadow role is empty at an actual fold boundary. -/
theorem unit_work_empty (v:Values) (k:U.Stack):data v (unitWork k)=[]:=by
  apply data_other
  intro s;cases s <;> intro h <;> cases h
/-- Every dedicated addition work/shadow role is empty at an actual fold boundary. -/
theorem add_work_empty (v:Values) (k:A.Stack):data v (addWork k)=[]:=by
  apply data_other
  intro s;cases s <;> intro h <;> cases h
/-- The actual full multiplication bank is exactly the frozen clean loop boundary. -/
theorem data_main (v:Values) (k:M.Stack):
    data v (main k)=SemiprimeD1StackJetMulExecution.data (cache v) [] [] (v .result) k:=by
  fin_cases k <;> first
    | exact data_get v .axes
    | exact data_get v .rank
    | exact data_get v .width
    | exact data_get v .left
    | exact data_get v .product
    | exact data_get v .result
    | (apply data_other;intro s;cases s <;> decide)
/-- The actual unit bank has private empty seed operands and the real shared context/product words. -/
theorem data_unit (v:Values) (k:U.Stack):
    data v (unitStack k)=SemiprimeD1StackJetUnit.bank (v .width) (v .rank) [] [] (v .product) k:=by
  fin_cases k <;> first
    | exact data_get v .width
    | exact data_get v .rank
    | exact data_get v .product
    | exact unit_work_empty v _
/-- The actual adder receives the actual product and saved tail sum, with all its work roles empty. -/
theorem data_add (v:Values) (k:A.Stack):
    data v (addStack k)=A.store [] [] [] [] (v .width) [] (v .product) (v .tailSum)
      (v .rank) [] [] (v .sum) [] [] [] k:=by
  fin_cases k <;> first
    | exact data_get v .width
    | exact data_get v .rank
    | exact data_get v .product
    | exact data_get v .tailSum
    | exact data_get v .sum
    | exact add_work_empty v _
/-- Actual context bank view, with physically retained input/rank/precision words and empty private work. -/
def contextBank (v:Values):X.Stack→List Bool:=SemiprimeD1StackJetContext.bank (v .axes) (v .precision)
  (SemiprimeD1StackJetContextExecution.ready (v .rank) [] [])
  (SemiprimeD1StackAdder.store [] [] [] (v .width))
/-- The actual context cache aliases all four input/output words and preserves every private empty role. -/
theorem data_context (v:Values) (k:X.Stack):data v (contextStack k)=contextBank v k:=by
  fin_cases k <;> first
    | exact data_get v .axes
    | exact data_get v .precision
    | exact data_get v .rank
    | exact data_get v .width
    | exact context_work_empty v _
end RiemannGaussian.SemiprimeD1StackJetFoldProjection
