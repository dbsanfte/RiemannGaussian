/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackLeafProduct
/-! # Actual dense summation of reached physical assignment products -/
set_option autoImplicit false
set_option synthInstance.maxSize 131072
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackLeafAddition
open SemiprimeD1StackLeaf SemiprimeD1StackLeafState
open SemiprimeD1StackProcedureTrace (Runs)
open SemiprimeD1TensorTapeCodec (vectorBits)

/-- Exact operand/cache/work projection of the included dense-adder program. -/
theorem add_project (p : PS.Values) (v : Values) (k : A.Stack) :
    data p v (addStack k)=SemiprimeD1StackJetAdd.store [] [] [] [] (p .width) []
      (p .product) (v .sum) (p .rank) [] [] (v .sumResult) [] [] [] k := by
  fin_cases k
  all_goals first
    | exact data_product_get p v .width
    | exact data_product_get p v .rank
    | exact data_product_get p v .product
    | exact data_get p v .sum
    | exact data_get p v .sumResult
    | rfl

/-- The actual reached product and sum are added by real scalar arithmetic;
both operands are physically consumed and only the new sum buffer is filled. -/
theorem add_call (ctx : SemiprimeD1JetAxes.Context) (p : PS.Values) (v : Values)
    (a b : List (List Bool)) (ha : p .product=vectorBits a) (hb : v .sum=vectorBits b)
    (hout : v .sumResult=[]) (hw : (p .width).length=ctx.precision) (hr : (p .rank).length=ctx.rank) :
    Runs program (SemiprimeD1StackJetAddExecution.totalTime (p .width) (p .rank) a b+1)
      .callAdd (data p v) .copySum
      (data (Function.update p .product [])
        (Function.update (Function.update v .sum []) .sumResult
          (vectorBits (SemiprimeD1JetRingBits.add ctx a b).words))) := by
  apply SemiprimeD1StackProcedureInclusion.included_call program addStack Label.add addStack_injective
    A.program .start (fun _=>rfl) .callAdd .copySum rfl _
    (SemiprimeD1StackJetAdd.state (some .start) none none [] [] [] [] (p .width) []
      (vectorBits a) (vectorBits b) (p .rank) [] [] [] [] [] [])
    (SemiprimeD1StackJetAdd.state none none none [] [] [] [] (p .width) []
      [] [] (p .rank) [] [] (vectorBits (SemiprimeD1JetRingBits.add ctx a b).words) [] [] [])
  · rfl
  · rfl
  · rfl
  · rfl
  · simpa only [SemiprimeD1StackJetAddExecution.rows_eq_original ctx _ _ a b hw hr] using
      SemiprimeD1StackJetAddExecution.source_run (p .width) (p .rank) a b
  · constructor
    · intro k
      rw [add_project]
      simp only [SemiprimeD1StackJetAdd.state,ha,hb,hout]
    · intro k hk; rfl
  · constructor
    · intro k
      rw [add_project]
      fin_cases k <;> simp [SemiprimeD1StackJetAdd.state,SemiprimeD1StackJetAdd.store,
        SemiprimeD1StackJetScalarAdd.store]
    · intro k hk
      have hp : k ≠ productStack (PS.address .product) := fun he=>hk (.inr .leftTape) he.symm
      have hs : k ≠ address .sum := fun he=>hk (.inr .rightTape) he.symm
      have ho : k ≠ address .sumResult := fun he=>hk (.inr .output) he.symm
      rw [data_update,data_update,data_product_update]
      simp only [Function.update_of_ne hp,Function.update_of_ne hs,Function.update_of_ne ho]

end RiemannGaussian.SemiprimeD1StackLeafAddition
