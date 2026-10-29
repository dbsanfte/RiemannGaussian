/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexProductMoves
/-! # Exact physical component views of the vertex-product register invariant -/
set_option autoImplicit false
set_option synthInstance.maxSize 65536
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackVertexProductProjection
open SemiprimeD1StackVertexProduct SemiprimeD1StackVertexProductState

/-- Dedicated context workspace is never a hidden live caller register. -/
theorem context_work_other (k : X.Stack) : ∀s,contextWork k ≠ address s := by
  intro s
  cases s <;> simp [contextWork,address,axes,rank,width,left,product,result,main,aux]
/-- Dedicated unit workspace is never a hidden live caller register. -/
theorem unit_work_other (k : U.Stack) : ∀s,unitWork k ≠ address s := by
  intro s
  cases s <;> simp [unitWork,address,axes,rank,width,left,product,result,main,aux]
/-- Dedicated vertex workspace is never a hidden live caller register. -/
theorem vertex_work_other (k : V.Stack) : ∀s,vertexWork k ≠ address s := by
  intro s
  cases s <;> simp [vertexWork,address,axes,rank,width,left,product,result,main,aux]
/-- Physical field-parser scratch contains no discarded caller word. -/
theorem field_work_other : ∀s,aux .fieldScratch ≠ address s := by decide

/-- Actual context supplier reads original headers and writes the shared caches. -/
theorem context_project (v : Values) (k : X.Stack) :
    data v (contextStack k)=
      if k=X.axesCache then v .axes else if k=X.rankCache then v .rank else if k=X.widthCache then v .width
      else if k=X.precisionBits then v .precision else [] := by
  unfold contextStack
  split_ifs
  · exact data_get v .axes
  · exact data_get v .rank
  · exact data_get v .width
  · exact data_get v .precision
  · exact data_other v (contextWork k) (context_work_other k)

/-- Actual unit supplier shares the already acquired arithmetic caches. -/
theorem unit_project (v : Values) (k : U.Stack) :
    data v (unitStack k)=
      if k=U.widthCache then v .width else if k=U.rankCache then v .rank else if k=U.output then v .result
      else if k=Sum.inr SemiprimeD1StackJetAdd.Aux.leftTape then v .left
      else if k=Sum.inr SemiprimeD1StackJetAdd.Aux.rightTape then v .product else [] := by
  unfold unitStack
  split_ifs
  · exact data_get v .width
  · exact data_get v .rank
  · exact data_get v .result
  · exact data_get v .left
  · exact data_get v .product
  · exact data_other v (unitWork k) (unit_work_other k)

/-- Actual vertex read consumes parsed fields and writes the multiplier operand. -/
theorem vertex_project (v : Values) (k : V.Stack) :
    data v (vertexStack k)=match k with
      | .ports => v .ports
      | .assignment => v .assignment
      | .tableTape => v .table
      | .output => v .left
      | _ => [] := by
  cases k with
  | ports => exact data_get v .ports
  | assignment => exact data_get v .assignment
  | tableTape => exact data_get v .table
  | output => exact data_get v .left
  | reader => exact data_other v _ (vertex_work_other .reader)
  | scratch => exact data_other v _ (vertex_work_other .scratch)
  | accumulator => exact data_other v _ (vertex_work_other .accumulator)
  | path => exact data_other v _ (vertex_work_other .path)
  | tasks => exact data_other v _ (vertex_work_other .tasks)

/-- Actual field read shares one stream and writes exactly the requested field. -/
theorem field_project (v : Values) (table : Bool) (k : F.Stack) :
    data v (fieldStack table k)=match k with
      | .inl .input => v .reader
      | .inl .scratch => []
      | .inl .output => if table then v .table else v .ports
      | .inr _ => v .valid := by
  rcases k with k|k
  · cases k with
    | input => exact data_get v .reader
    | scratch => exact data_other v _ field_work_other
    | output =>
      cases table with
      | false => exact data_get v .ports
      | true => exact data_get v .table
  · cases k
    exact data_get v .valid

/-- Declarative view of the six actual multiplier cache/result registers. -/
def multiplierCache (v : Values) : SemiprimeD1StackJetPointExecution.Cache :=
  ⟨v .left,v .product,v .axes,v .width,v .rank,[]⟩

/-- The actual multiplier receives precisely its physical cached vectors and
context, and no route, selected coefficient or product-answer argument. -/
theorem main_project (v : Values) (k : M.Stack) :
    data v (main k)=SemiprimeD1StackJetMulExecution.data (multiplierCache v) [] [] (v .result) k := by
  fin_cases k <;> simp [data,address,axes,rank,width,left,product,result,main,aux,
    SemiprimeD1StackJetPoint.aux,SemiprimeD1StackJetPoint.precision,SemiprimeD1StackJetPoint.mulStack,
    SemiprimeD1StackJetMul.output,SemiprimeD1StackJetMulExecution.data,SemiprimeD1StackJetMulExecution.indexed,
    SemiprimeD1StackJetPointExecution.resting,multiplierCache]

end RiemannGaussian.SemiprimeD1StackVertexProductProjection
