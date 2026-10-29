/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackLeafState
/-! # Actual closed assignment-product call inside the leaf sum -/
set_option autoImplicit false
set_option synthInstance.maxSize 131072
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackLeafProduct
open SemiprimeD1StackLeaf SemiprimeD1StackLeafState
open SemiprimeD1StackProcedureTrace (Runs)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)

/-- One real nested procedure invocation executes the whole literal vertex
product. All original tensor entries are read inside that procedure. -/
theorem product_call (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (p : PS.Values) (v : Values)
    (hvertices : p .vertices=SemiprimeD1StackVertexProduct.records vertices)
    (hreader : p .reader=[]) (hleft : p .left=[]) (hprod : p .product=[])
    (hports : p .ports=[]) (htable : p .table=[]) (hvalid : p .valid=[]) (hout : p .result=[])
    (haxes : p .axes=vectorBits (ctx.axes.map unary))
    (hw : (p .width).length=ctx.precision) (hr : p .rank=unary ctx.rank) :
    ∃ m ≤ SemiprimeD1StackVertexProductExecution.preparedBudget ctx vertices p+2,
      Runs program m .callProduct (data p v) .callAdd
        (data (Function.update p .product
          (vectorBits (SemiprimeD1TensorTapeLeaf.evaluateAssignment ctx vertices (p .assignment)).words)) v) := by
  obtain ⟨m,hm,hs⟩:=SemiprimeD1StackVertexProductExecution.prepared_source ctx hp vertices p
    hvertices hreader hleft hprod hports htable hvalid hout haxes hw hr
  refine ⟨m+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program productStack Label.product
    (by intro a b h; exact Sum.inl.inj h) P.program .prepared (fun _=>rfl)
    .callProduct .callAdd rfl m
    (⟨some .prepared,none,none,PS.data p,[]⟩:SemiprimeD1StackCalls.State P.Stack P.Label)
    (⟨none,none,none,PS.data (Function.update p .product
      (vectorBits (SemiprimeD1TensorTapeLeaf.evaluateAssignment ctx vertices (p .assignment)).words)),[]⟩:
      SemiprimeD1StackCalls.State P.Stack P.Label)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hs
  · constructor
    · intro k; rfl
    · intro k hk; rfl
  · constructor
    · intro k; rfl
    · intro k hk
      cases k with
      | inl k => exact (hk k rfl).elim
      | inr k => rfl

end RiemannGaussian.SemiprimeD1StackLeafProduct
