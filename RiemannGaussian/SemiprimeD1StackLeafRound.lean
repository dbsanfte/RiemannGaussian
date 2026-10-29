/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackLeafMoves
/-! # One actual assignment-product and dense-sum round -/
set_option autoImplicit false
set_option synthInstance.maxSize 131072
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackLeafRound
open SemiprimeD1StackLeaf SemiprimeD1StackLeafState SemiprimeD1StackLeafMoves
open SemiprimeD1StackProcedureTrace (Runs runs_trans)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)

/-- Derived sum of the actual parser, product, adder, copy and cleanup costs. -/
def roundBudget (ctx : SemiprimeD1JetAxes.Context) (vertices : List SemiprimeD1LeafCounter.Vertex)
    (p : PS.Values) (word : List Bool) (acc : List (List Bool)) : ℕ :=
  let entry:=(SemiprimeD1TensorTapeLeaf.evaluateAssignment ctx vertices word).words
  let out:=vectorBits (SemiprimeD1JetRingBits.add ctx entry acc).words
  8*word.length+8+(SemiprimeD1StackVertexProductExecution.preparedBudget ctx vertices
    (Function.update p .assignment word)+2)+
  (SemiprimeD1StackJetAddExecution.totalTime (p .width) (p .rank) entry acc+1)+
  (5*out.length+4)+(out.length+1)+(word.length+1)

/-- One real assignment record is parsed, its literal vertex tables multiplied,
and its result added to the actual reached sum. No semantic answer is an input. -/
theorem round_run (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (p : PS.Values) (v : Values)
    (word tail : List Bool) (acc : List (List Bool))
    (hcatalogue : v .catalogue=SemiprimeSourceHistogramKeyBits.frame word tail)
    (hvertices : p .vertices=SemiprimeD1StackVertexProduct.records vertices)
    (hreader : p .reader=[]) (hleft : p .left=[]) (hprod : p .product=[])
    (hports : p .ports=[]) (htable : p .table=[]) (hvalid : p .valid=[]) (hout : p .result=[])
    (hassignment : p .assignment=[]) (hflag : v .valid=[]) (hsum : v .sum=vectorBits acc)
    (hsout : v .sumResult=[]) (haxes : p .axes=vectorBits (ctx.axes.map unary))
    (hw : (p .width).length=ctx.precision) (hr : p .rank=unary ctx.rank) :
    ∃ m ≤ roundBudget ctx vertices p word acc, Runs program m .parse (data p v) .catalogueTag
      (data p (Function.update (Function.update v .catalogue tail) .sum
        (vectorBits (SemiprimeD1JetRingBits.add ctx
          (SemiprimeD1TensorTapeLeaf.evaluateAssignment ctx vertices word).words acc).words))) := by
  let p1:=Function.update p .assignment word
  let v1:=Function.update (Function.update v .catalogue tail) .valid [true]
  let v2:=Function.update v1 .valid []
  let entry:=(SemiprimeD1TensorTapeLeaf.evaluateAssignment ctx vertices word).words
  let p2:=Function.update p1 .product (vectorBits entry)
  let p3:=Function.update p2 .product []
  let out:=vectorBits (SemiprimeD1JetRingBits.add ctx entry acc).words
  let v3:=Function.update (Function.update v2 .sum []) .sumResult out
  let v4:=Function.update v3 .sum out
  let v5:=Function.update v4 .sumResult []
  have h1:=field_call p v word tail hcatalogue hassignment hflag
  have h2 : Runs program 1 .parsed (data p1 v1) .callProduct (data p1 v2) := by
    simpa only [v1,v2,Function.update_idem] using field_flag p1 (Function.update v .catalogue tail)
  obtain ⟨m3,hm3,h3⟩:=SemiprimeD1StackLeafProduct.product_call ctx hp vertices p1 v2
    (by simpa [p1] using hvertices) (by simpa [p1] using hreader) (by simpa [p1] using hleft)
    (by simpa [p1] using hprod) (by simpa [p1] using hports) (by simpa [p1] using htable)
    (by simpa [p1] using hvalid) (by simpa [p1] using hout) (by simpa [p1] using haxes)
    (by simpa [p1] using hw) (by simpa [p1] using hr)
  have h3' : Runs program m3 .callProduct (data p1 v2) .callAdd (data p2 v2) := by
    simpa [p2,entry,p1] using h3
  have h4 : Runs program (SemiprimeD1StackJetAddExecution.totalTime (p .width) (p .rank) entry acc+1)
      .callAdd (data p2 v2) .copySum (data p3 v3) := by
    apply SemiprimeD1StackLeafAddition.add_call ctx p2 v2 entry acc (by simp [p2])
      (by simpa [v2,v1] using hsum) (by simpa [v2,v1] using hsout)
      (by simpa [p2,p1] using hw) (by simp [p2,p1,hr,unary])
  have h5 : Runs program (5*out.length+4) .copySum (data p3 v3) .clearSumResult (data p3 v4) := by
    simpa [v4,v3] using copy_sum p3 v3
  have h6:=clear_sum p3 v4
  have h7:=clear_assignment p3 v5
  have hc:=runs_trans program _ _ _ _ _ _ _ _ h1 h2
  have hc:=runs_trans program _ _ _ _ _ _ _ _ hc h3'
  have hc:=runs_trans program _ _ _ _ _ _ _ _ hc h4
  have hc:=runs_trans program _ _ _ _ _ _ _ _ hc h5
  have hc:=runs_trans program _ _ _ _ _ _ _ _ hc h6
  have hc:=runs_trans program _ _ _ _ _ _ _ _ hc h7
  refine ⟨8*word.length+7+1+m3+
    (SemiprimeD1StackJetAddExecution.totalTime (p .width) (p .rank) entry acc+1)+
    (5*out.length+4)+((v4 .sumResult).length+1)+((p3 .assignment).length+1),?_,?_⟩
  · simp only [roundBudget]
    simp only [v4,v3,p3,p2,p1,Function.update_of_ne (by decide : Slot.sumResult ≠ .sum),
      Function.update_self,Function.update_of_ne (by decide : SemiprimeD1StackVertexProductState.Slot.assignment ≠ .product)]
    dsimp only [p1] at hm3
    dsimp only [entry,out]
    omega
  · convert hc using 1
    have hp3 : Function.update p3 .assignment []=p := by
      funext s
      cases s <;> simp_all [p3,p2,p1]
    rw [hp3]
    apply congrArg (data p)
    funext s
    cases s <;> simp_all [v5,v4,v3,v2,v1,out,entry]

end RiemannGaussian.SemiprimeD1StackLeafRound
