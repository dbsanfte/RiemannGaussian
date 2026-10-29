/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackLeafRound
/-! # Whole actual assignment-catalogue traversal and physical sum -/
set_option autoImplicit false
set_option synthInstance.maxSize 131072
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackLeafLoop
open SemiprimeD1StackLeaf SemiprimeD1StackLeafState
open SemiprimeD1StackProcedureTrace (Runs one_base runs_trans)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)

/-- Mathematical byte specification of the reached physical dense-sum fold. -/
def summed (ctx : SemiprimeD1JetAxes.Context) (vertices : List SemiprimeD1LeafCounter.Vertex) :
    List (List Bool)→List (List Bool)→List (List Bool)
  | [],acc => acc
  | bits::rest,acc => summed ctx vertices rest
      (SemiprimeD1JetRingBits.add ctx (SemiprimeD1TensorTapeLeaf.evaluateAssignment ctx vertices bits).words acc).words

/-- Sum of actual derived round bounds along the reached dense accumulator. -/
def loopBudget (ctx : SemiprimeD1JetAxes.Context) (vertices : List SemiprimeD1LeafCounter.Vertex)
    (p : PS.Values) : List (List Bool)→List (List Bool)→ℕ
  | [],_ => 1
  | word::rest,acc =>
    1+SemiprimeD1StackLeafRound.roundBudget ctx vertices p word acc+
      loopBudget ctx vertices p rest
        (SemiprimeD1JetRingBits.add ctx (SemiprimeD1TensorTapeLeaf.evaluateAssignment ctx vertices word).words acc).words

/-- One real catalogue-constructor pop. -/
theorem tag_cons (p : PS.Values) (v : Values) (word : List Bool) :
    Runs program 1 .catalogueTag (data p (Function.update v .catalogue (true::word))) .parse
      (data p (Function.update v .catalogue word)) := by
  apply one_base program .catalogueTag .parse (.pop (address .catalogue) .done .done .parse) _ _ rfl
  · simp only [SemiprimeD1StackBytecode.execute,data_get,Function.update_self,List.head?_cons,
      SemiprimeD1StackBytecode.choose]
  · change Function.update (data p (Function.update v .catalogue (true::word))) (address .catalogue)
      ((data p (Function.update v .catalogue (true::word)) (address .catalogue)).tail)=_
    rw [data_get,Function.update_self,List.tail_cons,←data_update,Function.update_idem]

/-- The actual catalogue terminator is physically consumed. -/
theorem tag_nil (p : PS.Values) (v : Values) :
    Runs program 1 .catalogueTag (data p (Function.update v .catalogue [false])) .done
      (data p (Function.update v .catalogue [])) := by
  apply one_base program .catalogueTag .done (.pop (address .catalogue) .done .done .parse) _ _ rfl
  · simp only [SemiprimeD1StackBytecode.execute,data_get,Function.update_self,List.head?_cons,
      SemiprimeD1StackBytecode.choose]
  · change Function.update (data p (Function.update v .catalogue [false])) (address .catalogue)
      ((data p (Function.update v .catalogue [false]) (address .catalogue)).tail)=_
    rw [data_get,Function.update_self,List.tail_cons,←data_update,Function.update_idem]

/-- Every physically acquired assignment record invokes the actual closed
product and dense-adder procedures once. No leaf or coefficient callback. -/
theorem loop_run (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (assignments : List (List Bool))
    (p : PS.Values) (v : Values) (acc : List (List Bool))
    (hcatalogue : v .catalogue=vectorBits assignments)
    (hvertices : p .vertices=SemiprimeD1StackVertexProduct.records vertices)
    (hreader : p .reader=[]) (hleft : p .left=[]) (hprod : p .product=[])
    (hports : p .ports=[]) (htable : p .table=[]) (hvalid : p .valid=[]) (hout : p .result=[])
    (hassignment : p .assignment=[]) (hflag : v .valid=[]) (hsum : v .sum=vectorBits acc)
    (hsout : v .sumResult=[]) (haxes : p .axes=vectorBits (ctx.axes.map unary))
    (hw : (p .width).length=ctx.precision) (hr : p .rank=unary ctx.rank) :
    ∃ m ≤ loopBudget ctx vertices p assignments acc, Runs program m .catalogueTag (data p v) .done
      (data p (Function.update (Function.update v .catalogue []) .sum
        (vectorBits (summed ctx vertices assignments acc)))) := by
  induction assignments generalizing v acc with
  | nil =>
    have hh:=tag_nil p v
    have hv : Function.update v .catalogue [false]=v := Function.update_eq_self_iff.mpr hcatalogue.symm
    rw [hv] at hh
    have hs : Function.update (Function.update v .catalogue []) .sum (vectorBits acc)=
        Function.update v .catalogue [] := by
      apply Function.update_eq_self_iff.mpr
      simpa only [Function.update_of_ne (by decide : Slot.sum ≠ .catalogue)] using hsum.symm
    exact ⟨1,by rfl,by simpa only [summed,hs] using hh⟩
  | cons word rest ih =>
    let v1:=Function.update v .catalogue (SemiprimeSourceHistogramKeyBits.frame word (vectorBits rest))
    have h1 : Runs program 1 .catalogueTag (data p v) .parse (data p v1) := by
      have hh:=tag_cons p v (SemiprimeSourceHistogramKeyBits.frame word (vectorBits rest))
      have hv : Function.update v .catalogue (true::SemiprimeSourceHistogramKeyBits.frame word (vectorBits rest))=v :=
        Function.update_eq_self_iff.mpr hcatalogue.symm
      simpa only [hv] using hh
    obtain ⟨m,hmb,hm⟩:=SemiprimeD1StackLeafRound.round_run ctx hp vertices p v1 word (vectorBits rest) acc
      (by simp [v1]) hvertices hreader hleft hprod hports htable hvalid hout hassignment
      (by simpa [v1] using hflag) (by simpa [v1] using hsum) (by simpa [v1] using hsout) haxes hw hr
    let next:=(SemiprimeD1JetRingBits.add ctx
      (SemiprimeD1TensorTapeLeaf.evaluateAssignment ctx vertices word).words acc).words
    let v2:=Function.update (Function.update v1 .catalogue (vectorBits rest)) .sum (vectorBits next)
    obtain ⟨n,hnb,hn⟩:=ih v2 next (by simp [v2])
      (by simpa [v2,v1] using hflag) (by simp [v2]) (by simpa [v2,v1] using hsout)
    have hc:=runs_trans program _ _ _ _ _ _ _ _ h1 hm
    have hc:=runs_trans program _ _ _ _ _ _ _ _ hc hn
    refine ⟨1+m+n,?_,?_⟩
    · change 1+m+n ≤ 1+SemiprimeD1StackLeafRound.roundBudget ctx vertices p word acc+
        loopBudget ctx vertices p rest next
      omega
    · convert hc using 1
      apply congrArg (data p)
      funext s
      cases s <;> simp [v2,v1,summed,next]

end RiemannGaussian.SemiprimeD1StackLeafLoop
