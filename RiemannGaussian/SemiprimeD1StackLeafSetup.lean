/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackLeafEnumeration
import RiemannGaussian.SemiprimeD1StackLeafValue
/-! # Closed binary-width acquisition, enumeration and actual leaf-sum execution -/
set_option autoImplicit false
set_option synthInstance.maxSize 131072
set_option maxRecDepth 131072
set_option maxHeartbeats 3000000
namespace RiemannGaussian.SemiprimeD1StackLeafSetup
open SemiprimeD1StackLeaf SemiprimeD1StackLeafState
open SemiprimeD1StackLeafAcquisition SemiprimeD1StackLeafEnumeration
open SemiprimeD1StackProcedureTrace (Runs runs_trans)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)

/-- Derived original-data startup/enumeration/fold transition bound. Binary
width conversion pays for its value; all assignments are actually materialized. -/
def enumeratedBudget (M : ℕ) (ctx : SemiprimeD1JetAxes.Context)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (p : PS.Values) (v : Values) : ℕ :=
  (5*(v .widthBits).length+4)+(7*M+6*(v .widthBits).length+4)+(2*M+1)+1+
    (100*(M+1)*2^M+11)+SemiprimeD1StackLeafLoop.loopBudget ctx vertices p
      (SemiprimeD1StackAssignmentOrder.assignments (2^M) (List.replicate M false)) []

/-- Starting from the context caches actually acquired by the preceding call,
the original binary width alone drives actual full enumeration and leaf sum. -/
theorem enumerated_run (M : ℕ) (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (p : PS.Values) (v : Values)
    (hM : SemiprimeBitArithmetic.bitValue (v .widthBits)=M)
    (hvertices : p .vertices=SemiprimeD1StackVertexProduct.records vertices)
    (hreader : p .reader=[]) (hleft : p .left=[]) (hprod : p .product=[])
    (hports : p .ports=[]) (htable : p .table=[]) (hvalid : p .valid=[]) (hout : p .result=[])
    (hassignment : p .assignment=[])
    (hi : v .unaryInput=[]) (hc : v .counter=[]) (hz : v .zero=[]) (hcat : v .catalogue=[])
    (hsum : v .sum=[]) (hsout : v .sumResult=[]) (hflag : v .valid=[])
    (haxes : p .axes=vectorBits (ctx.axes.map unary))
    (hw : (p .width).length=ctx.precision) (hr : p .rank=unary ctx.rank) :
    ∃ m ≤ enumeratedBudget M ctx vertices p v, Runs program m .widthCopy (data p v) .done
      (data p (Function.update v .sum (vectorBits (SemiprimeD1TensorTapeLeaf.run M ctx vertices).words))) := by
  let v1:=Function.update v .unaryInput (v .widthBits)
  let v2:=Function.update (Function.update v1 .unaryInput []) .counter
    (SemiprimeD1StackUnaryCounterExecution.markers M)
  let v3:=Function.update v2 .counter []
  let v4:=Function.update v3 .zero (List.replicate M false)
  let v5:=Function.update v4 .sum [false]
  let catalogue:=SemiprimeD1StackAssignmentOrder.assignments (2^M) (List.replicate M false)
  let v6:=Function.update (Function.update v5 .zero []) .catalogue (vectorBits catalogue)
  have h1:=width_copy p v hi
  have h2 : Runs program (2*(v .widthBits).length+1+
      SemiprimeD1StackUnaryCounterExecution.loopTime (v .widthBits).reverse 0+1)
      .widthUnary (data p v1) .makeZero (data p v2) := by
    simpa only [v1,v2,Function.update_self,hM] using width_unary p v1 (by simpa [v1] using hc)
  have h3 : Runs program (2*M+1) .makeZero (data p v2) .initializeSum (data p v4) := by
    have hh:=zero_run p v3 M (by simp [v3])
    have hv : Function.update v3 .counter (List.replicate M true)=v2 := by
      simp [v3,v2,SemiprimeD1StackUnaryCounterExecution.markers]
    rw [hv] at hh
    simpa [v4,v3,v2,v1,hz] using hh
  have h4 : Runs program 1 .initializeSum (data p v4) .enumerate (data p v5) := by
    simpa [v5,v4,v3,v2,v1,hsum] using initialize_sum p v4
  obtain ⟨m5,hm5,h5⟩:=enumeration_call p v5 M (by simp [v5,v4]) (by simpa [v5,v4,v3,v2,v1] using hcat)
  obtain ⟨m6,hm6,h6⟩:=SemiprimeD1StackLeafLoop.loop_run ctx hp vertices catalogue p v6 []
    (by simp [v6]) hvertices hreader hleft hprod hports htable hvalid hout hassignment
    (by simpa [v6,v5,v4,v3,v2,v1] using hflag) (by simp [v6,v5,vectorBits])
    (by simpa [v6,v5,v4,v3,v2,v1] using hsout) haxes hw hr
  have hc:=runs_trans program _ _ _ _ _ _ _ _ h1 h2
  have hc:=runs_trans program _ _ _ _ _ _ _ _ hc h3
  have hc:=runs_trans program _ _ _ _ _ _ _ _ hc h4
  have hc:=runs_trans program _ _ _ _ _ _ _ _ hc h5
  have hc:=runs_trans program _ _ _ _ _ _ _ _ hc h6
  refine ⟨(5*(v .widthBits).length+4)+
    (2*(v .widthBits).length+1+SemiprimeD1StackUnaryCounterExecution.loopTime (v .widthBits).reverse 0+1)+
    (2*M+1)+1+m5+m6,?_,?_⟩
  · have hu:=SemiprimeD1StackUnaryCounterExecution.source_time (v .widthBits)
    rw [hM] at hu
    change _ ≤ (5*(v .widthBits).length+4)+(7*M+6*(v .widthBits).length+4)+(2*M+1)+1+
      (100*(M+1)*2^M+11)+SemiprimeD1StackLeafLoop.loopBudget ctx vertices p catalogue []
    omega
  · convert hc using 1
    apply congrArg (data p)
    funext s
    cases s <;> simp_all [v6,v5,v4,v3,v2,v1,catalogue,SemiprimeD1StackLeafValue.summed_original M ctx hp]

end RiemannGaussian.SemiprimeD1StackLeafSetup
