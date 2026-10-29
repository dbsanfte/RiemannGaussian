/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexProductBody
/-! # Whole actual record traversal of the physical vertex-product program -/
set_option autoImplicit false
set_option synthInstance.maxSize 65536
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackVertexProductLoop
open SemiprimeD1StackVertexProduct SemiprimeD1StackVertexProductState
open SemiprimeD1StackProcedureTrace (Runs one_base runs_trans)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)

/-- Mathematical byte specification of the actually executed left fold. No
function or coefficient specification is passed to the machine. -/
def folded (ctx : SemiprimeD1JetAxes.Context) (assignment : List Bool)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (acc : List (List Bool)) : List (List Bool) :=
  match vertices with
  | [] => acc
  | vertex::rest => folded ctx assignment rest
      (SemiprimeD1JetRingBits.mul ctx (SemiprimeD1TensorTapeLeaf.evaluateVertex vertex assignment).words acc).words

/-- The actual tag pop consumes precisely one serialized vertex constructor. -/
theorem tag_cons (v : Values) (word : List Bool) :
    Runs program 1 .vertexTag (data (Function.update v .reader (true::word))) .readPorts
      (data (Function.update v .reader word)) := by
  apply one_base program .vertexTag .readPorts (.pop (address .reader) .done .done .readPorts) _ _ rfl
  · simp only [SemiprimeD1StackBytecode.execute,data_get,Function.update_self,List.head?_cons,
      SemiprimeD1StackBytecode.choose]
  · change Function.update (data (Function.update v .reader (true::word))) (address .reader)
      ((data (Function.update v .reader (true::word)) (address .reader)).tail)=_
    rw [data_get,Function.update_self,List.tail_cons,←data_update,Function.update_idem]

/-- The actual terminator is consumed before the caller reaches its halt label. -/
theorem tag_nil (v : Values) :
    Runs program 1 .vertexTag (data (Function.update v .reader [false])) .done
      (data (Function.update v .reader [])) := by
  apply one_base program .vertexTag .done (.pop (address .reader) .done .done .readPorts) _ _ rfl
  · simp only [SemiprimeD1StackBytecode.execute,data_get,Function.update_self,List.head?_cons,
      SemiprimeD1StackBytecode.choose]
  · change Function.update (data (Function.update v .reader [false])) (address .reader)
      ((data (Function.update v .reader [false]) (address .reader)).tail)=_
    rw [data_get,Function.update_self,List.tail_cons,←data_update,Function.update_idem]

/-- Sum of the proved literal round bounds along the actual reached accumulator
states. This is derived from original record data, never a supplied cost. -/
def loopBudget (ctx : SemiprimeD1JetAxes.Context) :
    List SemiprimeD1LeafCounter.Vertex → Values → List (List Bool) → ℕ
  | [],_,_ => 1
  | vertex::rest,v,b =>
    let nb:=(SemiprimeD1JetRingBits.mul ctx
      (SemiprimeD1TensorTapeLeaf.evaluateVertex vertex (v .assignment)).words b).words
    let next:=Function.update (Function.update v .reader (records rest)) .product (vectorBits nb)
    1+SemiprimeD1StackVertexProductBody.roundBudget ctx v vertex b+loopBudget ctx rest next nb

/-- All original records are physically parsed and multiplied in one fixed
program, with cleared workspace between iterations and no entry callback. -/
theorem loop_run (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (v : Values) (b : List (List Bool))
    (hreader : v .reader=records vertices)
    (hleft : v .left=[]) (hports : v .ports=[]) (htable : v .table=[])
    (hvalid : v .valid=[]) (hresult : v .result=[])
    (hb : v .product=vectorBits b)
    (haxes : v .axes=vectorBits (ctx.axes.map unary))
    (hw : (v .width).length=ctx.precision) (hr : v .rank=unary ctx.rank) :
    ∃ m ≤ loopBudget ctx vertices v b, Runs program m .vertexTag (data v) .done
      (data (Function.update (Function.update v .reader []) .product
        (vectorBits (folded ctx (v .assignment) vertices b)))) := by
  induction vertices generalizing v b with
  | nil =>
    have hh:=tag_nil v
    have hv : Function.update v .reader [false]=v := Function.update_eq_self_iff.mpr hreader.symm
    rw [hv] at hh
    refine ⟨1,by rfl,?_⟩
    have hu : Function.update (Function.update v .reader []) .product (vectorBits b)=
        Function.update v .reader [] := by
      apply Function.update_eq_self_iff.mpr
      simpa only [Function.update_of_ne (by decide : Slot.product ≠ .reader)] using hb.symm
    simpa only [folded,hu] using hh
  | cons vertex rest ih =>
    let word:=SemiprimeSourceHistogramKeyBits.frame
      (SemiprimeD1StackVertexReadExecution.portTape vertex.ports)
      (SemiprimeSourceHistogramKeyBits.frame (SemiprimeD1TensorTapeCodec.tape vertex.table) (records rest))
    let v1:=Function.update v .reader word
    have ht : Runs program 1 .vertexTag (data v) .readPorts (data v1) := by
      have hh:=tag_cons v word
      have hv : Function.update v .reader (true::word)=v := Function.update_eq_self_iff.mpr hreader.symm
      simpa only [hv] using hh
    obtain ⟨m,hmb,hm⟩:=SemiprimeD1StackVertexProductBody.round_run ctx hp v1 vertex (records rest) b
      (by simp [v1,word]) (by simpa [v1] using hleft) (by simpa [v1] using hports)
      (by simpa [v1] using htable) (by simpa [v1] using hvalid) (by simpa [v1] using hresult)
      (by simpa [v1] using hb) (by simpa [v1] using haxes) (by simpa [v1] using hw) (by simpa [v1] using hr)
    let av:=(SemiprimeD1TensorTapeLeaf.evaluateVertex vertex (v .assignment)).words
    let nb:=(SemiprimeD1JetRingBits.mul ctx av b).words
    let v2:=Function.update (Function.update v1 .reader (records rest)) .product (vectorBits nb)
    have hm' : Runs program m .readPorts (data v1) .vertexTag (data v2) := by
      simpa [v2,nb,av,v1] using hm
    obtain ⟨n,hnb,hn⟩:=ih v2 nb (by simp [v2]) (by simpa [v2,v1] using hleft)
      (by simpa [v2,v1] using hports) (by simpa [v2,v1] using htable)
      (by simpa [v2,v1] using hvalid) (by simpa [v2,v1] using hresult)
      (by simp [v2]) (by simpa [v2,v1] using haxes) (by simpa [v2,v1] using hw) (by simpa [v2,v1] using hr)
    have hc:=runs_trans program _ _ _ _ _ _ _ _ ht hm'
    have hc:=runs_trans program _ _ _ _ _ _ _ _ hc hn
    refine ⟨1+m+n,?_,?_⟩
    · have hb1 : SemiprimeD1StackVertexProductBody.roundBudget ctx v1 vertex b=
          SemiprimeD1StackVertexProductBody.roundBudget ctx v vertex b := by
        simp [SemiprimeD1StackVertexProductBody.roundBudget,v1]
      rw [hb1] at hmb
      have hv2 : v2=Function.update (Function.update v .reader (records rest)) .product (vectorBits nb) := by
        simp [v2,v1]
      rw [hv2] at hnb
      change 1+m+n ≤ 1+SemiprimeD1StackVertexProductBody.roundBudget ctx v vertex b+
        loopBudget ctx rest (Function.update (Function.update v .reader (records rest)) .product (vectorBits nb)) nb
      omega
    · convert hc using 1
      apply congrArg data
      funext s
      cases s <;> simp [v2,v1,folded,nb,av]

end RiemannGaussian.SemiprimeD1StackVertexProductLoop
