/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexProductMultiply
/-! # Actual parsed vertex-product round, including every cleanup and copy -/
set_option autoImplicit false
set_option synthInstance.maxSize 65536
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackVertexProductBody
open SemiprimeD1StackVertexProduct SemiprimeD1StackVertexProductState
open SemiprimeD1StackVertexProductRead SemiprimeD1StackVertexProductMoves
open SemiprimeD1StackProcedureTrace (Runs runs_trans one_base)
open SemiprimeD1TensorTapeCodec (vectorBits tape)
open SemiprimeD1StackUnaryDivmod (unary)

/-- Explicit sum of the actual parser, vertex-reader, dense-multiplier,
operand-drain and result-copy transition bounds for one literal record. -/
def roundBudget (ctx : SemiprimeD1JetAxes.Context) (v : Values)
    (vertex : SemiprimeD1LeafCounter.Vertex) (b : List (List Bool)) : ℕ :=
  let av:=(SemiprimeD1TensorTapeLeaf.evaluateVertex vertex (v .assignment)).words
  let c : SemiprimeD1StackJetPointExecution.Cache :=
    ⟨vectorBits av,vectorBits b,v .axes,v .width,v .rank,[]⟩
  let out:=vectorBits (SemiprimeD1JetRingBits.mul ctx av b).words
  8*(SemiprimeD1StackVertexReadExecution.portTape vertex.ports).length+
  8*(tape vertex.table).length+16+
  (SemiprimeD1StackVertexReadExecution.budget (v .assignment).length
    (SemiprimeD1StackVertexReadExecution.portTape vertex.ports).length (tape vertex.table).length+1)+
  (2000000*(SemiprimeD1StackJetMulBounds.inputSize ctx c+1)^6+1)+
  ((vectorBits av).length+1)+((vectorBits b).length+1)+6*out.length+5

/-- One actual record is parsed, gathered and multiplied; the coefficient
buffers are physically cleared before the result is copied into the next state. -/
theorem round_run (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (v : Values) (vertex : SemiprimeD1LeafCounter.Vertex) (tail : List Bool)
    (b : List (List Bool))
    (hreader : v .reader=SemiprimeSourceHistogramKeyBits.frame
      (SemiprimeD1StackVertexReadExecution.portTape vertex.ports)
      (SemiprimeSourceHistogramKeyBits.frame (tape vertex.table) tail))
    (hleft : v .left=[]) (hports : v .ports=[]) (htable : v .table=[])
    (hvalid : v .valid=[]) (hresult : v .result=[])
    (hb : v .product=vectorBits b)
    (haxes : v .axes=vectorBits (ctx.axes.map unary))
    (hw : (v .width).length=ctx.precision) (hr : v .rank=unary ctx.rank) :
    ∃ m ≤ roundBudget ctx v vertex b, Runs program m .readPorts (data v) .vertexTag
      (data (Function.update (Function.update v .reader tail) .product
        (vectorBits (SemiprimeD1JetRingBits.mul ctx
          (SemiprimeD1TensorTapeLeaf.evaluateVertex vertex (v .assignment)).words b).words))) := by
  let p:=SemiprimeD1StackVertexReadExecution.portTape vertex.ports
  let t:=tape vertex.table
  let av:=(SemiprimeD1TensorTapeLeaf.evaluateVertex vertex (v .assignment)).words
  let out:=vectorBits (SemiprimeD1JetRingBits.mul ctx av b).words
  let v1:=Function.update (Function.update (Function.update v .reader
    (SemiprimeSourceHistogramKeyBits.frame t tail)) .ports p) .valid [true]
  let v2:=Function.update v1 .valid []
  let v3:=Function.update (Function.update (Function.update v2 .reader tail) .table t) .valid [true]
  let v4:=Function.update v3 .valid []
  let v5:=Function.update (Function.update (Function.update v4 .ports []) .table []) .left (vectorBits av)
  let v6:=Function.update v5 .result out
  let v7:=Function.update v6 .left []
  let v8:=Function.update v7 .product []
  let v9:=Function.update v8 .product out
  let v10:=Function.update v9 .result []
  have h1 : Runs program (8*p.length+7) .readPorts (data v) .portsDone (data v1) :=
    field_call v false p (SemiprimeSourceHistogramKeyBits.frame t tail) _ _ rfl hreader hports hvalid
  have h2 : Runs program 1 .portsDone (data v1) .readTable (data v2) := by
    simpa only [v1,v2,Function.update_idem] using
      field_flag (Function.update (Function.update v .reader (SemiprimeSourceHistogramKeyBits.frame t tail)) .ports p)
        .portsDone .readTable rfl
  have h3 : Runs program (8*t.length+7) .readTable (data v2) .tableDone (data v3) := by
    apply field_call v2 true t tail _ _ rfl
    · simp [v2,v1]
    · simpa [v2,v1,fieldTarget] using htable
    · simp [v2]
  have h4 : Runs program 1 .tableDone (data v3) .callVertex (data v4) := by
    simpa only [v3,v4,Function.update_idem] using
      field_flag (Function.update (Function.update v2 .reader tail) .table t) .tableDone .callVertex rfl
  obtain ⟨m5,hm5,h5⟩:=vertex_call v4 vertex (by simp [v4,v3,v2,v1,p]) (by simp [v4,v3,t])
    (by simpa [v4,v3,v2,v1] using hleft)
  have h5' : Runs program m5 .callVertex (data v4) .callMul (data v5) := by
    simpa only [v5,av,v4,v3,v2,v1,Function.update_of_ne (by decide : Slot.assignment ≠ .valid),
      Function.update_of_ne (by decide : Slot.assignment ≠ .table),
      Function.update_of_ne (by decide : Slot.assignment ≠ .reader),
      Function.update_of_ne (by decide : Slot.assignment ≠ .ports)] using h5
  obtain ⟨m6,hm6,h6⟩:=SemiprimeD1StackVertexProductMultiply.multiply_call ctx hp v5 av b
    (by simp [v5]) (by simpa [v5,v4,v3,v2,v1] using hb)
    (by simpa [v5,v4,v3,v2,v1] using haxes)
    (by simpa [v5,v4,v3,v2,v1] using hw)
    (by simpa [v5,v4,v3,v2,v1] using hr)
    (by simpa [v5,v4,v3,v2,v1] using hresult)
  have h7:=drain_current v6 .left .clearA .clearB rfl
  have h8:=drain_current v7 .product .clearB .copyProduct rfl
  have h9 : Runs program (5*(v8 .result).length+4) .copyProduct (data v8) .clearOutput (data v9) := by
    simpa [copySource,copyTarget,v9,v8,v7,v6] using copy_call v8 false .copyProduct .clearOutput rfl
  have h10:=drain_current v9 .result .clearOutput .vertexTag rfl
  have hc:=runs_trans program _ _ _ _ _ _ _ _ h1 h2
  have hc:=runs_trans program _ _ _ _ _ _ _ _ hc h3
  have hc:=runs_trans program _ _ _ _ _ _ _ _ hc h4
  have hc:=runs_trans program _ _ _ _ _ _ _ _ hc h5'
  have hc:=runs_trans program _ _ _ _ _ _ _ _ hc h6
  have hc:=runs_trans program _ _ _ _ _ _ _ _ hc h7
  have hc:=runs_trans program _ _ _ _ _ _ _ _ hc h8
  have hc:=runs_trans program _ _ _ _ _ _ _ _ hc h9
  have hc:=runs_trans program _ _ _ _ _ _ _ _ hc h10
  have hv10 : v10=Function.update (Function.update v .reader tail) .product out := by
    funext s
    cases s <;> simp_all [v10,v9,v8,v7,v6,v5,v4,v3,v2,v1]
  refine ⟨8*p.length+7+1+(8*t.length+7)+1+m5+m6+((v6 .left).length+1)+
    ((v7 .product).length+1)+(5*(v8 .result).length+4)+((v9 .result).length+1),?_,?_⟩
  · dsimp only [roundBudget]
    simp only [v5,v4,v3,v2,v1,SemiprimeD1StackVertexProductProjection.multiplierCache,
      Function.update_self,Function.update_of_ne (by decide : Slot.assignment ≠ .valid),
      Function.update_of_ne (by decide : Slot.assignment ≠ .table),
      Function.update_of_ne (by decide : Slot.assignment ≠ .reader),
      Function.update_of_ne (by decide : Slot.assignment ≠ .ports)] at hm5 hm6
    simp [v9,v8,v7,v6,v5,v4,v3,v2,v1,p,t,out,av,hb] at hm5 hm6 ⊢
    omega
  · change Runs program _ .readPorts (data v) .vertexTag (data (Function.update (Function.update v .reader tail) .product out))
    rw [←hv10]
    exact hc

end RiemannGaussian.SemiprimeD1StackVertexProductBody
