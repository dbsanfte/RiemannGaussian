/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackLeafExecution
import RiemannGaussian.SemiprimeD1StackVertexProductPolynomial
/-! # Fixed polynomial physical leaf overhead with the actual 2^M enumeration -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
namespace RiemannGaussian.SemiprimeD1StackLeafPolynomial
open SemiprimeD1StackLeaf SemiprimeD1StackLeafState
open SemiprimeD1TensorTapeCodec (vectorBits tape)
open SemiprimeD1StackVertexProductPolynomial (vectorBound preparedPolynomial)

/-- Literal records contain every encoded original field and every vertex tag. -/
theorem records_caps (vertices : List SemiprimeD1LeafCounter.Vertex) :
    vertices.length≤(SemiprimeD1StackVertexProduct.records vertices).length ∧
    ∀v∈vertices,(SemiprimeD1StackVertexReadExecution.portTape v.ports).length≤
      (SemiprimeD1StackVertexProduct.records vertices).length ∧
      (tape v.table).length≤(SemiprimeD1StackVertexProduct.records vertices).length := by
  induction vertices with
  | nil => simp [SemiprimeD1StackVertexProduct.records]
  | cons x xs ih =>
    have hlen : (SemiprimeD1StackVertexProduct.records (x::xs)).length=
        2*(SemiprimeD1StackVertexReadExecution.portTape x.ports).length+2*(tape x.table).length+
          (SemiprimeD1StackVertexProduct.records xs).length+3 := by
      simp [SemiprimeD1StackVertexProduct.records,SemiprimeSourceHistogramKeyBits.frame_length]
      omega
    constructor
    · simp only [List.length_cons]
      omega
    · intro y hy
      rcases List.mem_cons.mp hy with rfl|hy
      · constructor <;> omega
      · have hh:=ih.2 y hy
        constructor <;> omega

/-- Fixed polynomial covering one full assignment parse/product/add/cleanup. -/
def roundPolynomial (S : ℕ) : ℕ :=
  8*S+8+(preparedPolynomial S+2)+(200*(S+1)*(2*vectorBound S+S+2)+1)+
    (5*vectorBound S+4)+(vectorBound S+1)+(S+1)

/-- The reached product/add round has a closed polynomial cap from original
literal-table data invariants and physical context/input dimensions only. -/
theorem roundBudget_le (ctx : SemiprimeD1JetAxes.Context)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (p : PS.Values) (word : List Bool)
    (acc : List (List Bool)) (S : ℕ)
    (hv : ∀x∈vertices,SemiprimeD1TensorTables.Good ctx x.table ∧
      (SemiprimeD1StackVertexReadExecution.portTape x.ports).length≤S ∧ (tape x.table).length≤S)
    (hcount : vertices.length≤S) (hrecords : (p .vertices).length≤S)
    (hr : ctx.rank≤S) (hp : ctx.precision≤S) (ha : ctx.axes.length≤S)
    (haxes : (p .axes).length≤S) (hw : (p .width).length≤S) (hrank : (p .rank).length≤S)
    (hword : word.length≤S) (hacc : (vectorBits acc).length≤vectorBound S) :
    SemiprimeD1StackLeafRound.roundBudget ctx vertices p word acc≤roundPolynomial S := by
  let entry:=(SemiprimeD1TensorTapeLeaf.evaluateAssignment ctx vertices word).words
  have hentry:=SemiprimeD1StackVertexProductPolynomial.good_vector_length ctx entry
    (SemiprimeD1TensorTapeLeaf.evaluateAssignment_good ctx vertices word) S hr hp
  have hout:=SemiprimeD1StackVertexProductPolynomial.good_vector_length ctx
    (SemiprimeD1JetRingBits.add ctx entry acc).words (SemiprimeD1LeafCounterBounds.add_good ctx _ _) S hr hp
  have hprod:=SemiprimeD1StackVertexProductPolynomial.preparedBudget_le ctx vertices
    (Function.update p .assignment word) S hv hcount (by simpa using hrecords) hr hp ha
    (by simpa using haxes) (by simpa using hw) (by simpa using hrank) (by simpa using hword)
  have hadd:=SemiprimeD1StackJetAddExecution.totalTime_le (p .width) (p .rank) entry acc
  have hadd' : SemiprimeD1StackJetAddExecution.totalTime (p .width) (p .rank) entry acc≤
      200*(S+1)*(2*vectorBound S+S+2) := by
    apply hadd.trans
    unfold SemiprimeD1StackJetAddExecution.timeBound
    have hm:=Nat.mul_le_mul (Nat.add_le_add_right hrank 1)
      (by omega : (vectorBits entry).length+(vectorBits acc).length+(p .width).length+2≤2*vectorBound S+S+2)
    nlinarith [Nat.mul_le_mul_left 200 hm]
  dsimp only [SemiprimeD1StackLeafRound.roundBudget,roundPolynomial]
  dsimp only [entry] at hentry hout hadd'
  omega

/-- No enumeration-count oracle: this bound follows the actual reached dense
accumulators, each new one canonical by the actual adder. -/
theorem loopBudget_le (ctx : SemiprimeD1JetAxes.Context)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (p : PS.Values)
    (words : List (List Bool)) (acc : List (List Bool)) (S : ℕ)
    (hv : ∀x∈vertices,SemiprimeD1TensorTables.Good ctx x.table ∧
      (SemiprimeD1StackVertexReadExecution.portTape x.ports).length≤S ∧ (tape x.table).length≤S)
    (hcount : vertices.length≤S) (hrecords : (p .vertices).length≤S)
    (hr : ctx.rank≤S) (hp : ctx.precision≤S) (ha : ctx.axes.length≤S)
    (haxes : (p .axes).length≤S) (hw : (p .width).length≤S) (hrank : (p .rank).length≤S)
    (hwords : ∀word∈words,word.length≤S) (hacc : (vectorBits acc).length≤vectorBound S) :
    SemiprimeD1StackLeafLoop.loopBudget ctx vertices p words acc≤words.length*(1+roundPolynomial S)+1 := by
  induction words generalizing acc with
  | nil => simp [SemiprimeD1StackLeafLoop.loopBudget]
  | cons word rest ih =>
    have hword:=hwords word (by simp)
    have hround:=roundBudget_le ctx vertices p word acc S hv hcount hrecords hr hp ha haxes hw hrank hword hacc
    let next:=(SemiprimeD1JetRingBits.add ctx
      (SemiprimeD1TensorTapeLeaf.evaluateAssignment ctx vertices word).words acc).words
    have hout:=SemiprimeD1StackVertexProductPolynomial.good_vector_length ctx next
      (SemiprimeD1LeafCounterBounds.add_good ctx _ _) S hr hp
    have ht:=ih next (fun w hw=>hwords w (by simp [hw])) hout
    change 1+SemiprimeD1StackLeafRound.roundBudget ctx vertices p word acc+
      SemiprimeD1StackLeafLoop.loopBudget ctx vertices p rest
        (SemiprimeD1JetRingBits.add ctx (SemiprimeD1TensorTapeLeaf.evaluateAssignment ctx vertices word).words acc).words≤_
    simp only [List.length_cons]
    nlinarith

end RiemannGaussian.SemiprimeD1StackLeafPolynomial
