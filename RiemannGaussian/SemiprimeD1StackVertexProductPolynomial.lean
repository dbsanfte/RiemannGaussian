/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexProductExecution
/-! # Original-data polynomial bounds for the actual parsed vertex product -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackVertexProductPolynomial
open SemiprimeD1StackVertexProductState
open SemiprimeD1TensorTapeCodec (vectorBits tape)
open SemiprimeD1TensorTables (GoodWords)

/-- Actual framed-vector inventory from the literal coefficient widths. -/
theorem vector_length (ws : List (List Bool)) (P : ℕ) (hw : ∀w∈ws,w.length≤P) :
    (vectorBits ws).length≤2*ws.length*(P+1)+1 := by
  induction ws with
  | nil => simp [vectorBits]
  | cons w ws ih =>
    have hh:=hw w (by simp)
    have ht:=ih (fun x hx=>hw x (by simp [hx]))
    simp only [vectorBits,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
    nlinarith

/-- Fixed polynomial encoded size for any actual canonical current-context vector. -/
def vectorBound (S : ℕ) : ℕ := 2*S*(S+1)+1
/-- Original shape/width discharge the encoded-vector cap. -/
theorem good_vector_length (ctx : SemiprimeD1JetAxes.Context) (ws : List (List Bool))
    (hg : GoodWords ctx ws) (S : ℕ) (hr : ctx.rank≤S) (hp : ctx.precision≤S) :
    (vectorBits ws).length≤vectorBound S := by
  have hh:=vector_length ws ctx.precision (fun w hw=>(hg.2 w hw).2)
  rw [hg.1] at hh
  apply hh.trans
  unfold vectorBound
  gcongr

/-- Pure polynomial covering every real parser/read/multiply/copy/drain round. -/
def roundPolynomial (S : ℕ) : ℕ :=
  16*S+16+(5*(3*S+8)*(S+1)+8*(4*S+3)+3+1)+
  (2000000*(10*S+2*vectorBound S+2)^6+1)+
  (vectorBound S+1)+(vectorBound S+1)+6*vectorBound S+5

/-- All arithmetic and storage caps of one executed round follow from original
stored-table canonicality and original dimensions/inventory, not result advice. -/
theorem roundBudget_le (ctx : SemiprimeD1JetAxes.Context) (v : Values)
    (vertex : SemiprimeD1LeafCounter.Vertex) (b : List (List Bool)) (S : ℕ)
    (hv : SemiprimeD1TensorTables.Good ctx vertex.table) (hb : GoodWords ctx b)
    (hr : ctx.rank≤S) (hp : ctx.precision≤S) (ha : ctx.axes.length≤S)
    (haxes : (v .axes).length≤S) (hw : (v .width).length≤S) (hrank : (v .rank).length≤S)
    (hbits : (v .assignment).length≤S)
    (hports : (SemiprimeD1StackVertexReadExecution.portTape vertex.ports).length≤S)
    (htable : (tape vertex.table).length≤S) :
    SemiprimeD1StackVertexProductBody.roundBudget ctx v vertex b≤roundPolynomial S := by
  let av:=(SemiprimeD1TensorTapeLeaf.evaluateVertex vertex (v .assignment)).words
  have hav : GoodWords ctx av := by
    rw [show av=(SemiprimeD1LeafCounter.evaluateVertex vertex (v .assignment)).words from
      SemiprimeD1TensorTapeLeaf.evaluateVertex_words _ _]
    exact SemiprimeD1LeafCounterBounds.evaluateVertex_good ctx vertex hv _
  have hva:=good_vector_length ctx av hav S hr hp
  have hvb:=good_vector_length ctx b hb S hr hp
  have hvo:=good_vector_length ctx (SemiprimeD1JetRingBits.mul ctx av b).words
    (SemiprimeD1LeafCounterBounds.mul_good ctx av b) S hr hp
  let c : SemiprimeD1StackJetPointExecution.Cache :=
    ⟨vectorBits av,vectorBits b,v .axes,v .width,v .rank,[]⟩
  have hc : SemiprimeD1StackJetMulBounds.inputSize ctx c≤10*S+2*vectorBound S+1 := by
    dsimp only [SemiprimeD1StackJetMulBounds.inputSize,SemiprimeD1StackJetPointBounds.inputSize,
      SemiprimeD1StackJetMulExecution.indexed,c]
    omega
  have hm : 2000000*(SemiprimeD1StackJetMulBounds.inputSize ctx c+1)^6≤
      2000000*(10*S+2*vectorBound S+2)^6 := by
    exact Nat.mul_le_mul_left 2000000 (Nat.pow_le_pow_left (by omega) 6)
  have hread : SemiprimeD1StackVertexReadExecution.budget (v .assignment).length
      (SemiprimeD1StackVertexReadExecution.portTape vertex.ports).length (tape vertex.table).length≤
      5*(3*S+8)*(S+1)+8*(4*S+3)+3 := by
    unfold SemiprimeD1StackVertexReadExecution.budget SemiprimeD1StackGatherBytecode.budget
      SemiprimeD1StackBitGatherBounds.budget SemiprimeD1StackTreeBytecode.budget
    have hm:=Nat.mul_le_mul (by omega : 3*(v .assignment).length+8≤3*S+8) (Nat.add_le_add_right hports 1)
    nlinarith [Nat.mul_le_mul_left 5 hm]
  dsimp only [SemiprimeD1StackVertexProductBody.roundBudget,roundPolynomial]
  change _ ≤ _ at hm
  change (vectorBits av).length≤_ at hva
  change _≤_ at hvo
  dsimp only [c,av] at hm hva hvo
  omega

/-- All reached record rounds have the same original inventory cap; no recursive
cost oracle is used and accumulator sizes are derived from actual multiplication. -/
theorem loopBudget_le (ctx : SemiprimeD1JetAxes.Context)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (v : Values) (b : List (List Bool)) (S : ℕ)
    (hv : ∀x∈vertices,SemiprimeD1TensorTables.Good ctx x.table ∧
      (SemiprimeD1StackVertexReadExecution.portTape x.ports).length≤S ∧ (tape x.table).length≤S)
    (hb : GoodWords ctx b) (hr : ctx.rank≤S) (hp : ctx.precision≤S) (ha : ctx.axes.length≤S)
    (haxes : (v .axes).length≤S) (hw : (v .width).length≤S) (hrank : (v .rank).length≤S)
    (hbits : (v .assignment).length≤S) :
    SemiprimeD1StackVertexProductLoop.loopBudget ctx vertices v b≤vertices.length*(1+roundPolynomial S)+1 := by
  induction vertices generalizing v b with
  | nil => simp [SemiprimeD1StackVertexProductLoop.loopBudget]
  | cons x xs ih =>
    have hx:=hv x (by simp)
    let nb:=(SemiprimeD1JetRingBits.mul ctx (SemiprimeD1TensorTapeLeaf.evaluateVertex x (v .assignment)).words b).words
    let next:=Function.update (Function.update v .reader (SemiprimeD1StackVertexProduct.records xs)) .product (vectorBits nb)
    have hround:=roundBudget_le ctx v x b S hx.1 hb hr hp ha haxes hw hrank hbits hx.2.1 hx.2.2
    have ht:=ih next nb (fun y hy=>hv y (by simp [hy]))
      (SemiprimeD1LeafCounterBounds.mul_good ctx _ _) (by simpa [next] using haxes)
      (by simpa [next] using hw) (by simpa [next] using hrank) (by simpa [next] using hbits)
    change 1+SemiprimeD1StackVertexProductBody.roundBudget ctx v x b+
      SemiprimeD1StackVertexProductLoop.loopBudget ctx xs next nb≤_
    simp only [List.length_cons]
    nlinarith

/-- Fixed polynomial including literal unit construction, both physical copies
and all original record rounds. -/
def preparedPolynomial (S : ℕ) : ℕ :=
  (200*(S+1)*(S+8)+8)+1+(5*vectorBound S+4)+(vectorBound S+1)+(5*S+4)+
    (S*(1+roundPolynomial S)+1)

/-- Actual prepared product budget is fixed polynomial in the original context
and literal record inventory. Stored-table canonicality is a data invariant. -/
theorem preparedBudget_le (ctx : SemiprimeD1JetAxes.Context)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (v : Values) (S : ℕ)
    (hv : ∀x∈vertices,SemiprimeD1TensorTables.Good ctx x.table ∧
      (SemiprimeD1StackVertexReadExecution.portTape x.ports).length≤S ∧ (tape x.table).length≤S)
    (hcount : vertices.length≤S) (hrecords : (v .vertices).length≤S)
    (hr : ctx.rank≤S) (hp : ctx.precision≤S) (ha : ctx.axes.length≤S)
    (haxes : (v .axes).length≤S) (hw : (v .width).length≤S) (hrank : (v .rank).length≤S)
    (hbits : (v .assignment).length≤S) :
    SemiprimeD1StackVertexProductExecution.preparedBudget ctx vertices v≤preparedPolynomial S := by
  let unit:=vectorBits (SemiprimeD1JetAffineCoefficient.one ctx).words
  let ready:=Function.update (Function.update (Function.update (Function.update v .result unit)
    .product unit) .result []) .reader (SemiprimeD1StackVertexProduct.records vertices)
  have hu:=good_vector_length ctx (SemiprimeD1JetAffineCoefficient.one ctx).words
    (SemiprimeD1LeafCounterBounds.one_good ctx) S hr hp
  have ht:=loopBudget_le ctx vertices ready (SemiprimeD1JetAffineCoefficient.one ctx).words S hv
    (SemiprimeD1LeafCounterBounds.one_good ctx) hr hp ha (by simpa [ready] using haxes)
    (by simpa [ready] using hw) (by simpa [ready] using hrank) (by simpa [ready] using hbits)
  have hc:=SemiprimeD1StackJetUnitExecution.totalTime_le (v .width) (v .rank)
  have hc' : SemiprimeD1StackJetUnitExecution.totalTime (v .width) (v .rank)≤200*(S+1)*(S+8)+8 := by
    apply hc.trans
    unfold SemiprimeD1StackJetUnitExecution.timeBound
    have hm:=Nat.mul_le_mul (Nat.add_le_add_right hrank 1) (Nat.add_le_add_right hw 8)
    nlinarith [Nat.mul_le_mul_left 200 hm]
  have htc:=Nat.mul_le_mul_right (1+roundPolynomial S) hcount
  dsimp only [SemiprimeD1StackVertexProductExecution.preparedBudget,preparedPolynomial]
  change _≤_ at ht
  dsimp only [ready,unit] at ht
  omega

end RiemannGaussian.SemiprimeD1StackVertexProductPolynomial
