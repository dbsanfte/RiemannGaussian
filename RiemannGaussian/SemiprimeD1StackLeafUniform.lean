/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackLeafPolynomial
/-! # Closed original-header polynomial-times-enumeration transition bound -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
namespace RiemannGaussian.SemiprimeD1StackLeafUniform
open SemiprimeD1StackLeaf SemiprimeD1StackLeafState
open SemiprimeD1StackLeafPolynomial
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)

/-- Actual original context/header/serialized-table inventory. The binary words
are physical inputs; their precision/assignment-width VALUES are paid explicitly. -/
def resource (M : ℕ) (ctx : SemiprimeD1JetAxes.Context) (pBits mBits : List Bool)
    (vertices : List SemiprimeD1LeafCounter.Vertex) : ℕ :=
  M+ctx.rank+ctx.precision+ctx.axes.length+(vectorBits (ctx.axes.map unary)).length+
    pBits.length+mBits.length+(SemiprimeD1StackVertexProduct.records vertices).length+1
/-- Fixed polynomial startup/cleanup overhead before enumeration scaling. -/
def overhead (S : ℕ) : ℕ :=
  1000*(5*S+2)^2+1+(5*S+4)+(13*S+4)+(2*S+1)+1+11+1+1
/-- Fixed polynomial multiplying the ACTUAL exhaustive assignment count 2^M. -/
def polynomial (S : ℕ) : ℕ := overhead S+100*(S+1)+(1+roundPolynomial S)

/-- Complete original-input budget cap. Every local table bound is its original
canonical data invariant; no encoded entry, assignment, rank or cost is advised. -/
theorem budget_le (M : ℕ) (ctx : SemiprimeD1JetAxes.Context) (pBits mBits : List Bool)
    (hprecision : SemiprimeBitArithmetic.bitValue pBits=ctx.precision)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (hg : SemiprimeD1LeafCounter.Good ctx vertices) :
    SemiprimeD1StackLeafExecution.budget M ctx pBits mBits vertices≤
      polynomial (resource M ctx pBits mBits vertices)*2^M := by
  let S:=resource M ctx pBits mBits vertices
  let ready:=Function.update (Function.update
    (SemiprimeD1StackLeafExecution.originalProductValues ctx pBits vertices) .rank (unary ctx.rank)) .width
      (SemiprimeD1StackUnaryCounterExecution.markers ctx.precision)
  let catalogue:=SemiprimeD1StackAssignmentOrder.assignments (2^M) (List.replicate M false)
  have hM : M≤S := by dsimp [S,resource];omega
  have hr : ctx.rank≤S := by dsimp [S,resource];omega
  have hp : ctx.precision≤S := by dsimp [S,resource];omega
  have ha : ctx.axes.length≤S := by dsimp [S,resource];omega
  have hx : (vectorBits (ctx.axes.map unary)).length≤S := by dsimp [S,resource];omega
  have hm : mBits.length≤S := by dsimp [S,resource];omega
  have hpb : pBits.length≤S := by dsimp [S,resource];omega
  have hrecords : (SemiprimeD1StackVertexProduct.records vertices).length≤S := by dsimp [S,resource];omega
  have hrc:=records_caps vertices
  have hv : ∀x∈vertices,SemiprimeD1TensorTables.Good ctx x.table ∧
      (SemiprimeD1StackVertexReadExecution.portTape x.ports).length≤S ∧
      (SemiprimeD1TensorTapeCodec.tape x.table).length≤S := by
    intro x hmem
    exact ⟨hg x hmem,(hrc.2 x hmem).1.trans hrecords,(hrc.2 x hmem).2.trans hrecords⟩
  have hloop:=loopBudget_le ctx vertices ready catalogue [] S hv (hrc.1.trans hrecords)
    (by simpa [ready,SemiprimeD1StackLeafExecution.originalProductValues,
      SemiprimeD1StackVertexProductState.values] using hrecords) hr hp ha
    (by simpa [ready,SemiprimeD1StackLeafExecution.originalProductValues,
      SemiprimeD1StackVertexProductState.values] using hx)
    (by simpa [ready,SemiprimeD1StackUnaryCounterExecution.markers] using hp)
    (by simpa [ready,unary] using hr)
    (by
      intro word hword
      have hlen:=SemiprimeD1StackAssignmentOrder.assignments_width (2^M) (List.replicate M false) word hword
      have hw : word.length=M := by simpa using hlen
      omega)
    (by simp [vectorBits,SemiprimeD1StackVertexProductPolynomial.vectorBound])
  have hlen : catalogue.length=2^M := SemiprimeD1StackAssignmentOrder.assignments_length _ _
  rw [hlen] at hloop
  have hres : SemiprimeD1StackJetContextBounds.resource ctx.axes pBits≤5*S+1 := by
    change (vectorBits (ctx.axes.map unary)).length+ctx.axes.length+ctx.rank+pBits.length+
      SemiprimeBitArithmetic.bitValue pBits+1≤5*S+1
    rw [hprecision]
    omega
  have hcontext : 1000*(SemiprimeD1StackJetContextBounds.resource ctx.axes pBits+1)^2≤1000*(5*S+2)^2 :=
    Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left (by omega) 2)
  have henum := Nat.mul_le_mul_right (2^M) (Nat.mul_le_mul_left 100 (Nat.add_le_add_right hM 1))
  have hfirst : SemiprimeD1StackLeafExecution.budget M ctx pBits mBits vertices≤
      overhead S+(100*(S+1)+(1+roundPolynomial S))*2^M := by
    dsimp only [SemiprimeD1StackLeafExecution.budget,SemiprimeD1StackLeafSetup.enumeratedBudget,
      SemiprimeD1StackLeafExecution.originalValues]
    dsimp only [ready,catalogue] at hloop
    unfold overhead
    nlinarith
  have hpow : 1 ≤ (2 : ℕ)^M := by
    have hpos : (0 : ℕ) < 2^M := by positivity
    omega
  have hscale:=Nat.mul_le_mul_left (overhead S) hpow
  change _≤polynomial S*2^M
  unfold polynomial
  nlinarith

end RiemannGaussian.SemiprimeD1StackLeafUniform
