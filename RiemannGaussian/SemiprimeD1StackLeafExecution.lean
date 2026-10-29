/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackLeafSetup
/-! # Closed actual original-header leaf execution, exact old leaf words -/
set_option autoImplicit false
set_option synthInstance.maxSize 131072
set_option maxRecDepth 131072
set_option maxHeartbeats 3000000
namespace RiemannGaussian.SemiprimeD1StackLeafExecution
open SemiprimeD1StackLeaf SemiprimeD1StackLeafState
open SemiprimeD1StackProcedureTrace (Runs runs_trans)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)

/-- Proof-side tuple of the original encoded headers and literal vertex records. -/
def originalProductValues (ctx : SemiprimeD1JetAxes.Context) (pBits : List Bool)
    (vertices : List SemiprimeD1LeafCounter.Vertex) : PS.Values :=
  SemiprimeD1StackVertexProductState.values (vectorBits (ctx.axes.map unary)) pBits
    (SemiprimeD1StackVertexProduct.records vertices) [] [] [] [] [] [] [] [] [] []
/-- The original binary assignment-width word is the only initially live outer register. -/
def originalValues (mBits : List Bool) : Values
  | .widthBits => mBits
  | _ => []
/-- Actual original physical start satisfies the declarative register invariant. -/
theorem initial_data (ctx : SemiprimeD1JetAxes.Context) (pBits mBits : List Bool)
    (vertices : List SemiprimeD1LeafCounter.Vertex) :
    (initial (vectorBits (ctx.axes.map unary)) pBits mBits
      (SemiprimeD1StackVertexProduct.records vertices)).data=
      data (originalProductValues ctx pBits vertices) (originalValues mBits) := by
  funext k
  fin_cases k <;> rfl

/-- Exact clean final store: original inputs and actually acquired caches retained,
only the leaf sum is added; every other data/return/work register is empty. -/
def finalData (M : ℕ) (ctx : SemiprimeD1JetAxes.Context) (pBits mBits : List Bool)
    (vertices : List SemiprimeD1LeafCounter.Vertex) : Stack→List Bool :=
  data (Function.update (Function.update (originalProductValues ctx pBits vertices) .rank (unary ctx.rank))
      .width (SemiprimeD1StackUnaryCounterExecution.markers ctx.precision))
    (Function.update (originalValues mBits) .sum
      (vectorBits (SemiprimeD1TensorTapeLeaf.run M ctx vertices).words))

/-- Actual complete transition budget from original headers and literal records,
retaining real context acquisition, width conversion, all assignments and folds. -/
def budget (M : ℕ) (ctx : SemiprimeD1JetAxes.Context) (pBits mBits : List Bool)
    (vertices : List SemiprimeD1LeafCounter.Vertex) : ℕ :=
  let ready:=Function.update (Function.update (originalProductValues ctx pBits vertices) .rank (unary ctx.rank))
    .width (SemiprimeD1StackUnaryCounterExecution.markers ctx.precision)
  1000*(SemiprimeD1StackJetContextBounds.resource ctx.axes pBits+1)^2+1+
    SemiprimeD1StackLeafSetup.enumeratedBudget M ctx vertices ready (originalValues mBits)+1

/-- One fixed finite program, starting with original physical headers and literal
tables only, executes actual enumeration/products/sums and returns EXACT bytes
of the frozen eager leaf routine. No prepared assignment, rank, precision count,
entry, coefficient, route, cost or leaf answer is supplied. -/
theorem source_run (M : ℕ) (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive)
    (pBits mBits : List Bool) (hprecision : SemiprimeBitArithmetic.bitValue pBits=ctx.precision)
    (hM : SemiprimeBitArithmetic.bitValue mBits=M) (vertices : List SemiprimeD1LeafCounter.Vertex) :
    ∃ m ≤ budget M ctx pBits mBits vertices, SemiprimeD1StackCalls.run program m
      (initial (vectorBits (ctx.axes.map unary)) pBits mBits (SemiprimeD1StackVertexProduct.records vertices))=
      some (⟨none,none,none,finalData M ctx pBits mBits vertices,[]⟩:
        SemiprimeD1StackCalls.State Stack Label) := by
  let p:=originalProductValues ctx pBits vertices
  let v:=originalValues mBits
  let ready:=Function.update (Function.update p .rank (unary ctx.rank)) .width
    (SemiprimeD1StackUnaryCounterExecution.markers ctx.precision)
  obtain ⟨m,hmb,hm⟩:=SemiprimeD1StackLeafAcquisition.context_call p v ctx.axes hp rfl rfl rfl
  have hm' : Runs program m .start (data p v) .widthCopy (data ready v) := by
    simpa only [ready,p,originalProductValues,SemiprimeD1StackVertexProductState.values,
      SemiprimeD1JetAxes.Context.rank,hprecision] using hm
  obtain ⟨n,hnb,hn⟩:=SemiprimeD1StackLeafSetup.enumerated_run M ctx hp vertices ready v
    hM (by simp [ready,p,originalProductValues,SemiprimeD1StackVertexProductState.values])
    (by simp [ready,p,originalProductValues,SemiprimeD1StackVertexProductState.values])
    (by simp [ready,p,originalProductValues,SemiprimeD1StackVertexProductState.values])
    (by simp [ready,p,originalProductValues,SemiprimeD1StackVertexProductState.values])
    (by simp [ready,p,originalProductValues,SemiprimeD1StackVertexProductState.values])
    (by simp [ready,p,originalProductValues,SemiprimeD1StackVertexProductState.values])
    (by simp [ready,p,originalProductValues,SemiprimeD1StackVertexProductState.values])
    (by simp [ready,p,originalProductValues,SemiprimeD1StackVertexProductState.values])
    (by simp [ready,p,originalProductValues,SemiprimeD1StackVertexProductState.values])
    rfl rfl rfl rfl rfl rfl rfl
    (by simp [ready,p,originalProductValues,SemiprimeD1StackVertexProductState.values])
    (by simp [ready,SemiprimeD1StackUnaryCounterExecution.markers]) (by simp [ready])
  have hc:=runs_trans program _ _ _ _ _ _ _ _ hm' hn
  obtain ⟨finish,hfinish,hout⟩:=hc []
    (initial (vectorBits (ctx.axes.map unary)) pBits mBits (SemiprimeD1StackVertexProduct.records vertices))
    ⟨rfl,initial_data ctx pBits mBits vertices,rfl⟩
  have hh:=SemiprimeD1StackProcedureTrace.halt_run program .done rfl _ [] finish hout
  refine ⟨m+n+1,?_,?_⟩
  · change m+n+1 ≤ 1000*(SemiprimeD1StackJetContextBounds.resource ctx.axes pBits+1)^2+1+
        SemiprimeD1StackLeafSetup.enumeratedBudget M ctx vertices ready v+1
    simpa only [p,originalProductValues,SemiprimeD1StackVertexProductState.values] using
      Nat.add_le_add_right (Nat.add_le_add hmb hnb) 1
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
    rfl

end RiemannGaussian.SemiprimeD1StackLeafExecution
