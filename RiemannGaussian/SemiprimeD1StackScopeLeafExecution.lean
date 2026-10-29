/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackScopeLeaf
/-! # Closed actual scope-counted leaf trace, no cardinality header -/
set_option autoImplicit false
set_option synthInstance.maxSize 131072
set_option maxRecDepth 131072
set_option maxHeartbeats 3000000
namespace RiemannGaussian.SemiprimeD1StackScopeLeafExecution
open SemiprimeD1StackScopeLeaf
namespace PS
export SemiprimeD1StackVertexProductState (Values data address)
end PS
open SemiprimeD1StackProcedureTrace (Runs runs_trans)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
namespace LS
export SemiprimeD1StackLeafState (data data_get data_product_update data_update)
end LS

/-- The original header tuple with context caches actually acquired by the first call. -/
def ready (ctx : SemiprimeD1JetAxes.Context) (pBits : List Bool)
    (vertices : List SemiprimeD1LeafCounter.Vertex) : PS.Values :=
  Function.update (Function.update (SemiprimeD1StackLeafExecution.originalProductValues ctx pBits vertices)
    .rank (unary ctx.rank)) .width (SemiprimeD1StackUnaryCounterExecution.markers ctx.precision)
/-- Exact final store, preserving every original scope record and every leaf input. -/
def finalData (ctx : SemiprimeD1JetAxes.Context) (pBits : List Bool)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (scopeWords : List (List Bool)) : Stack→List Bool :=
  data (SemiprimeD1StackLeafExecution.finalData scopeWords.length ctx pBits [] vertices) (vectorBits scopeWords)
/-- Closed actual stage budget: context, complete scope scan and the actual unary-ready leaf. -/
def budget (ctx : SemiprimeD1JetAxes.Context) (pBits : List Bool)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (scopeWords : List (List Bool)) : ℕ :=
  (1000*(SemiprimeD1StackJetContextBounds.resource ctx.axes pBits+1)^2+1)+
    (11*(vectorBits scopeWords).length+6)+
    (SemiprimeD1StackScopeLeafReady.budget scopeWords.length ctx vertices (ready ctx pBits vertices)+1)+1

/-- Real original-header scope-counted execution. The only assignment width is
acquired by physically scanning ALL scope records, including unused variables. -/
theorem source_run (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive) (pBits : List Bool)
    (hprecision : SemiprimeBitArithmetic.bitValue pBits=ctx.precision)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (scopeWords : List (List Bool)) :
    ∃ m ≤ budget ctx pBits vertices scopeWords,
      SemiprimeD1StackCalls.run program m
        (initial (vectorBits (ctx.axes.map unary)) pBits
          (SemiprimeD1StackVertexProduct.records vertices) (vectorBits scopeWords))=
      some (⟨none,none,none,finalData ctx pBits vertices scopeWords,[]⟩:
        SemiprimeD1StackCalls.State Stack Label) := by
  let p:=SemiprimeD1StackLeafExecution.originalProductValues ctx pBits vertices
  let v:=SemiprimeD1StackLeafExecution.originalValues []
  let p1:=ready ctx pBits vertices
  let inputLeaf:=LS.data p v
  let readyLeaf:=LS.data p1 v
  let countedLeaf:=LS.data p1 (Function.update v .counter (List.replicate scopeWords.length true))
  let outputLeaf:=SemiprimeD1StackLeafExecution.finalData scopeWords.length ctx pBits [] vertices
  obtain ⟨mc,hmc,hcontext⟩:=SemiprimeD1StackJetContextBounds.source_run_polynomial ctx.axes hp pBits
  have h1 : Runs program (mc+1) .start (data inputLeaf (vectorBits scopeWords)) .countScopes
      (data readyLeaf (vectorBits scopeWords)) := by
    apply SemiprimeD1StackProcedureInclusion.included_call program contextStack Label.context contextStack_injective
      X.program .start (fun _=>rfl) .start .countScopes rfl mc
      (SemiprimeD1StackJetContext.initial (vectorBits (ctx.axes.map unary)) pBits)
      (⟨none,none,none,SemiprimeD1StackJetContextCorrectness.finalData ctx.axes pBits,[]⟩:
        SemiprimeD1StackCalls.State X.Stack X.Label)
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hcontext
    · constructor
      · intro k
        change PS.data p (SemiprimeD1StackVertexProduct.contextStack k)=_
        rw [SemiprimeD1StackVertexProductProjection.context_project]
        fin_cases k <;> simp [p,SemiprimeD1StackLeafExecution.originalProductValues,
          SemiprimeD1StackVertexProductState.values,SemiprimeD1StackJetContext.initial,
          SemiprimeD1StackJetContext.bank,SemiprimeD1StackJetContext.cached,
          SemiprimeD1StackJetContext.axesCache,SemiprimeD1StackJetContext.rankCache,
          SemiprimeD1StackJetContext.widthCache,SemiprimeD1StackJetContext.precisionBits]
      · intro k hk; rfl
    · constructor
      · intro k
        change PS.data p1 (SemiprimeD1StackVertexProduct.contextStack k)=_
        rw [SemiprimeD1StackVertexProductProjection.context_project]
        fin_cases k <;> simp [p1,ready,SemiprimeD1StackLeafExecution.originalProductValues,
          SemiprimeD1StackVertexProductState.values,SemiprimeD1StackJetContextCorrectness.finalData,
          SemiprimeD1StackJetContext.bank,SemiprimeD1StackJetContext.cached,
          SemiprimeD1StackJetContextExecution.ready,SemiprimeD1StackJetSuffix.data,SemiprimeD1StackAdder.store,
          SemiprimeD1StackJetContext.axesCache,SemiprimeD1StackJetContext.rankCache,
          SemiprimeD1StackJetContext.widthCache,SemiprimeD1StackJetContext.precisionBits,hprecision,
          SemiprimeD1JetAxes.Context.rank]
      · intro k hk
        cases k with
        | inr k => cases k <;> rfl
        | inl k =>
          have hr : k ≠ SemiprimeD1StackLeaf.productStack (PS.address .rank) :=
            fun he=>hk SemiprimeD1StackJetContext.rankCache (congrArg leafStack he.symm)
          have hw : k ≠ SemiprimeD1StackLeaf.productStack (PS.address .width) :=
            fun he=>hk SemiprimeD1StackJetContext.widthCache (congrArg leafStack he.symm)
          change LS.data p1 v k=LS.data p v k
          dsimp only [p1,ready]
          rw [LS.data_product_update,LS.data_product_update]
          simp only [Function.update_of_ne hr,Function.update_of_ne hw]
          rfl
  have h2 : Runs program (SemiprimeD1StackDigitCountExecution.totalTime scopeWords+1)
      .countScopes (data readyLeaf (vectorBits scopeWords)) .callLeaf (data countedLeaf (vectorBits scopeWords)) := by
    apply SemiprimeD1StackProcedureInclusion.included_call program countStack Label.count countStack_injective
      D.program (.inl .main) (fun _=>rfl) .countScopes .callLeaf rfl _
      (SemiprimeD1StackDigitCountExecution.initial (vectorBits scopeWords))
      (SemiprimeD1StackDigitCountExecution.done scopeWords)
    · rfl
    · rfl
    · rfl
    · rfl
    · exact SemiprimeD1StackDigitCountExecution.acquire_run scopeWords
    · constructor
      · intro k
        cases k
        · rfl
        · rfl
        · exact LS.data_get p1 v .counter
        · rfl
        · rfl
        · rfl
        · rfl
      · intro k hk; rfl
    · constructor
      · intro k
        cases k
        · rfl
        · rfl
        · exact LS.data_get p1 (Function.update v .counter (List.replicate scopeWords.length true)) .counter
        · rfl
        · rfl
        · rfl
        · rfl
      · intro k hk
        cases k with
        | inr k => cases k <;> rfl
        | inl k =>
          have hn : k ≠ SemiprimeD1StackLeafState.address .counter :=
            fun he=>hk .count (congrArg leafStack he.symm)
          change LS.data p1 (Function.update v .counter (List.replicate scopeWords.length true)) k=LS.data p1 v k
          rw [LS.data_update]
          exact Function.update_of_ne hn _ _
  obtain ⟨ml,hml,hleaf⟩:=SemiprimeD1StackScopeLeafReady.ready_run scopeWords.length ctx hp vertices p1 v
    (by simp [p1,ready,SemiprimeD1StackLeafExecution.originalProductValues,SemiprimeD1StackVertexProductState.values])
    (by simp [p1,ready,SemiprimeD1StackLeafExecution.originalProductValues,SemiprimeD1StackVertexProductState.values])
    (by simp [p1,ready,SemiprimeD1StackLeafExecution.originalProductValues,SemiprimeD1StackVertexProductState.values])
    (by simp [p1,ready,SemiprimeD1StackLeafExecution.originalProductValues,SemiprimeD1StackVertexProductState.values])
    (by simp [p1,ready,SemiprimeD1StackLeafExecution.originalProductValues,SemiprimeD1StackVertexProductState.values])
    (by simp [p1,ready,SemiprimeD1StackLeafExecution.originalProductValues,SemiprimeD1StackVertexProductState.values])
    (by simp [p1,ready,SemiprimeD1StackLeafExecution.originalProductValues,SemiprimeD1StackVertexProductState.values])
    (by simp [p1,ready,SemiprimeD1StackLeafExecution.originalProductValues,SemiprimeD1StackVertexProductState.values])
    (by simp [p1,ready,SemiprimeD1StackLeafExecution.originalProductValues,SemiprimeD1StackVertexProductState.values])
    rfl rfl rfl rfl rfl rfl
    (by simp [p1,ready,SemiprimeD1StackLeafExecution.originalProductValues,SemiprimeD1StackVertexProductState.values])
    (by simp [p1,ready,SemiprimeD1StackUnaryCounterExecution.markers]) (by simp [p1,ready])
  have h3 : Runs program (ml+1) .callLeaf (data countedLeaf (vectorBits scopeWords)) .done
      (data outputLeaf (vectorBits scopeWords)) := by
    apply SemiprimeD1StackProcedureInclusion.included_call program leafStack Label.leaf
      (by intro a b h; exact Sum.inl.inj h) L.program .makeZero (fun _=>rfl) .callLeaf .done rfl ml
      (⟨some .makeZero,none,none,countedLeaf,[]⟩:SemiprimeD1StackCalls.State L.Stack L.Label)
      (⟨none,none,none,outputLeaf,[]⟩:SemiprimeD1StackCalls.State L.Stack L.Label)
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hleaf
    · constructor
      · intro k; rfl
      · intro k hk; rfl
    · constructor
      · intro k; rfl
      · intro k hk
        cases k with
        | inl k => exact (hk k rfl).elim
        | inr k => cases k <;> rfl
  have hh:=runs_trans program _ _ _ _ _ _ _ _ h1 h2
  have hh:=runs_trans program _ _ _ _ _ _ _ _ hh h3
  have hinit : (initial (vectorBits (ctx.axes.map unary)) pBits
      (SemiprimeD1StackVertexProduct.records vertices) (vectorBits scopeWords)).data=
      data inputLeaf (vectorBits scopeWords) := by
    apply congrArg (fun ds=>data ds (vectorBits scopeWords))
    exact SemiprimeD1StackLeafExecution.initial_data ctx pBits [] vertices
  obtain ⟨finish,hfinish,hAt⟩:=hh [] (initial (vectorBits (ctx.axes.map unary)) pBits
    (SemiprimeD1StackVertexProduct.records vertices) (vectorBits scopeWords)) ⟨rfl,hinit,rfl⟩
  have hhalt:=SemiprimeD1StackProcedureTrace.halt_run program .done rfl _ [] finish hAt
  refine ⟨(mc+1)+(SemiprimeD1StackDigitCountExecution.totalTime scopeWords+1)+(ml+1)+1,?_,?_⟩
  · have hd:=SemiprimeD1StackDigitCountExecution.totalTime_le scopeWords
    unfold budget
    change _≤(1000*(SemiprimeD1StackJetContextBounds.resource ctx.axes pBits+1)^2+1)+
      (11*(vectorBits scopeWords).length+6)+(SemiprimeD1StackScopeLeafReady.budget scopeWords.length ctx vertices p1+1)+1
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hhalt]
    rfl

end RiemannGaussian.SemiprimeD1StackScopeLeafExecution
