/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackLeafLoop
/-! # Actual context and binary assignment-width acquisition in the leaf caller -/
set_option autoImplicit false
set_option synthInstance.maxSize 131072
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackLeafAcquisition
open SemiprimeD1StackLeaf SemiprimeD1StackLeafState
open SemiprimeD1StackProcedureTrace (Runs runs_trans one_base)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)

/-- Actual context supplier shares precisely the retained product registers. -/
theorem context_call (p : PS.Values) (v : Values) (axesList : List ℕ)
    (hp : ∀q∈axesList,0<q) (ha : p .axes=vectorBits (axesList.map unary))
    (hr : p .rank=[]) (hw : p .width=[]) :
    ∃ m ≤ 1000*(SemiprimeD1StackJetContextBounds.resource axesList (p .precision)+1)^2+1,
      Runs program m .start (data p v) .widthCopy
        (data (Function.update (Function.update p .rank (unary axesList.prod)) .width
          (SemiprimeD1StackUnaryCounterExecution.markers (SemiprimeBitArithmetic.bitValue (p .precision)))) v) := by
  obtain ⟨m,hm,hs⟩:=SemiprimeD1StackJetContextBounds.source_run_polynomial axesList hp (p .precision)
  refine ⟨m+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program contextStack Label.context contextStack_injective
    SemiprimeD1StackJetContext.program .start (fun _=>rfl) .start .widthCopy rfl m
    (SemiprimeD1StackJetContext.initial (vectorBits (axesList.map unary)) (p .precision))
    (⟨none,none,none,SemiprimeD1StackJetContextCorrectness.finalData axesList (p .precision),[]⟩:
      SemiprimeD1StackCalls.State SemiprimeD1StackJetContext.Stack SemiprimeD1StackJetContext.Label)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hs
  · constructor
    · intro k
      change PS.data p (P.contextStack k)=_
      rw [SemiprimeD1StackVertexProductProjection.context_project]
      fin_cases k <;> simp [SemiprimeD1StackJetContext.initial,SemiprimeD1StackJetContext.bank,
        SemiprimeD1StackJetContext.cached,SemiprimeD1StackJetContext.axesCache,
        SemiprimeD1StackJetContext.rankCache,SemiprimeD1StackJetContext.widthCache,
        SemiprimeD1StackJetContext.precisionBits,ha,hr,hw]
    · intro k hk; rfl
  · constructor
    · intro k
      change PS.data _ (P.contextStack k)=_
      rw [SemiprimeD1StackVertexProductProjection.context_project]
      fin_cases k <;> simp [SemiprimeD1StackJetContextCorrectness.finalData,
        SemiprimeD1StackJetContext.bank,SemiprimeD1StackJetContext.cached,
        SemiprimeD1StackJetContextExecution.ready,SemiprimeD1StackJetSuffix.data,SemiprimeD1StackAdder.store,
        SemiprimeD1StackJetContext.axesCache,SemiprimeD1StackJetContext.rankCache,
        SemiprimeD1StackJetContext.widthCache,SemiprimeD1StackJetContext.precisionBits,ha]
    · intro k hk
      have hr : k ≠ productStack (PS.address .rank) := fun he=>hk SemiprimeD1StackJetContext.rankCache he.symm
      have hw : k ≠ productStack (PS.address .width) := fun he=>hk SemiprimeD1StackJetContext.widthCache he.symm
      rw [data_product_update,data_product_update]
      simp only [Function.update_of_ne hr,Function.update_of_ne hw]

/-- Exact small unary-acquisition register projection, including its actual input. -/
theorem unary_project (p : PS.Values) (v : Values) (k : U.Stack) :
    data p v (unaryStack k)=SemiprimeD1StackAdder.store (v .unaryInput) [] [] (v .counter) k := by
  cases k
  · exact data_get p v .unaryInput
  · rfl
  · rfl
  · exact data_get p v .counter

/-- The original binary width is really copied to its acquisition procedure. -/
theorem width_copy (p : PS.Values) (v : Values) (he : v .unaryInput=[]) :
    Runs program (5*(v .widthBits).length+4) .widthCopy (data p v) .widthUnary
      (data p (Function.update v .unaryInput (v .widthBits))) := by
  apply SemiprimeD1StackProcedureTrace.included_call program (copyStack false) (Label.copy false)
    (copyStack_injective false) SemiprimeD1StackCopy.code (0:Fin 9) (fun _=>rfl) .widthCopy .widthUnary rfl _
    (SemiprimeD1StackCopy.state 0 none (v .widthBits) [] [])
    (SemiprimeD1StackCopy.done (v .widthBits) (v .widthBits))
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words (v .widthBits) [] none
  · constructor
    · intro k
      fin_cases k
      · exact data_get p v .widthBits
      · change data p v (address .unaryInput)=[]
        rw [data_get,he]
      · rfl
    · intro k hk; rfl
  · constructor
    · intro k
      fin_cases k
      · exact data_get p (Function.update v .unaryInput (v .widthBits)) .widthBits
      · exact data_get p (Function.update v .unaryInput (v .widthBits)) .unaryInput
      · rfl
    · intro k hk
      have hn : k ≠ address .unaryInput := fun he=>hk 1 he.symm
      rw [data_update]
      exact Function.update_of_ne hn _ _

/-- Actual binary-to-marker procedure, not an advised width or loop count. -/
theorem width_unary (p : PS.Values) (v : Values) (he : v .counter=[]) :
    Runs program (2*(v .unaryInput).length+1+
      SemiprimeD1StackUnaryCounterExecution.loopTime (v .unaryInput).reverse 0+1)
      .widthUnary (data p v) .makeZero
      (data p (Function.update (Function.update v .unaryInput []) .counter
        (SemiprimeD1StackUnaryCounterExecution.markers (SemiprimeBitArithmetic.bitValue (v .unaryInput))))) := by
  apply SemiprimeD1StackProcedureTrace.included_call program unaryStack Label.unary
    (by intro a b h; simpa only [unaryStack,Sum.inr.injEq,Sum.inl.injEq] using h)
    U.code .reverse (fun _=>rfl) .widthUnary .makeZero rfl _
    (SemiprimeD1StackUnaryCounter.state (some .reverse) none (v .unaryInput) [] [] [])
    (SemiprimeD1StackUnaryCounter.state none none [] [] []
      (SemiprimeD1StackUnaryCounterExecution.markers (SemiprimeBitArithmetic.bitValue (v .unaryInput))))
  · rfl
  · rfl
  · exact SemiprimeD1StackUnaryCounterExecution.source_run (v .unaryInput)
  · constructor
    · intro k
      rw [unary_project]
      simp only [SemiprimeD1StackUnaryCounter.state,he]
    · intro k hk; rfl
  · constructor
    · intro k
      rw [unary_project]
      cases k <;> simp [SemiprimeD1StackUnaryCounter.state,SemiprimeD1StackAdder.store]
    · intro k hk
      have hi : k ≠ address .unaryInput := fun he=>hk .left he.symm
      have ho : k ≠ address .counter := fun he=>hk .output he.symm
      rw [data_update,data_update]
      simp only [Function.update_of_ne hi,Function.update_of_ne ho]

end RiemannGaussian.SemiprimeD1StackLeafAcquisition
