/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexProductProjection
/-! # Actual original-header context and unit setup inside the product caller -/
set_option autoImplicit false
set_option synthInstance.maxSize 65536
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackVertexProductSetup
open SemiprimeD1StackVertexProduct SemiprimeD1StackVertexProductState
open SemiprimeD1StackVertexProductProjection
open SemiprimeD1StackProcedureTrace (Runs)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1JetAxes (Context)

/-- Acquired context fields come from the original physical producers, not
prepared rank/precision-count answer words in the vertex-product entry. -/
theorem context_call (v : Values) (axisList : List ℕ) (hp : ∀q∈axisList,0<q)
    (ha : v .axes=vectorBits (axisList.map unary)) (hr : v .rank=[]) (hw : v .width=[]) :
    ∃ m ≤ 1000*(SemiprimeD1StackJetContextBounds.resource axisList (v .precision)+1)^2+1,
      Runs program m .start (data v) .prepared
        (data (Function.update (Function.update v .rank (unary axisList.prod)) .width
          (SemiprimeD1StackUnaryCounterExecution.markers (SemiprimeBitArithmetic.bitValue (v .precision))))) := by
  obtain ⟨m,hm,hsource⟩:=SemiprimeD1StackJetContextBounds.source_run_polynomial axisList hp (v .precision)
  refine ⟨m+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program contextStack Label.context contextStack_injective
    X.program .start (fun _=>rfl) .start .prepared rfl m
    (SemiprimeD1StackJetContext.initial (vectorBits (axisList.map unary)) (v .precision))
    (⟨none,none,none,SemiprimeD1StackJetContextCorrectness.finalData axisList (v .precision),[]⟩:
      SemiprimeD1StackCalls.State X.Stack X.Label)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hsource
  · constructor
    · intro k
      rw [context_project]
      fin_cases k <;> simp [SemiprimeD1StackJetContext.initial,SemiprimeD1StackJetContext.bank,
        SemiprimeD1StackJetContext.cached,X.axesCache,X.rankCache,X.widthCache,X.precisionBits,ha,hr,hw]
    · intro k hk
      rfl
  · constructor
    · intro k
      rw [context_project]
      fin_cases k <;> simp [SemiprimeD1StackJetContextCorrectness.finalData,
        SemiprimeD1StackJetContext.bank,SemiprimeD1StackJetContext.cached,
        SemiprimeD1StackJetContextExecution.ready,SemiprimeD1StackJetSuffix.data,SemiprimeD1StackAdder.store,
        X.axesCache,X.rankCache,X.widthCache,X.precisionBits,ha]
    · intro k hk
      have hnR : k ≠ address .rank := fun he=>hk X.rankCache he.symm
      have hnW : k ≠ address .width := fun he=>hk X.widthCache he.symm
      rw [data_update,data_update]
      simp only [Function.update_of_ne hnW,Function.update_of_ne hnR]

/-- Actual literal-unit setup inside the product caller uses only the already
acquired context caches and physically creates its canonical dense vector. -/
theorem unit_call (ctx : Context) (v : Values) (hw : (v .width).length=ctx.precision)
    (hr : (v .rank).length=ctx.rank) (hleft : v .left=[]) (hprod : v .product=[]) (hout : v .result=[]) :
    Runs program (SemiprimeD1StackJetUnitExecution.totalTime (v .width) (v .rank)+1) .prepared (data v) .unitDone
      (data (Function.update v .result (vectorBits (SemiprimeD1JetAffineCoefficient.one ctx).words))) := by
  apply SemiprimeD1StackProcedureInclusion.included_call program unitStack Label.unit unitStack_injective
    U.program .seed0 (fun _=>rfl) .prepared .unitDone rfl _
    (SemiprimeD1StackJetUnit.initial (v .width) (v .rank))
    (⟨none,none,none,SemiprimeD1StackJetUnit.bank (v .width) (v .rank) [] []
      (vectorBits (SemiprimeD1JetAffineCoefficient.one ctx).words),[]⟩:
      SemiprimeD1StackCalls.State U.Stack U.Label)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackJetUnitExecution.source_run ctx (v .width) (v .rank) hw hr
  · constructor
    · intro k
      rw [unit_project]
      fin_cases k <;> simp [SemiprimeD1StackJetUnit.initial,SemiprimeD1StackJetUnit.bank,
        SemiprimeD1StackJetAdd.store,SemiprimeD1StackJetScalarAdd.store,
        U.widthCache,U.rankCache,U.output,hleft,hprod,hout]
    · intro k hk
      rfl
  · constructor
    · intro k
      rw [unit_project]
      fin_cases k <;> simp [SemiprimeD1StackJetUnit.bank,SemiprimeD1StackJetAdd.store,
        SemiprimeD1StackJetScalarAdd.store,U.widthCache,U.rankCache,U.output,hleft,hprod]
    · intro k hk
      have hn : k ≠ address .result := fun he=>hk U.output he.symm
      rw [data_update]
      exact Function.update_of_ne hn _ _

end RiemannGaussian.SemiprimeD1StackVertexProductSetup
