/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetFoldSpec
/-! # Actual original-header acquisition and the same-program acquired-cache entry
The full entry accepts no rank or precision-count answer. The prepared entry is
exactly the state reached after the real immutable context source returns.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackJetFoldContext
open SemiprimeD1StackJetFold SemiprimeD1StackJetFoldState SemiprimeD1StackJetFoldProjection
open SemiprimeD1StackJetFoldSpec SemiprimeD1StackProcedureTrace
open SemiprimeD1JetAxes (Context)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeBitArithmetic (bitValue)
local notation "ctl" => Label.local
/-- Proof-side interpretation of the two original actual header words. -/
def context (axes:List Nat) (precision:List Bool):Context:=⟨axes,bitValue precision⟩
/-- Exact original inputs and actual acquired counter words, not an instruction operand. -/
def acquiredHeader (axes:List Nat) (precision children:List Bool):Header:=
  ⟨vectorBits (axes.map unary),precision,children,unary axes.prod,
    SemiprimeD1StackUnaryCounterExecution.markers (bitValue precision)⟩
/-- Actual acquired counters satisfy every physical arithmetic context relation. -/
theorem header_matches (axes:List Nat) (precision children:List Bool):
    Matches (context axes precision) (acquiredHeader axes precision children):=by
  constructor
  · rfl
  · exact List.length_replicate
  · rfl
/-- SAME-program cache entry is the literal complete context-source output, with all new work words empty. -/
def ready (axes:List Nat) (precision children:List Bool):C.State Stack Label:=
  ⟨some (ctl .prepared),none,none,data (bank (acquiredHeader axes precision children) [] [] [] [] [] [] [] [] []),[]⟩
/-- The context source's actual final data is its original input plus its two real acquired counters. -/
theorem context_result_updates (axes:List Nat) (precision:List Bool):
    Function.update (Function.update
      (SemiprimeD1StackJetContext.initial (vectorBits (axes.map unary)) precision).data
      X.rankCache (unary axes.prod)) X.widthCache
        (SemiprimeD1StackUnaryCounterExecution.markers (bitValue precision))=
      SemiprimeD1StackJetContextCorrectness.finalData axes precision:=by
  funext k;fin_cases k <;> rfl
/-- The full source physically acquires its own rank/precision caches and pays the real context call/return. -/
theorem context_call (axes:List Nat) (hp:∀q∈axes,0 < q) (precision children:List Bool):
    ∃time ≤ SemiprimeD1StackJetContextCorrectness.budget axes precision+1,
      Runs program time (ctl .start) (initial (vectorBits (axes.map unary)) precision children).data
        (ctl .prepared) (ready axes precision children).data:=by
  obtain ⟨time,ht,hr⟩:=SemiprimeD1StackJetContextCorrectness.source_run axes hp precision
  let v:=values (vectorBits (axes.map unary)) precision children [] [] [] [] [] [] [] [] [] [] []
  let source:=SemiprimeD1StackJetContext.initial (vectorBits (axes.map unary)) precision
  let out:C.State X.Stack X.Label:=⟨none,none,none,SemiprimeD1StackJetContextCorrectness.finalData axes precision,[]⟩
  have hin:SemiprimeD1StackMultiplierLink.DataRel contextStack (data v) source.data (data v):=by
    constructor
    · intro k;rw [data_context];fin_cases k <;> rfl
    · intro k _;rfl
  rw [initial_data]
  refine ⟨time+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program contextStack Label.context context_injective
    X.program .start (fun _=>rfl) (ctl .start) (ctl .prepared) rfl time source out _ _ rfl rfl rfl rfl hr hin
  have h0:=SemiprimeD1StackMultiplierLink.data_update contextStack context_injective (data v) source.data (data v) hin
    X.rankCache (unary axes.prod)
  have h1:=SemiprimeD1StackMultiplierLink.data_update contextStack context_injective (data v) _ _ h0
    X.widthCache (SemiprimeD1StackUnaryCounterExecution.markers (bitValue precision))
  rw [context_result_updates] at h1
  change SemiprimeD1StackMultiplierLink.DataRel contextStack (data v) out.data
    (Function.update (Function.update (data v) (address .rank) (unary axes.prod)) (address .width)
      (SemiprimeD1StackUnaryCounterExecution.markers (bitValue precision))) at h1
  rw [←data_update,←data_update] at h1
  exact h1
end RiemannGaussian.SemiprimeD1StackJetFoldContext
