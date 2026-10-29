/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryDenominatorLoop
/-! # Whole actual two-tape common-denominator acquisition source
One physical copy retains the actual row tape. Every marker/field/product/fit
and the real halt are joined in this single finite program and single own clock.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryDenominatorExecution
open SemiprimeD1StackRecoveryDenominator SemiprimeD1StackRecoveryDenominatorState
open SemiprimeD1StackRecoveryDenominatorPrimitives SemiprimeD1StackRecoveryDenominatorView
open SemiprimeD1StackRecoveryDenominatorEncoding SemiprimeD1StackRecoveryDenominatorLoop
open SemiprimeD1StackProcedureTrace
/-- Actual source copy and literal one seed; no accumulator word is supplied. -/
theorem setup_run (rows widthTemplate:List Bool):
    Runs program (5*rows.length+5) (.local .start) (initial rows widthTemplate).data (.local (.loop false))
      (data (bank rows rows widthTemplate [] [] [true] [])):=by
  rw [initial_data,initial_bank]
  have h0:=copy_view true (.local .start) (.local .seed) (bank rows [] widthTemplate [] [] [] []) rfl rfl
  change Runs program (5*rows.length+4) (.local .start) (data (bank rows [] widthTemplate [] [] [] []))
    (.local .seed) (data (Function.update (bank rows [] widthTemplate [] [] [] []) (.aux .reader) (rows++[]))) at h0
  rw [List.append_nil,update_reader] at h0
  have h1:=push_view (.local .seed) (.local (.loop false)) (.mul (.inl .right)) true
    (bank rows rows widthTemplate [] [] [] []) rfl
  rw [update_accumulator] at h1
  have h:=join h0 h1
  convert h using 1;rfl
/-- Exact old-empty-exception physical output description for the complete acquired stream. -/
def result (rs:List Row) (widthTemplate:List Bool):List Bool:=answer widthTemplate false rs [true]
/-- Actual all19-role final halt, retaining the original row tape and template literally. -/
def done (rs:List Row) (widthTemplate:List Bool):C.State Stack Label:=
  ⟨none,none,none,data (bank (tape rs) [] widthTemplate [] [] [] (result rs widthTemplate)),[]⟩
/-- Same actual source clock immediately before its genuine final halt. -/
def bodyTime (rs:List Row) (widthTemplate:List Bool):Nat:=5*(tape rs).length+5+budget widthTemplate false rs [true]
/-- Exact complete actual source transition count, including every real return and halt. -/
def timeBound (rs:List Row) (widthTemplate:List Bool):Nat:=bodyTime rs widthTemplate+1
/-- Whole literal physical source, from two actual tapes through all raw products and the final width fit. -/
theorem source_trace (rs:List Row) (widthTemplate:List Bool):
    Runs program (bodyTime rs widthTemplate) (.local .start) (initial (tape rs) widthTemplate).data
      (.local .done) (done rs widthTemplate).data:=by
  exact join (setup_run (tape rs) widthTemplate) (loop_run false rs (tape rs) widthTemplate [true] (fun _=>rfl))
/-- SAME parameterless program actually halts from the actual row/template bytes only. -/
theorem source_run (rs:List Row) (widthTemplate:List Bool):
    SemiprimeD1StackCalls.run program (timeBound rs widthTemplate) (initial (tape rs) widthTemplate)=some (done rs widthTemplate):=by
  obtain ⟨out,hr,ha⟩:=source_trace rs widthTemplate [] (initial (tape rs) widthTemplate) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (.local .done) rfl (done rs widthTemplate).data [] out ha
  rw [timeBound,SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
  exact hh
/-- Whole output projection is exact actual bytes, including nil's literal one. -/
theorem output_result (rs:List Row) (widthTemplate:List Bool):(done rs widthTemplate).data output=result rs widthTemplate:=rfl
/-- All original input words are retained and every other allocated role is physically empty except the actual output. -/
theorem result_bank (rs:List Row) (widthTemplate:List Bool):
    (done rs widthTemplate).data=Function.update (input (tape rs) widthTemplate) output (result rs widthTemplate):=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> rfl
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
  · rcases k with k|k
    · fin_cases k <;> rfl
    · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackRecoveryDenominatorExecution
