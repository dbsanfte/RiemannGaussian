/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesLoop
/-! # Whole actual two-tape recovery-entry acquisition source
The same finite25-role program copies rows, physically seeds the output false,
parses all source fields, acquires actual children, frames/cleans every entry,
performs one final reverse and genuinely halts. Both originals are retained.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesExecution
open SemiprimeD1StackRecoveryEntries SemiprimeD1StackRecoveryEntriesState
open SemiprimeD1StackRecoveryEntriesPrimitives SemiprimeD1StackRecoveryEntriesLoop
open SemiprimeD1StackRecoveryEntriesEncoding (childTape outputTape)
open SemiprimeD1StackRecoveryEntriesOrder (chunks output_chunks)
open SemiprimeD1StackRecoveryDenominatorEncoding (Row tape)
open SemiprimeD1StackProcedureTrace
/-- Actual row copy and literal false output sentinel, paid before the first row is read. -/
theorem setup_run (rows children:List Bool):
    Runs program (5*rows.length+5) (.local .start) (initial rows children).data (.local .loop)
      (data children (words rows rows (fun _=>[]) [] [] [] [] [] [false])):=by
  rw [initial_data]
  have h0:=copy_run children (words rows [] (fun _=>[]) [] [] [] [] [] [])
  change Runs program (5*rows.length+4) (.local .start)
    (data children (words rows [] (fun _=>[]) [] [] [] [] [] [])) (.local .sentinel)
    (data children (Function.update (words rows [] (fun _=>[]) [] [] [] [] [] []) .reader (rows++[]))) at h0
  rw [List.append_nil,update_reader] at h0
  have h1:=push_run (.local .sentinel) (.local .loop) .output false children
    (words rows rows (fun _=>[]) [] [] [] [] [] []) rfl
  rw [update_out] at h1
  have h:=join h0 h1
  exact h
/-- The identical actual whole-source clock before its final genuine halt. -/
def bodyTime (rows:List Row) (children:List (List (List Bool))):Nat:=5*(tape rows).length+5+budget children rows []
/-- Exact complete25-role primitive count including every actual call/return, row logger and halt. -/
def timeBound (rows:List Row) (children:List (List (List Bool))):Nat:=bodyTime rows children+1
/-- Actual whole halt retains two original tapes and all private/index/query-shadow roles are empty. -/
def done (rows:List Row) (children:List (List (List Bool))):C.State Stack Label:=
  ⟨none,none,none,data (childTape children) (words (tape rows) [] (fun _=>[]) [] [] [] [] [] (outputTape rows children)),[]⟩
/-- Complete actual source from the two physical input words, without template/Entry/getter/answer advice. -/
theorem source_trace (rows:List Row) (children:List (List (List Bool))):
    Runs program (bodyTime rows children) (.local .start) (initial (tape rows) (childTape children)).data
      (.local .done) (done rows children).data:=by
  have h0:=setup_run (tape rows) (childTape children)
  have h1:=loop_run children rows (tape rows) [] [false]
  simp only [List.reverse_nil,List.nil_append,←output_chunks] at h1
  exact join h0 h1
/-- SAME literal finite program genuinely halts after acquiring all original-order entries from physical source/child tapes. -/
theorem source_run (rows:List Row) (children:List (List (List Bool))):
    SemiprimeD1StackCalls.run program (timeBound rows children) (initial (tape rows) (childTape children))=some (done rows children):=by
  obtain ⟨out,hr,ha⟩:=source_trace rows children [] (initial (tape rows) (childTape children)) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (.local .done) rfl (done rows children).data [] out ha
  rw [timeBound,SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
  exact hh
/-- Literal physical output is exactly the full four-field entry tape. -/
theorem output_tape (rows:List Row) (children:List (List (List Bool))):(done rows children).data output=outputTape rows children:=rfl
/-- Both original input tapes survive; every other22 private/counter/shadow/reader tape is empty except actual output. -/
theorem result_bank (rows:List Row) (children:List (List (List Bool))):
    (done rows children).data=Function.update (input (tape rows) (childTape children)) output (outputTape rows children):=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesExecution
