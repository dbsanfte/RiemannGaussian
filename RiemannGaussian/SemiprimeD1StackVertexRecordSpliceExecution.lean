/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexRecordSplice
/-! # Exact EOF cancellation with no accumulated-history traversal
Every new record bit is physically reversed once. The native row prefix is
only an output specification; it is never supplied to finite machine control.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackVertexRecordSpliceExecution
open SemiprimeD1StackVertexRecordSplice SemiprimeD1StackProcedureTrace
/-- Actual reversal consumes only the new record while prepending onto the unchanged old tail. -/
theorem reverse_call (record history : List Bool) :
    Runs program (2*record.length+3) (.local .start) (data record history) (.local .strip) (data [] (record.reverse++history)) := by
  apply included_call program id Label.reverse Function.injective_id SemiprimeD1StackReverseWord.code 0
    (fun _=>rfl) (.local .start) (.local .strip) rfl (2*record.length+2)
    (SemiprimeD1StackReverseWord.state none record history) (SemiprimeD1StackReverseWord.done (record.reverse++history))
    _ _ rfl rfl (SemiprimeD1StackReverseWord.reverse_run record history none)
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;exact (hk k rfl).elim
/-- The new singleton EOF is now at the front and is removed by ONE literal Boolean pop. -/
theorem strip_run (row history : List Bool) :
    Runs program 1 (.local .strip) (data [] (false::(row.reverse++history))) (.local .done) (data [] (row.reverse++history)) := by
  apply one_base program (.local .strip) (.local .done) (.pop 1 (.local .reject) (.local .done) (.local .reject)) _ _ rfl rfl
  funext k
  fin_cases k <;> rfl
/-- Whole SAME actual two-word source, exact raw cancellation, cleared flags and true halt. -/
theorem source_run (row history : List Bool) :
    SemiprimeD1StackCalls.run program (timeBound row) (initial (row++[false]) history)=some (done (row.reverse++history)) := by
  have h0:=reverse_call (row++[false]) history
  simp only [List.reverse_append,List.reverse_singleton,List.singleton_append] at h0
  have h1:=strip_run row history
  have h:=runs_trans program _ _ _ _ _ _ _ _ h0 h1
  obtain ⟨finish,hfinish,hAt⟩:=h [] (initial (row++[false]) history) ⟨rfl,rfl,rfl⟩
  have hhalt:=halt_run program (.local .done) rfl (data [] (row.reverse++history)) [] finish hAt
  have hr : SemiprimeD1StackCalls.run program ((2*(row++[false]).length+3+1)+1) (initial (row++[false]) history)=
      some (done (row.reverse++history)) := by
    rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some]
    exact hhalt
  have hclock : timeBound row=(2*(row++[false]).length+3+1)+1 := by
    simp only [timeBound,List.length_append,List.length_singleton]
    omega
  rw [hclock]
  exact hr
/-- SAME actual caller trace preserves arbitrary real outer returns and stale transient flags. -/
theorem source_trace (row history : List Bool) :
    Runs program (timeBound row-1) (.local .start) (data (row++[false]) history) (.local .done) (data [] (row.reverse++history)) := by
  have h0:=reverse_call (row++[false]) history
  simp only [List.reverse_append,List.reverse_singleton,List.singleton_append] at h0
  have h:=runs_trans program _ _ _ _ _ _ _ _ h0 (strip_run row history)
  convert h using 1
  simp only [timeBound,List.length_append,List.length_singleton]
  omega
/-- Exact bit-machine clock depends on the NEW row only; the old history is never recopied. -/
def machineSplice (row history : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (row++[false]) history))
      (some (SemiprimeD1StackCalls.configuration (done (row.reverse++history)))) (timeBound row) := by
  apply SemiprimeD1StackCalls.evalsCorrect 0 1 (.local .start) program
  exact ⟨⟨timeBound row,source_run row history⟩,le_rfl⟩
end RiemannGaussian.SemiprimeD1StackVertexRecordSpliceExecution
