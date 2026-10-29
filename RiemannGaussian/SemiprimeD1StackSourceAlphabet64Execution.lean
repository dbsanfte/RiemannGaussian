/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Source
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Finish
/-! # Whole actual unary-width alphabet source: enumeration, every physical row and real halt -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceAlphabet64Execution
open SemiprimeD1StackSourceAlphabet64 SemiprimeD1StackSourceAlphabet64Encoding
open SemiprimeD1StackSourceAlphabet64Source SemiprimeD1StackSourceAlphabet64Primitives
open SemiprimeD1StackSourceAlphabet64Rows SemiprimeD1StackSourceAlphabet64Loop
open SemiprimeD1StackSourceAlphabet64Finish SemiprimeD1StackProcedureTrace
/-- Whole fixed-program clock pays real setup/enum, all raw input bytes, each actual
row normalization/frame/cleanup and the sole whole final log reversal/halt. -/
def runBound (a:Nat) :Nat :=
  95*a+100*(6*a+1)*2^(6*a)+21+
  5*(SemiprimeD1TensorTapeCodec.vectorBits (words a)).length+4+
  (2000*(a+1)*(words a).length+1)+2*(stream a (words a)).length+4+1
/-- The actual raw counter vector is copied ONCE; every acquired binary-power word remains literal. -/
theorem copy_stream (a:Nat) :
    Runs program (5*(SemiprimeD1TensorTapeCodec.vectorBits (words a)).length+4) .copyStream (enumerated a) .header
      (boundary (enumerated a) (SemiprimeD1TensorTapeCodec.vectorBits (words a)) []) :=by
  have h:=copy_call .stream .copyStream .header rfl (enumerated a) rfl rfl
  have he:Function.update (enumerated a) (copyStack .stream 1) (enumerated a (copyStack .stream 0))=
      boundary (enumerated a) (SemiprimeD1TensorTapeCodec.vectorBits (words a)) []:=by
    funext k
    rcases k with k|k
    · rfl
    · cases k <;> rfl
  rw [he] at h
  exact h
/-- Generic final framing/projection lemma avoids any evaluated original-width native word source. -/
theorem finished_result (a:Nat) :finished (enumerated a) a (words a)=result a :=by
  unfold finished
  rw [stream_records]
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Whole SAME literal source, from actual unary markers only; every compact candidate
and every actual colour field is acquired, framed and returned in original chronological order. -/
theorem source_trace (a:Nat) :
    ∃q,q+1 ≤ runBound a ∧ Runs program q .start (input (List.replicate a true)) .done (result a) :=by
  obtain ⟨e,he,h0⟩:=prefix_run a
  have h1:=copy_stream a
  obtain ⟨r,hr,h2⟩:=rows_run (enumerated a) a (words a) [] (word_width a) rfl rfl rfl rfl rfl rfl
  rw [List.append_nil] at h2
  have h3:=finish_run (enumerated a) a (words a) rfl
  rw [finished_result] at h3
  have hall:=compose (compose (compose h0 h1) h2) h3
  exact ⟨_,by unfold runBound;omega,hall⟩
/-- Actual complete halt with all scratch/flags/real frames clear and all actual binary power words retained. -/
theorem source_run (a:Nat) :
    ∃q ≤ runBound a,SemiprimeD1StackCalls.run program q (initial (List.replicate a true))=some (done a) :=by
  obtain ⟨q,hq,hr⟩:=source_trace a
  obtain ⟨finish,hf,hAt⟩:=hr [] (initial (List.replicate a true)) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (result a) [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- Genuine fixed finite-machine source certificate uses THIS complete own clock,
not a transported old histogram/classified report or an external candidate body. -/
noncomputable def alphabetInTime (a:Nat) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (List.replicate a true)))
      (some (SemiprimeD1StackCalls.configuration (done a))) (runBound a) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .source) (aux .output) .start program
  let h:=source_run a
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackSourceAlphabet64Execution
