/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectedKeysLoop
import RiemannGaussian.SemiprimeD1StackSourceSelectedKeysSetup
import RiemannGaussian.SemiprimeD1StackSourceSelectedKeysFinish
/-! # Whole same-program selected-key source from actual complete cache and occurrence bytes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectedKeysExecution
open SemiprimeD1StackSourceSelectedKeys SemiprimeD1StackSourceSelectedKeysEncoding
open SemiprimeD1StackSourceSelectedKeysPrimitives SemiprimeD1StackSourceSelectedKeysView
open SemiprimeD1StackSourceSelectedKeysLoop SemiprimeD1StackSourceSelectedKeysSetup SemiprimeD1StackSourceSelectedKeysFinish
open SemiprimeD1StackProcedureTrace
/-- Own whole trace clock includes every input copy, lookup, frame, byte drain, both reversals and final halt. -/
def runBound (i:Inputs) :Nat :=setupTime i+rowsTime i i.rows+finishTime i (stream i.ids i.rows).reverse+1
/-- The complete actual source returns EXACT chronological oldjoint key-vector bytes from the retained full dictionary. -/
theorem source_trace (i:Inputs) (hc:Complete i) :
    ∃q,q+1 ≤ runBound i ∧ Runs program q .start (source i).data .done (result i) :=by
  have h0:=setup_run i
  obtain ⟨q,hq,h1⟩:=rows_run i i.rows [] hc
  simp only [List.append_nil] at h1
  have h2:=finish_run i (stream i.ids i.rows).reverse
  rw [List.reverse_reverse,stream_vector] at h2
  refine ⟨_,?_,join (join h0 h1) h2⟩
  unfold runBound
  omega
/-- Whole source includes its actual literal halt, clearing both flags and real return frames. -/
theorem source_run (i:Inputs) (hc:Complete i) :
    ∃q ≤ runBound i,SemiprimeD1StackCalls.run program q (source i)=some (done i) :=by
  obtain ⟨q,hq,hr⟩:=source_trace i hc
  obtain ⟨finish,hf,hAt⟩:=hr [] (source i) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (result i) [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- Genuine finite-machine source certificate uses the actual acquired multiword bank, with complete-cache lineage explicit. -/
noncomputable def selectedKeysInTime (i:Inputs) (hc:Complete i) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (source i))
      (some (SemiprimeD1StackCalls.configuration (done i))) (runBound i) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .source) (aux .output) .start program
  let h:=source_run i hc
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackSourceSelectedKeysExecution
