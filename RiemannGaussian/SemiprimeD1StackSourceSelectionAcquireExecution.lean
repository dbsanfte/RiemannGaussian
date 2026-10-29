/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireEncoding
import RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireProjection
/-! # Whole actual original row/count/dimension-to-selected-keys acquisition
Four real sources and eleven physical copies are composed below. F, compact
keys, catalogue, powers, selected IDs, dictionary and output are all acquired
inside this fixed program. The graph and native runs occur in proofs only.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireExecution
open SemiprimeD1StackSourceSelectionAcquire SemiprimeD1StackSourceSelectionAcquireEncoding
open SemiprimeD1StackSourceSelectionAcquireCalls SemiprimeD1StackSourceSelectionAcquirePrimitives
open SemiprimeD1StackSourceSelectionAcquireSelectorInput SemiprimeD1StackSourceSelectionAcquireKeyInput
open SemiprimeD1StackSourceSelectionAcquireProjection SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Exact original acquired selector executes as one actual included whole source, with every other154-role word retained. -/
theorem selector_acquired_call (net:N.Network) (a:Nat) (occurrences:Occ.Stack→List Bool)
    (alphabet:Alpha.Stack→List Bool) (keys:Keys.Stack→List Bool) (scratch:List Bool) :
    ∃t ≤ selectorBound net a+1,Runs program t (ctl .select)
      (data occurrences alphabet (selectorSource net a).data keys scratch) (ctl (.copy .dictionary))
      (data occurrences alphabet (selectorDone net a).data keys scratch) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackSourceIncidenceSelectOriginal.acquired_source_run net.leftCount net.rows.length a
    (N.arity net.rows) (N.owner net.rows)
  refine ⟨t+1,by exact Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program selectorStack Label.selector
    (fun _ _ h=>Sum.inl.inj (Sum.inr.inj (Sum.inr.inj h))) Select.program (.local .start) (fun _=>rfl)
    (ctl .select) (ctl (.copy .dictionary)) rfl t (selectorSource net a) (selectorDone net a)
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · rcases k with k|k
          · exact (hk k rfl).elim
          · rfl
/-- Entire actual four-source acquisition, through all cleanup and immediately before the real halt. -/
theorem source_trace (net:N.Network) (a:Nat) :
    ∃t,t+1 ≤ timeBound net a ∧ Runs program t (ctl .start) (source net a).data (ctl .done) (result net a) :=by
  obtain ⟨b,hb,h0⟩:=occurrence_call net.leftCount (originalRows net) (Alpha.initial (List.replicate a true)).data
    (fun _=>[]) (fun _=>[]) []
  obtain ⟨c,hc,h1⟩:=alphabet_call a (occurrenceDone net).data (fun _=>[]) (fun _=>[]) []
  have h2:=selector_input_run (occurrenceDone net).data (alphabetDone a).data (fun _=>[])
  have hs:selectorReady (occurrenceDone net).data (alphabetDone a).data=(selectorSource net a).data:=
    selectorReady_original net a
  rw [hs] at h2
  obtain ⟨d,hd,h3⟩:=selector_acquired_call net a (occurrenceDone net).data (alphabetDone a).data (fun _=>[]) []
  have h4:=key_input_run (occurrenceDone net).data (alphabetDone a).data (selectorDone net a).data
  have hk:keyReady (selectorDone net a).data=(SemiprimeD1StackSourceSelectedKeysEncoding.source (keyInput net a)).data:=
    keyReady_original net.leftCount net.rows.length a (N.arity net.rows) (N.owner net.rows)
  rw [hk] at h4
  have hcomplete:SemiprimeD1StackSourceSelectedKeysEncoding.Complete (keyInput net a):=
    SemiprimeD1StackSourceSelectedKeysOriginal.original_complete net.leftCount net.rows.length 64 a
      (N.arity net.rows) (N.owner net.rows) [] [] (SemiprimeD1TensorTapeCodec.vectorBits (selectedIDs net a))
  obtain ⟨e,he,h5⟩:=keys_call (keyInput net a) hcomplete (occurrenceDone net).data (alphabetDone a).data (selectorDone net a).data []
  have h:=join (join (join (join (join h0 h1) h2) h3) h4) h5
  refine ⟨b+c+selectorCopyTime (occurrenceDone net).data (alphabetDone a).data+d+
      keyCopyTime (selectorDone net a).data+e,?_,h⟩
  unfold timeBound
  omega
/-- SAME literal154-role program from the original three physical words really halts at the complete acquired key/cache bank. -/
theorem source_run (net:N.Network) (a:Nat) :
    ∃t ≤ timeBound net a,SemiprimeD1StackCalls.run program t (source net a)=some (done net a) :=by
  obtain ⟨t,ht,h⟩:=source_trace net a
  obtain ⟨out,ho,ha⟩:=h [] (source net a) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result net a) [] out ha
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,ho,Option.bind_some];exact hh⟩
/-- Genuine compiled whole source certificate pays all four real acquisitions and eleven actual handoffs. -/
noncomputable def acquireInTime (net:N.Network) (a:Nat) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (source net a))
      (some (SemiprimeD1StackCalls.configuration (done net a))) (timeBound net a) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (occurrenceStack .rows) (keyStack (Keys.aux .output)) (ctl .start) program
  let h:=source_run net a
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireExecution
