/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectionAcquirePrimitives
/-! # Four real complete acquisition calls with all other154-role fields retained -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireCalls
open SemiprimeD1StackSourceSelectionAcquire SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- One real complete occurrence source call pays its own clock and preserves every other physical word. -/
theorem occurrence_call (n:Nat) (rows:List (List (List Bool))) (alphabet:Alpha.Stack→List Bool) (selector:Select.Stack→List Bool) (keys:Keys.Stack→List Bool) (scratch:List Bool) :
    ∃t ≤ SemiprimeD1StackSourceOccurrencesExecution.timeBound n rows+1,Runs program t (ctl .start)
      (data (SemiprimeD1StackSourceOccurrencesExecution.source n rows).data alphabet selector keys scratch) (ctl .alphabet) (data (SemiprimeD1StackSourceOccurrencesExecution.done n rows).data alphabet selector keys scratch) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackSourceOccurrencesExecution.source_run n rows
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program occurrenceStack Label.occurrence
    (fun _ _ h=>Sum.inl.inj (h)) Occ.program (.local .start) (fun _=>rfl) (ctl .start) (ctl .alphabet) rfl t
    (SemiprimeD1StackSourceOccurrencesExecution.source n rows) (SemiprimeD1StackSourceOccurrencesExecution.done n rows) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- One real complete alphabet source call pays its own clock and preserves every other physical word. -/
theorem alphabet_call (a:Nat) (occurrences:Occ.Stack→List Bool) (selector:Select.Stack→List Bool) (keys:Keys.Stack→List Bool) (scratch:List Bool) :
    ∃t ≤ 10000*(a+1)*(64^a+1)+1,Runs program t (ctl .alphabet)
      (data occurrences (Alpha.initial (List.replicate a true)).data selector keys scratch) (ctl (.copy .occurrences)) (data occurrences (SemiprimeD1StackSourceAlphabet64Encoding.done a).data selector keys scratch) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackSourceAlphabet64Bounds.source_run_bounded a
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program alphabetStack Label.alphabet
    (fun _ _ h=>Sum.inl.inj (Sum.inr.inj (h))) Alpha.program .start (fun _=>rfl) (ctl .alphabet) (ctl (.copy .occurrences)) rfl t
    (Alpha.initial (List.replicate a true)) (SemiprimeD1StackSourceAlphabet64Encoding.done a) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · exact (hk k rfl).elim
        · rfl
/-- One real complete selector source call pays its own clock and preserves every other physical word. -/
theorem selector_call (i:SemiprimeD1StackSourceIncidenceSelectExecution.Inputs) (occurrences:Occ.Stack→List Bool) (alphabet:Alpha.Stack→List Bool) (keys:Keys.Stack→List Bool) (scratch:List Bool) :
    ∃t ≤ SemiprimeD1StackSourceIncidenceSelectClock.polynomial i+1,Runs program t (ctl .select)
      (data occurrences alphabet (SemiprimeD1StackSourceIncidenceSelectExecution.source i).data keys scratch) (ctl (.copy .dictionary)) (data occurrences alphabet (SemiprimeD1StackSourceIncidenceSelectExecution.done i).data keys scratch) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackSourceIncidenceSelectClock.source_run_bounded i
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program selectorStack Label.selector
    (fun _ _ h=>Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (h)))) Select.program (.local .start) (fun _=>rfl) (ctl .select) (ctl (.copy .dictionary)) rfl t
    (SemiprimeD1StackSourceIncidenceSelectExecution.source i) (SemiprimeD1StackSourceIncidenceSelectExecution.done i) _ _ rfl rfl rfl rfl hr
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
/-- One real complete keys source call pays its own clock and preserves every other physical word. -/
theorem keys_call (i:SemiprimeD1StackSourceSelectedKeysEncoding.Inputs) (hc:SemiprimeD1StackSourceSelectedKeysEncoding.Complete i) (occurrences:Occ.Stack→List Bool) (alphabet:Alpha.Stack→List Bool) (selector:Select.Stack→List Bool) (scratch:List Bool) :
    ∃t ≤ SemiprimeD1StackSourceSelectedKeysBounds.polynomial i+1,Runs program t (ctl .keys)
      (data occurrences alphabet selector (SemiprimeD1StackSourceSelectedKeysEncoding.source i).data scratch) (ctl .done) (data occurrences alphabet selector (SemiprimeD1StackSourceSelectedKeysEncoding.done i).data scratch) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackSourceSelectedKeysBounds.source_run_bounded i hc
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program keyStack Label.keys
    (fun _ _ h=>Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (h))))) Keys.program .start (fun _=>rfl) (ctl .keys) (ctl .done) rfl t
    (SemiprimeD1StackSourceSelectedKeysEncoding.source i) (SemiprimeD1StackSourceSelectedKeysEncoding.done i) _ _ rfl rfl rfl rfl hr
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
          · rfl
          · rcases k with k|k
            · exact (hk k rfl).elim
            · rfl
end RiemannGaussian.SemiprimeD1StackSourceSelectionAcquireCalls

