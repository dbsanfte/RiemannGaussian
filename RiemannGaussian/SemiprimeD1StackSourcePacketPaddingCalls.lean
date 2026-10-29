/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourcePacketPaddingPrimitives
/-! # Real whole frequency acquisition once and optional actual counter-entry calls -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourcePacketPaddingCalls
open SemiprimeD1StackSourcePacketPadding SemiprimeD1StackSourcePacketPaddingPrimitives
open SemiprimeD1StackProcedureTrace
/-- The whole actual key-only producer runs once, paying all real nested calls and preserving the acquired exponent/output fields. -/
theorem frequency_call (before:Stack→List Bool) (keys:List (List Bool))
    (hi:∀k,before (frequencyStack k)=(SemiprimeD1StackSourceKeyFrequencyEncoding.source keys).data k) :
    ∃q≤ SemiprimeD1StackSourceKeyFrequencyExecution.runBound keys+1,Runs program q .start before .copyCut
      (Sum.elim (SemiprimeD1StackSourceKeyFrequencyEncoding.done keys).data (fun k=>before (aux k))) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackSourceKeyFrequencyExecution.source_run keys
  refine ⟨q+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program frequencyStack Label.frequency frequency_injective
    F.program .start (fun _=>rfl) .start .copyCut rfl q
    (SemiprimeD1StackSourceKeyFrequencyEncoding.source keys) (SemiprimeD1StackSourceKeyFrequencyEncoding.done keys) _ _
    rfl rfl rfl rfl hr
  · exact ⟨hi,fun _ _=>rfl⟩
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- Only actual high-suffix bytes are incremented; every other frequency/cache/exponent word is retained exactly. -/
theorem counter_call (before:Stack→List Bool) (word:List Bool)
    (hw:before (frequencyStack F.oldCount)=word)
    (hn:before (frequencyStack (F.aux .incNext))=[])
    (hi:before (frequencyStack (F.aux .incScratch))=[])
    (ht:before (frequencyStack (F.aux .trimScratch))=[])
    (ho:before (frequencyStack (F.aux .count))=[])
    (hl:before (frequencyStack (F.lookupStack (.inl .left)))=[])
    (hr:before (frequencyStack (F.lookupStack (.inl .right)))=[]) :
    ∃q≤40*(word.length+1)+2,Runs program q (.cutDone true) before .prefix
      (Function.update (Function.update before (frequencyStack F.oldCount) []) (frequencyStack (F.aux .count))
        (SemiprimeD1StackSourceEnvironmentEncoding.successor word)) :=by
  let small:=fun k=>before (frequencyStack k)
  let start:C.State F.Stack F.Label:=⟨some .increment,none,none,small,[]⟩
  let stop:C.State F.Stack F.Label:=⟨none,none,none,Function.update (Function.update small F.oldCount []) (F.aux .count)
    (SemiprimeD1StackSourceEnvironmentEncoding.successor word),[]⟩
  obtain ⟨q,hq,htrace⟩:=SemiprimeD1StackSourceKeyFrequencyCounterEntry.source_run small word hw hn hi ht ho hl hr
  have hin:Link.DataRel frequencyStack before start.data before:=⟨fun _=>rfl,fun _ _=>rfl⟩
  have h0:=Link.data_update frequencyStack frequency_injective before start.data before hin F.oldCount []
  have h1:=Link.data_update frequencyStack frequency_injective before _ _ h0 (F.aux .count)
    (SemiprimeD1StackSourceEnvironmentEncoding.successor word)
  refine ⟨q+1,by omega,?_⟩
  exact SemiprimeD1StackProcedureCallsTrace.included_call program frequencyStack Label.frequency frequency_injective F.program
    .increment (fun _=>rfl) (.cutDone true) .prefix rfl q start stop before _ rfl rfl rfl rfl htrace hin h1
end RiemannGaussian.SemiprimeD1StackSourcePacketPaddingCalls
