/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseParametersPrimitives
/-! # Real parser, complete phase source, heap allocation and ordinal-log calls -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseParametersCalls
open SemiprimeD1StackRootPhaseParameters SemiprimeD1StackRootPhaseParametersEncoding
open SemiprimeD1StackRootPhaseParametersPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- One actual framed binary phase word is consumed, copied and validated physically. -/
theorem parse_call (bank:Stack→List Bool) (word tail:List Bool)
    (hi:bank (aux .reader)=frame word tail) (ho:bank (aux .index)=[])
    (hs:bank (aux .fieldScratch)=[]) (hv:bank (aux .valid)=[]) :
    Runs program (8*word.length+7) .parse bank .check
      (Function.update (Function.update (Function.update bank (aux .reader) tail) (aux .index) word) (aux .valid) [true]) :=by
  let before:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let after:SemiprimeD1StackBytecode.State F.Stack F.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:Link.DataRel fieldStack bank before.store bank:=by
    constructor
    · intro k;rcases k with k|k
      · cases k <;> simp [fieldStack,before,SemiprimeD1TensorTapeFieldBytecode.initial,
          SemiprimeD1TensorTapeFieldMachine.contents,hi,ho,hs]
      · cases k;exact hv
    · intro k _;rfl
  apply included_call program fieldStack Label.field field_injective F.code
    (F.active .tagPop (none,false)) (fun _=>rfl) .parse .check rfl (8*word.length+6)
    before after _ _ rfl rfl (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin
  have h0:=Link.data_update fieldStack field_injective bank before.store bank hin (.inl .input) tail
  have h1:=Link.data_update fieldStack field_injective bank _ _ h0 (.inl .output) word
  have h2:=Link.data_update fieldStack field_injective bank _ _ h1 (.inr ()) [true]
  have he:Function.update (Function.update (Function.update before.store (.inl .input) tail)
      (.inl .output) word) (.inr ()) [true]=after.store:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  simpa only [he,fieldStack] using h2
/-- Actual stopped phase data replaces only its literal forty-eight-role bank. -/
def replacePhase (bank:Stack→List Bool) (phase:P.Stack→List Bool) : Stack→List Bool :=
  data (fun k=>bank (gridStack k)) phase (fun k=>bank (aux k))
/-- One WHOLE phase source call acquires geometry, guard, metadata and binary P/D.
Rejected phases are actual stopped banks too and follow this identical call. -/
theorem phase_call (bank:Stack→List Bool) (a u edges:Nat) (t:List Bool)
    (hi:∀k,bank (phaseStack k)=P.input a u edges t [false,true] k) :
    ∃q≤SemiprimeD1StackPhaseWorkingPrecisionExecution.runBound a u edges t [false,true],
      Runs program (q+1) .phaseCall bank (.serialize 0)
        (replacePhase bank (SemiprimeD1StackPhaseWorkingPrecisionComponents.result a u edges t [false,true])) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackPhaseWorkingPrecisionExecution.source_run a u edges t [false,true]
  refine ⟨q,hq,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program phaseStack Label.phase phase_injective
    P.program .start (fun _=>rfl) .phaseCall (.serialize 0) rfl q
    (P.initial a u edges t [false,true])
    (SemiprimeD1StackPhaseWorkingPrecisionExecution.done a u edges t [false,true]) _ _ rfl rfl rfl rfl hr
  · constructor
    · exact hi
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · exact (hk k rfl).elim
        · rfl
/-- Actual allocation physically copies the old counter to the stable reference,
increments the real counter and writes every byte of the complete phase record. -/
theorem allocate_call (bank:Stack→List Bool) (hs:bank (aux .recordScratch)=[])
    (hr:bank (aux .reference)=[]) (ht:bank (aux .counterScratch)=[]) :
    Runs program (5*(bank (aux .counter)).length+6*(bank (aux .record)).length+8) .allocate bank .logReference
      (Function.update (Function.update (Function.update bank (aux .heap)
        (frame (bank (aux .record)) (bank (aux .heap)))) (aux .counter) (true::bank (aux .counter)))
        (aux .reference) (bank (aux .counter))) :=by
  let before:=SemiprimeD1StackHeapAllocate.state 0 none (bank (aux .record)) (bank (aux .heap)) [] (bank (aux .counter)) [] []
  let after:=SemiprimeD1StackHeapAllocate.done (bank (aux .record))
    (frame (bank (aux .record)) (bank (aux .heap))) (true::bank (aux .counter)) (bank (aux .counter))
  have hin:Link.DataRel heapStack bank before.store bank:=by
    constructor
    · intro k;fin_cases k
      · rfl
      · rfl
      · exact hs
      · rfl
      · exact hr
      · exact ht
    · intro k _;rfl
  apply included_call program heapStack Label.allocator heap_injective SemiprimeD1StackHeapAllocate.code
    0 (fun _=>rfl) .allocate .logReference rfl
    (5*(bank (aux .counter)).length+6*(bank (aux .record)).length+7) before after _ _ rfl rfl
    (SemiprimeD1StackHeapAllocate.allocate_run _ _ _ none) hin
  have h0:=Link.data_update heapStack heap_injective bank before.store bank hin 1
    (frame (bank (aux .record)) (bank (aux .heap)))
  have h1:=Link.data_update heapStack heap_injective bank _ _ h0 3 (true::bank (aux .counter))
  have h2:=Link.data_update heapStack heap_injective bank _ _ h1 4 (bank (aux .counter))
  have he:Function.update (Function.update (Function.update before.store 1
      (frame (bank (aux .record)) (bank (aux .heap)))) 3 (true::bank (aux .counter))) 4
      (bank (aux .counter))=after.store:=by funext k;fin_cases k <;> rfl
  simpa only [he,show heapStack 1=aux .heap from rfl,show heapStack 3=aux .counter from rfl,show heapStack 4=aux .reference from rfl] using h2
/-- The reference logger executes the literal restoring body; the ordinal itself
was acquired from the real counter, not supplied as a native append result. -/
theorem reference_call (bank:Stack→List Bool) (hs:bank (aux .refScratch)=[]) :
    ∃q≤6*(2*(bank (aux .reference)).length+3),
      Runs program (q+1) .logReference bank (.clear 0)
        (Function.update bank (aux .refsHistory)
          ((true::frame (bank (aux .reference)) []).reverse++bank (aux .refsHistory))) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackAssignmentBody.body_run (bank (aux .reference)) (bank (aux .refsHistory))
  refine ⟨q,hq,?_⟩
  let before:SemiprimeD1StackBytecode.State B.Stack B.Label:=
    ⟨some B.entry,none,SemiprimeD1StackAssignmentBody.contents (bank (aux .reference)) [] (bank (aux .refsHistory))⟩
  let after:SemiprimeD1StackBytecode.State B.Stack B.Label:=
    ⟨none,none,SemiprimeD1StackAssignmentBody.contents (bank (aux .reference)) []
      ((true::frame (bank (aux .reference)) []).reverse++bank (aux .refsHistory))⟩
  have hin:Link.DataRel bodyStack bank before.store bank:=by
    constructor
    · intro k;cases k
      · rfl
      · exact hs
      · rfl
    · intro k _;rfl
  apply included_call program bodyStack Label.body body_injective B.code B.entry (fun _=>rfl)
    .logReference (.clear 0) rfl q before after _ _ rfl rfl hr hin
  have hh:=Link.data_update bodyStack body_injective bank before.store bank hin .history
    ((true::frame (bank (aux .reference)) []).reverse++bank (aux .refsHistory))
  have he:Function.update before.store .history
      ((true::frame (bank (aux .reference)) []).reverse++bank (aux .refsHistory))=after.store:=by
    funext k;cases k <;> rfl
  simpa only [he,bodyStack] using hh
end RiemannGaussian.SemiprimeD1StackRootPhaseParametersCalls
