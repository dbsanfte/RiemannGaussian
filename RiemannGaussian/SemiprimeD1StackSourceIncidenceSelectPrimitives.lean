/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelect
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectEncoding
import RiemannGaussian.SemiprimeD1StackSourceIncidenceExecution
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Real selector calls, parses, comparisons and complete physical cleanup
All clocks below arise from actual included source traces. The dictionary,
current key, candidate and result are physical words; none is a source supplier.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectPrimitives
open SemiprimeD1StackSourceIncidenceSelect SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
local notation "ctl" => Label.local
/-- Exact chronological source-fragment composition preserves every real outer return. -/
theorem join {m n:Nat} {pc mid next:Label} {before between after:Stack→List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between next after) :
    Runs program (m+n) pc before next after :=runs_trans program m n pc mid next before between after h g
/-- Actual complete preserving copy, including both restoration loops and its real caller return. -/
theorem copy_call (what:Copy) (pc next:Control)
    (hc:program (ctl pc)=.call (.copier what 0) (ctl next)) (before:Stack→List Bool) (xs ys:List Bool)
    (hx:before (copyStack what 0)=xs) (hy:before (copyStack what 1)=ys) (hs:before (copyStack what 2)=[]) :
    Runs program (5*xs.length+4) (ctl pc) before (ctl next)
      (Function.update before (copyStack what 1) (xs++ys)) :=by
  let start:=SemiprimeD1StackCopy.state 0 none xs ys []
  let stop:=SemiprimeD1StackCopy.done xs (xs++ys)
  have hi:Link.DataRel (copyStack what) before start.store before:=by
    constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update (copyStack what) (copy_injective what) before start.store before hi (1:Fin 3) (xs++ys)
  have he:Function.update start.store 1 (xs++ys)=stop.store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program (copyStack what) (Label.copier what) (copy_injective what) SemiprimeD1StackCopy.code 0
    (fun _=>rfl) (ctl pc) (ctl next) hc (5*xs.length+3) start stop before _ rfl rfl
    (SemiprimeD1StackCopy.copy_words xs ys none) hi ho
/-- Complete real field read pays all input/output bits and leaves its physical true-valid flag. -/
theorem field_call (part:Part) (pc next:Control)
    (hc:program (ctl pc)=.call (.parser part (Field.active .tagPop (none,false))) (ctl next))
    (before:Stack→List Bool) (word tail:List Bool)
    (hi:before (fieldStack part (.inl .input))=frame word tail)
    (ho:before (fieldStack part (.inl .output))=[])
    (hs:before (fieldStack part (.inl .scratch))=[])
    (hv:before (fieldStack part (.inr ()))=[]) :
    Runs program (8*word.length+7) (ctl pc) before (ctl next)
      (Function.update (Function.update (Function.update before (fieldStack part (.inl .input)) tail)
        (fieldStack part (.inl .output)) word) (fieldStack part (.inr ())) [true]) :=by
  let start:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let stop:SemiprimeD1StackBytecode.State Field.Stack Field.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:Link.DataRel (fieldStack part) before start.store before:=by
    constructor
    · intro k;rcases k with k|k
      · cases k
        · exact hi
        · exact hs
        · exact ho
      · cases k;exact hv
    · intro k _;rfl
  have h0:=Link.data_update (fieldStack part) (field_injective part) before start.store before hin (.inl .input) tail
  have h1:=Link.data_update (fieldStack part) (field_injective part) before _ _ h0 (.inl .output) word
  have h2:=Link.data_update (fieldStack part) (field_injective part) before _ _ h1 (.inr ()) [true]
  have he:Function.update (Function.update (Function.update start.store (.inl .input) tail) (.inl .output) word) (.inr ()) [true]=stop.store:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  rw [he] at h2
  exact included_call program (fieldStack part) (Label.parser part) (field_injective part) Field.code
    (Field.active .tagPop (none,false)) (fun _=>rfl) (ctl pc) (ctl next) hc (8*word.length+6) start stop before _ rfl rfl
    (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin h2
/-- Real preserving Frame writes a physical field onto its existing dictionary/vector tail. -/
theorem frame_call (pc next:Control)
    (hc:program (ctl pc)=.call (.framer 0) (ctl next)) (before:Stack→List Bool) (word buffer:List Bool)
    (hw:before (frameStack 0)=word) (hb:before (frameStack 1)=buffer) (hs:before (frameStack 2)=[]) :
    Runs program (6*word.length+5) (ctl pc) before (ctl next)
      (Function.update before (frameStack 1) (frame word buffer)) :=by
  let start:=SemiprimeD1StackFrame.state 0 none word buffer []
  let stop:=SemiprimeD1StackFrame.done word (frame word buffer)
  have hi:Link.DataRel (frameStack) before start.store before:=by
    constructor
    · intro k;fin_cases k
      · exact hw
      · exact hb
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update (frameStack) (frame_injective) before start.store before hi (1:Fin 3) (frame word buffer)
  have he:Function.update start.store 1 (frame word buffer)=stop.store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program (frameStack) Label.framer (frame_injective) SemiprimeD1StackFrame.code 0 (fun _=>rfl)
    (ctl pc) (ctl next) hc (6*word.length+4) start stop before _ rfl rfl
    (SemiprimeD1StackFrame.frame_words word buffer none) hi ho
/-- One literal local push preserves the entire other physical bank and all real outer returns. -/
theorem push_run (pc:Control) (next:Label) (k:Stack) (b:Bool) (before:Stack→List Bool)
    (hc:program (ctl pc)=.base (.push k b next)) :
    Runs program 1 (ctl pc) before next (Function.update before k (b::before k)) :=
  one_base program _ _ _ _ _ hc rfl rfl
/-- One literal local pop consumes ONLYthe actual physical Boolean head. -/
theorem pop_run (pc:Control) (empty low high:Label) (k:Stack) (before:Stack→List Bool) (xs:List Bool)
    (hc:program (ctl pc)=.base (.pop k empty low high)) (hx:before k=xs) :
    Runs program 1 (ctl pc) before (SemiprimeD1StackBytecode.choose empty low high xs.head?) (Function.update before k xs.tail) :=by
  apply one_base program (ctl pc) _ (.pop k empty low high) before _ hc
  · simp only [SemiprimeD1StackBytecode.execute,hx]
  · simp only [SemiprimeD1StackBytecode.execute,hx]
/-- Real EOF peek does not silently discard any remaining singleton-result bytes. -/
theorem peek_run (pc:Control) (empty low high:Label) (k:Stack) (before:Stack→List Bool) (xs:List Bool)
    (hc:program (ctl pc)=.base (.peek k empty low high)) (hx:before k=xs) :
    Runs program 1 (ctl pc) before (SemiprimeD1StackBytecode.choose empty low high xs.head?) before :=by
  apply one_base program (ctl pc) _ (.peek k empty low high) before before hc
  · simp only [SemiprimeD1StackBytecode.execute,hx]
  · rfl
/-- Every table/key/owner/row cleanup actually visits every byte and its final empty branch. -/
theorem drain_loop (pc:Control) (next:Label) (k:Stack)
    (hc:program (ctl pc)=.base (.pop k next (ctl pc) (ctl pc))) (before:Stack→List Bool) (xs:List Bool) (hx:before k=xs) :
    Runs program (xs.length+1) (ctl pc) before next (Function.update before k []) :=by
  induction xs generalizing before with
  | nil=>exact pop_run pc next (ctl pc) (ctl pc) k before [] hc hx
  | cons b xs ih=>
    have h0:=pop_run pc next (ctl pc) (ctl pc) k before (b::xs) hc hx
    have h1:=ih (Function.update before k xs) (Function.update_self _ _ _)
    have hh:=join (by cases b <;> exact h0) h1
    simpa only [List.length_cons,Function.update_idem,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
/-- Actual five-word comparison consumes only copied operands and returns its computed strict borrow. -/
theorem less_call (before:Stack→List Bool) (a b:List Bool)
    (ha:before (aux .compareLeft)=a) (hb:before (aux .compareRight)=b)
    (hs:before (aux .compareScratch)=[]) (hd:before (aux .discard)=[]) (ho:before (aux .compareOutput)=[]) :
    Runs program (SemiprimeD1StackWordLessExecution.totalTime a b+1) (ctl .compare) before (ctl .compared)
      (Function.update (Function.update (Function.update before (aux .compareLeft) [])
        (aux .compareRight) []) (aux .compareOutput) [SemiprimeD1StackWordLessExecution.answer a b]) :=by
  let start:=SemiprimeD1StackWordLess.initial a b
  let stop:=SemiprimeD1StackWordLessExecution.done a b
  have hin:Link.DataRel lessStack before start.data before:=by
    constructor
    · intro k;rcases k with k|k
      · cases k
        · exact ha
        · exact hb
        · exact hs
        · exact hd
      · cases k;exact ho
    · intro k _;rfl
  have h0:=Link.data_update lessStack less_injective before start.data before hin (.inl .left) []
  have h1:=Link.data_update lessStack less_injective before _ _ h0 (.inl .right) []
  have h2:=Link.data_update lessStack less_injective before _ _ h1 (.inr ()) [SemiprimeD1StackWordLessExecution.answer a b]
  have he:Function.update (Function.update (Function.update start.data (.inl .left) []) (.inl .right) [])
      (.inr ()) [SemiprimeD1StackWordLessExecution.answer a b]=stop.data:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  rw [he] at h2
  exact SemiprimeD1StackProcedureCallsTrace.included_call program lessStack Label.less less_injective
    Less.program .start (fun _=>rfl) (ctl .compare) (ctl .compared) rfl
    (SemiprimeD1StackWordLessExecution.totalTime a b) start stop before _ rfl rfl rfl rfl
    (SemiprimeD1StackWordLessExecution.source_run a b) hin h2
/-- The shared environment instructions are included twice structurally, with every real return retained. -/
theorem environment_code (pc:E.Label) :
    program (environmentLabel pc)=SemiprimeD1StackValidationLink.instruction environmentStack environmentLabel
      (SemiprimeD1StackSourceEnvironment.program pc) :=by
  change SemiprimeD1StackValidationLink.instruction queryStack Label.queryCode
    (SemiprimeD1StackValidationLink.instruction Q.environmentStack (fun l=>(show Q.Label from .environment l))
      (SemiprimeD1StackSourceEnvironment.program pc))=_
  generalize SemiprimeD1StackSourceEnvironment.program pc=op
  cases op with
  | base op=>cases op <;> rfl
  | call entry next=>rfl
  | ret=>rfl
/-- Every environment role is a direct distinct field of the actual scorer bank. -/
theorem environment_injective :Function.Injective environmentStack :=by
  intro i j h
  exact Sum.inl_injective (Sum.inl_injective h)
/-- Generic caller preservation for the actual shared environment entry; only proved literal traces instantiate it. -/
theorem environment_call (pc next:Control) (entry:E.Label)
    (hc:program (ctl pc)=.call (environmentLabel entry) (ctl next))
    (time:Nat) (start stop:SemiprimeD1StackCalls.State E.Stack E.Label) (before after:Stack→List Bool)
    (he:start.pc=some entry) (hf:start.frames=[]) (hn:stop.pc=none) (ht:stop.frames=[])
    (hr:SemiprimeD1StackCalls.run SemiprimeD1StackSourceEnvironment.program time start=some stop)
    (hin:Link.DataRel environmentStack before start.data before)
    (hout:Link.DataRel environmentStack before stop.data after) :
    Runs program (time+1) (ctl pc) before (ctl next) after :=
  SemiprimeD1StackProcedureCallsTrace.included_call program environmentStack environmentLabel environment_injective
    SemiprimeD1StackSourceEnvironment.program entry environment_code (ctl pc) (ctl next) hc time
    start stop before after he hf hn ht hr hin hout
/-- The real parser's true-valid byte is physically consumed before returning the complete unframed word. -/
theorem field_valid (part:Part) (pc validPC:Control) (next:Label)
    (hc:program (ctl pc)=.call (.parser part (Field.active .tagPop (none,false))) (ctl validPC))
    (hp:program (ctl validPC)=.base (.pop (aux .valid) (ctl .abort) (ctl .abort) next))
    (before:Stack→List Bool) (word tail:List Bool)
    (hi:before (fieldStack part (.inl .input))=frame word tail)
    (ho:before (fieldStack part (.inl .output))=[])
    (hs:before (fieldStack part (.inl .scratch))=[])
    (hv:before (aux .valid)=[]) :
    Runs program (8*word.length+8) (ctl pc) before next
      (Function.update (Function.update before (fieldStack part (.inl .input)) tail)
        (fieldStack part (.inl .output)) word) :=by
  let after:=Function.update (Function.update before (fieldStack part (.inl .input)) tail)
    (fieldStack part (.inl .output)) word
  have hout:aux .valid ≠ fieldStack part (.inl .output):=
    by
      intro h
      have he:=field_injective part (show fieldStack part (.inr ())=fieldStack part (.inl .output) from h)
      cases he
  have hin:aux .valid ≠ fieldStack part (.inl .input):=
    by
      intro h
      have he:=field_injective part (show fieldStack part (.inr ())=fieldStack part (.inl .input) from h)
      cases he
  have hvalid:after (aux .valid)=[]:=by
    dsimp only [after]
    rw [Function.update_of_ne hout,Function.update_of_ne hin,hv]
  have h0:=field_call part pc validPC hc before word tail hi ho hs hv
  change Runs program (8*word.length+7) _ _ _ (Function.update after (aux .valid) [true]) at h0
  have h1:=pop_run validPC (ctl .abort) (ctl .abort) next (aux .valid)
    (Function.update after (aux .valid) [true]) [true] hp (Function.update_self _ _ _)
  change Runs program 1 _ _ _ (Function.update (Function.update after (aux .valid) [true]) (aux .valid) []) at h1
  have hz:Function.update after (aux .valid) []=after:=by
    simpa only [hvalid] using (Function.update_eq_self (aux .valid) after)
  rw [Function.update_idem,hz] at h1
  have h:=join h0 h1
  simpa only [Nat.add_assoc,SemiprimeD1StackBytecode.choose,List.head?_cons,after] using h
/-- Unused colour bytes are parsed, validated and entirely drained; only the actual reader tail changes. -/
theorem field_discard (part:Part) (pc validPC drainPC:Control) (next:Label)
    (hc:program (ctl pc)=.call (.parser part (Field.active .tagPop (none,false))) (ctl validPC))
    (hp:program (ctl validPC)=.base (.pop (aux .valid) (ctl .abort) (ctl .abort) (ctl drainPC)))
    (hd:program (ctl drainPC)=.base (.pop (fieldStack part (.inl .output)) next (ctl drainPC) (ctl drainPC)))
    (before:Stack→List Bool) (word tail:List Bool)
    (hi:before (fieldStack part (.inl .input))=frame word tail)
    (ho:before (fieldStack part (.inl .output))=[])
    (hs:before (fieldStack part (.inl .scratch))=[]) (hv:before (aux .valid)=[]) :
    Runs program (9*word.length+9) (ctl pc) before next
      (Function.update before (fieldStack part (.inl .input)) tail) :=by
  let after:=Function.update before (fieldStack part (.inl .input)) tail
  have hne:fieldStack part (.inl .output) ≠ fieldStack part (.inl .input):=
    by
      intro h
      have he:=field_injective part h
      cases he
  have hzero:after (fieldStack part (.inl .output))=[]:=by
    dsimp only [after]
    rw [Function.update_of_ne hne,ho]
  have h0:=field_valid part pc validPC (ctl drainPC) hc hp before word tail hi ho hs hv
  have h1:=drain_loop drainPC next (fieldStack part (.inl .output)) hd
    (Function.update after (fieldStack part (.inl .output)) word) word (Function.update_self _ _ _)
  have hz:Function.update after (fieldStack part (.inl .output)) []=after:=by
    simpa only [hzero] using (Function.update_eq_self (fieldStack part (.inl .output)) after)
  rw [Function.update_idem,hz] at h1
  have h:=join h0 h1
  have ht:(8*word.length+8)+(word.length+1)=9*word.length+9:=by omega
  simpa only [ht] using h
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectPrimitives
