/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceOccurrences
/-! # Actual row-source copies, parsers, binary-key frames, counter and literal drains -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceOccurrencesPrimitives
open SemiprimeD1StackSourceOccurrences SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
local notation "ctl" => Label.local
/-- Actual fragments concatenate in this same literal record source. -/
theorem join {m n:Nat} {pc mid next:Label} {before between after:Stack→List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between next after) :
    Runs program (m+n) pc before next after :=runs_trans program m n pc mid next before between after h g
/-- The actual copy operands name separate physical words. -/
theorem copy_ne (what:Copy) :copyStack what 0≠copyStack what 1 :=by cases what <;> decide
/-- Copy restoration scratch never aliases the actual destination. -/
theorem copy_scratch_ne (what:Copy) :Stack.copyScratch≠copyStack what 1 :=by cases what <;> decide
/-- One real preserving copy charges all source bytes and its actual return. -/
theorem copy_call (what:Copy) (pc next:Control)
    (hc:program (ctl pc)=.call (.copy what 0) (ctl next))
    (before:Stack→List Bool) (xs ys:List Bool)
    (hx:before (copyStack what 0)=xs) (hy:before (copyStack what 1)=ys) (hz:before .copyScratch=[]) :
    Runs program (5*xs.length+4) (ctl pc) before (ctl next)
      (Function.update before (copyStack what 1) (xs++ys)) :=by
  apply included_call program (copyStack what) (Label.copy what) (copy_injective what)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) (ctl pc) (ctl next) hc (5*xs.length+3)
    (SemiprimeD1StackCopy.state 0 none xs ys []) (SemiprimeD1StackCopy.done xs (xs++ys)) before _
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words xs ys none
  · constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
      · exact hz
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k
      · change Function.update before (copyStack what 1) (xs++ys) (copyStack what 0)=xs
        rw [Function.update_of_ne (copy_ne what),hx]
      · exact Function.update_self _ _ _
      · change Function.update before (copyStack what 1) (xs++ys) .copyScratch=[]
        rw [Function.update_of_ne (copy_scratch_ne what),hz]
    · intro k hk
      exact Function.update_of_ne (fun he=>hk 1 he.symm) _ _
/-- Actual field reader address for the current record or port field. -/
def fieldInput (part:Part) :Stack :=fieldStack part (.inl .input)
/-- Actual field destination; all three field caches are private. -/
def fieldOutput (part:Part) :Stack :=fieldStack part (.inl .output)
/-- One actual parser consumes and copies the field, retaining its true validity marker. -/
theorem field_call (part:Part) (pc next:Control)
    (hc:program (ctl pc)=.call (.field part (Field.active .tagPop (none,false))) (ctl next))
    (before:Stack→List Bool) (word tail:List Bool)
    (hi:before (fieldInput part)=frame word tail) (ho:before (fieldOutput part)=[])
    (hs:before .fieldScratch=[]) (hv:before .valid=[]) :
    Runs program (8*word.length+7) (ctl pc) before (ctl next)
      (Function.update (Function.update (Function.update before (fieldInput part) tail)
        (fieldOutput part) word) .valid [true]) :=by
  let start:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let stop:SemiprimeD1StackBytecode.State Field.Stack Field.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:Link.DataRel (fieldStack part) before start.store before :=by
    constructor
    · intro k;rcases k with k|k
      · cases k
        · exact hi
        · exact hs
        · exact ho
      · cases k;exact hv
    · intro k _;rfl
  apply included_call program (fieldStack part) (Label.field part) (field_injective part) Field.code
    (Field.active .tagPop (none,false)) (fun _=>rfl) (ctl pc) (ctl next) hc (8*word.length+6)
    start stop before _ rfl rfl (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin
  have h0:=Link.data_update (fieldStack part) (field_injective part) before start.store before hin (.inl .input) tail
  have h1:=Link.data_update (fieldStack part) (field_injective part) before _ _ h0 (.inl .output) word
  have h2:=Link.data_update (fieldStack part) (field_injective part) before _ _ h1 (.inr ()) [true]
  have he:Function.update (Function.update (Function.update start.store (.inl .input) tail)
      (.inl .output) word) (.inr ()) [true]=stop.store :=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  simpa only [he,fieldInput,fieldOutput,fieldStack] using h2
/-- Actual frame source never aliases the shared pair buffer. -/
theorem frame_ne (what:Frame) :frameStack what 0≠Stack.frameBuffer :=by cases what <;> decide
/-- One preserving frame physically copies either the binary owner or the actual unary port key. -/
theorem frame_call (what:Frame) (pc next:Control)
    (hc:program (ctl pc)=.call (.frame what 0) (ctl next))
    (before:Stack→List Bool) (xs ys:List Bool)
    (hx:before (frameStack what 0)=xs) (hy:before .frameBuffer=ys) (hz:before .frameScratch=[]) :
    Runs program (6*xs.length+5) (ctl pc) before (ctl next)
      (Function.update before .frameBuffer (frame xs ys)) :=by
  apply included_call program (frameStack what) (Label.frame what) (frame_injective what)
    SemiprimeD1StackFrame.code 0 (fun _=>rfl) (ctl pc) (ctl next) hc (6*xs.length+4)
    (SemiprimeD1StackFrame.state 0 none xs ys []) (SemiprimeD1StackFrame.done xs (frame xs ys)) before _
  · rfl
  · rfl
  · exact SemiprimeD1StackFrame.frame_words xs ys none
  · constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
      · exact hz
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k
      · change Function.update before .frameBuffer (frame xs ys) (frameStack what 0)=xs
        rw [Function.update_of_ne (frame_ne what),hx]
      · exact Function.update_self _ _ _
      · change Function.update before .frameBuffer (frame xs ys) .frameScratch=[]
        rw [Function.update_of_ne (by decide:Stack.frameScratch≠.frameBuffer),hz]
    · intro k hk
      exact Function.update_of_ne (fun he=>hk 1 he.symm) _ _
/-- Both actual reversal operands are distinct for every literal call site. -/
theorem reverse_ne (what:Reverse) :reverseStack what 0≠reverseStack what 1 :=by cases what <;> decide
/-- Real consuming reversal includes every pop/push, branch, halt and caller return. -/
theorem reverse_call (what:Reverse) (pc next:Control)
    (hc:program (ctl pc)=.call (.reverse what 0) (ctl next))
    (before:Stack→List Bool) (xs ys:List Bool)
    (hx:before (reverseStack what 0)=xs) (hy:before (reverseStack what 1)=ys) :
    Runs program (2*xs.length+3) (ctl pc) before (ctl next)
      (Function.update (Function.update before (reverseStack what 0) [])
        (reverseStack what 1) (xs.reverse++ys)) :=by
  apply included_call program (reverseStack what) (Label.reverse what) (reverse_injective what)
    SemiprimeD1StackReverseWord.code 0 (fun _=>rfl) (ctl pc) (ctl next) hc (2*xs.length+2)
    (SemiprimeD1StackReverseWord.state none xs ys) (SemiprimeD1StackReverseWord.done (xs.reverse++ys)) before _
  · rfl
  · rfl
  · exact SemiprimeD1StackReverseWord.reverse_run xs ys none
  · constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k
      · change Function.update (Function.update before (reverseStack what 0) [])
          (reverseStack what 1) (xs.reverse++ys) (reverseStack what 0)=[]
        rw [Function.update_of_ne (reverse_ne what),Function.update_self]
      · exact Function.update_self _ _ _
    · intro k hk
      rw [Function.update_of_ne (fun he=>hk 1 he.symm),Function.update_of_ne (fun he=>hk 0 he.symm)]
/-- Actual fixed-width binary increment; both counter transfer reversals remain caller work. -/
theorem increment_call (part:Counter) (before:Stack→List Bool) (xs:List Bool)
    (hx:before .counter=xs) (hs:before .incrementScratch=[]) (ho:before .next=[]) :
    ∃q ≤5*(2*xs.length+3)+1,Runs program q (ctl (.increment part)) before (ctl (.carry part))
      (Function.update (Function.update before .counter []) .next
        (SemiprimeD1StackIncrement.overflow xs::SemiprimeD1StackIncrement.wrapped xs)) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackIncrementBytecode.increment_run xs []
  simp only [List.append_nil] at hr
  refine ⟨q+1,by omega,?_⟩
  let start:SemiprimeD1StackBytecode.State SemiprimeD1TensorTapeFieldMachine.Stack Inc.Label:=
    ⟨some Inc.entry,none,SemiprimeD1TensorTapeFieldMachine.contents xs [] []⟩
  let stop:SemiprimeD1StackBytecode.State SemiprimeD1TensorTapeFieldMachine.Stack Inc.Label:=
    ⟨none,none,SemiprimeD1TensorTapeFieldMachine.contents [] []
      (SemiprimeD1StackIncrement.overflow xs::SemiprimeD1StackIncrement.wrapped xs)⟩
  have hin:Link.DataRel incrementStack before start.store before :=by
    constructor
    · intro k;cases k
      · exact hx
      · exact hs
      · exact ho
    · intro k _;rfl
  apply included_call program incrementStack Label.increment increment_injective Inc.code Inc.entry (fun _=>rfl)
    (ctl (.increment part)) (ctl (.carry part)) rfl q start stop before _ rfl rfl hr hin
  have h0:=Link.data_update incrementStack increment_injective before start.store before hin .input []
  have h1:=Link.data_update incrementStack increment_injective before _ _ h0 .output
    (SemiprimeD1StackIncrement.overflow xs::SemiprimeD1StackIncrement.wrapped xs)
  have he:Function.update (Function.update start.store .input []) .output
      (SemiprimeD1StackIncrement.overflow xs::SemiprimeD1StackIncrement.wrapped xs)=stop.store :=by
    funext k;cases k <;> rfl
  simpa only [he,incrementStack] using h1
/-- One real local push, with the entire remaining physical bank retained. -/
theorem push_run (pc:Control) (next:Label) (k:Stack) (b:Bool) (before:Stack→List Bool)
    (hc:program (ctl pc)=.base (.push k b next)) :
    Runs program 1 (ctl pc) before next (Function.update before k (b::before k)) :=
  one_base program _ _ _ _ _ hc rfl rfl
/-- One real local pop exposes the actual Boolean head and consumes precisely one physical cell. -/
theorem pop_run (pc:Control) (empty low high:Label) (k:Stack) (before:Stack→List Bool) (xs:List Bool)
    (hc:program (ctl pc)=.base (.pop k empty low high)) (hx:before k=xs) :
    Runs program 1 (ctl pc) before (SemiprimeD1StackBytecode.choose empty low high xs.head?)
      (Function.update before k xs.tail) :=by
  apply one_base program (ctl pc) _ (.pop k empty low high) before _ hc
  · simp only [SemiprimeD1StackBytecode.execute,hx]
  · simp only [SemiprimeD1StackBytecode.execute,hx]
/-- Literal cleanup visits every current key/table byte and its empty branch. -/
theorem drain_loop (pc:Control) (next:Label) (k:Stack)
    (hc:program (ctl pc)=.base (.pop k next (ctl pc) (ctl pc)))
    (before:Stack→List Bool) (xs:List Bool) (hx:before k=xs) :
    Runs program (xs.length+1) (ctl pc) before next (Function.update before k []) :=by
  induction xs generalizing before with
  | nil=>exact pop_run pc next (ctl pc) (ctl pc) k before [] hc hx
  | cons b xs ih=>
    have h0:=pop_run pc next (ctl pc) (ctl pc) k before (b::xs) hc hx
    have h1:=ih (Function.update before k xs) (Function.update_self _ _ _)
    have hh:=join (by cases b <;> exact h0) h1
    simpa only [List.length_cons,Function.update_idem,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
/-- Literal fixed return target of each normalization call. -/
def afterTrim :Trim→Label | .factor=>ctl .ownerTag | .owner=>ctl .frameFactor
/-- The REAL frozen reducer.trim entry consumes actual reverse bits and emits canonical magnitude bytes. -/
theorem trim_call (kind:Trim) (bank:Stack→List Bool)
    (hl:bank (trimStack kind .left)=[]) (hr:bank (trimStack kind .right)=[]) :
    Runs program (SemiprimeD1StackReduceExecution.trimTime (bank Stack.normScratch)+1) (ctl (.normalize kind)) bank
      (afterTrim kind)
      (Function.update (Function.update bank Stack.normScratch []) (trimStack kind .output)
        (SemiprimeD1StackReduceExecution.trimReverse (bank Stack.normScratch)++bank (trimStack kind .output))) :=by
  let before:=SemiprimeD1StackReduce.state (some .trim) none [] []
    (bank Stack.normScratch) (bank (trimStack kind .output))
  let after:=SemiprimeD1StackReduce.state none none [] [] []
    (SemiprimeD1StackReduceExecution.trimReverse (bank Stack.normScratch)++bank (trimStack kind .output))
  have hin:Link.DataRel (trimStack kind) bank before.store bank:=by
    constructor
    · intro k;cases k
      · exact hl
      · exact hr
      · rfl
      · rfl
    · intro k _;rfl
  apply included_call program (trimStack kind) (Label.trim kind) (trim_injective kind) Reduce.code .trim
    (fun _=>rfl) (ctl (.normalize kind)) _ rfl (SemiprimeD1StackReduceExecution.trimTime (bank Stack.normScratch))
    before after _ _ rfl rfl (SemiprimeD1StackReduceExecution.trim_run _ _ none) hin
  have h0:=Link.data_update (trimStack kind) (trim_injective kind) bank before.store bank hin .scratch []
  have h1:=Link.data_update (trimStack kind) (trim_injective kind) bank _ _ h0 .output
    (SemiprimeD1StackReduceExecution.trimReverse (bank Stack.normScratch)++bank (trimStack kind .output))
  have he:Function.update (Function.update before.store .scratch []) .output
      (SemiprimeD1StackReduceExecution.trimReverse (bank Stack.normScratch)++bank (trimStack kind .output))=after.store:=by
    funext k;cases k <;> rfl
  simpa only [he,show trimStack kind .scratch=Stack.normScratch from rfl] using h1
end RiemannGaussian.SemiprimeD1StackSourceOccurrencesPrimitives
