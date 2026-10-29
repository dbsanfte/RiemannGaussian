/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequency
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Literal paid frequency-source primitive calls and actual counter return -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyPrimitives
open SemiprimeD1StackSourceKeyFrequency SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Exact chronological source-fragment composition preserves every real outer return. -/
theorem join {m n:Nat} {pc mid next:Label} {before between after:Stack→List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between next after) :
    Runs program (m+n) pc before next after :=runs_trans program m n pc mid next before between after h g
/-- Actual complete preserving copy, including both restoration loops and its real caller return. -/
theorem copy_call (what:Copy) (pc next:Label)
    (hc:program pc=.call (.copier what 0) next) (before:Stack→List Bool) (xs ys:List Bool)
    (hx:before (copyStack what 0)=xs) (hy:before (copyStack what 1)=ys) (hs:before (copyStack what 2)=[]) :
    Runs program (5*xs.length+4) pc before next
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
    (fun _=>rfl) pc next hc (5*xs.length+3) start stop before _ rfl rfl
    (SemiprimeD1StackCopy.copy_words xs ys none) hi ho
/-- Complete real field read, with actual true-valid marker retained until its physical pop. -/
theorem field_call (pc next:Label)
    (hc:program pc=.call (.parser (Field.active .tagPop (none,false))) next)
    (before:Stack→List Bool) (word tail:List Bool) (hi:before (aux .reader)=frame word tail)
    (ho:before (aux .raw)=[]) (hs:before (lookupStack (.inr .fieldScratch))=[]) (hv:before (lookupStack (.inr .valid))=[]) :
    Runs program (8*word.length+7) pc before next
      (Function.update (Function.update (Function.update before (aux .reader) tail)
        (aux .raw) word) (lookupStack (.inr .valid)) [true]) :=by
  let start:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let stop:SemiprimeD1StackBytecode.State Field.Stack Field.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:Link.DataRel fieldStack before start.store before:=by
    constructor
    · intro k;rcases k with k|k
      · cases k
        · exact hi
        · exact hs
        · exact ho
      · cases k;exact hv
    · intro k _;rfl
  have h0:=Link.data_update fieldStack field_injective before start.store before hin (.inl .input) tail
  have h1:=Link.data_update fieldStack field_injective before _ _ h0 (.inl .output) word
  have h2:=Link.data_update fieldStack field_injective before _ _ h1 (.inr ()) [true]
  have he:Function.update (Function.update (Function.update start.store (.inl .input) tail) (.inl .output) word) (.inr ()) [true]=stop.store:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  rw [he] at h2
  exact included_call program fieldStack Label.parser field_injective Field.code
    (Field.active .tagPop (none,false)) (fun _=>rfl) pc next hc (8*word.length+6) start stop before _ rfl rfl
    (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin h2
/-- Real preserving Frame writes a physical field onto its existing dictionary/vector tail. -/
theorem frame_call (part:Frame) (pc next:Label)
    (hc:program pc=.call (.framer part 0) next) (before:Stack→List Bool) (word buffer:List Bool)
    (hw:before (frameStack part 0)=word) (hb:before (frameStack part 1)=buffer) (hs:before (frameStack part 2)=[]) :
    Runs program (6*word.length+5) pc before next
      (Function.update before (frameStack part 1) (frame word buffer)) :=by
  let start:=SemiprimeD1StackFrame.state 0 none word buffer []
  let stop:=SemiprimeD1StackFrame.done word (frame word buffer)
  have hi:Link.DataRel (frameStack part) before start.store before:=by
    constructor
    · intro k;fin_cases k
      · exact hw
      · exact hb
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update (frameStack part) (frame_injective part) before start.store before hi (1:Fin 3) (frame word buffer)
  have he:Function.update start.store 1 (frame word buffer)=stop.store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program (frameStack part) (Label.framer part) (frame_injective part) SemiprimeD1StackFrame.code 0 (fun _=>rfl)
    pc next hc (6*word.length+4) start stop before _ rfl rfl
    (SemiprimeD1StackFrame.frame_words word buffer none) hi ho
/-- Every inner-owner/row/final reversal consumes its real source and pays all bytes and return cells. -/
theorem reverse_call (pc next:Label)
    (hc:program pc=.call (.reversal 0) next) (before:Stack→List Bool) (xs ys:List Bool)
    (hx:before (reverseStack 0)=xs) (hy:before (reverseStack 1)=ys) :
    Runs program (2*xs.length+3) pc before next
      (Function.update (Function.update before (reverseStack 0) []) (reverseStack 1) (xs.reverse++ys)) :=by
  let start:=SemiprimeD1StackReverseWord.state none xs ys
  let stop:=SemiprimeD1StackReverseWord.done (xs.reverse++ys)
  have hi:Link.DataRel reverseStack before start.store before:=by
    constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
    · intro k _;rfl
  have h0:=Link.data_update reverseStack reverse_injective before start.store before hi (0:Fin 2) []
  have h1:=Link.data_update reverseStack reverse_injective before _ _ h0 (1:Fin 2) (xs.reverse++ys)
  have he:Function.update (Function.update start.store 0 []) 1 (xs.reverse++ys)=stop.store:=by funext k;fin_cases k <;> rfl
  rw [he] at h1
  exact included_call program reverseStack Label.reversal reverse_injective
    SemiprimeD1StackReverseWord.code 0 (fun _=>rfl) pc next hc (2*xs.length+2) start stop before _ rfl rfl
    (SemiprimeD1StackReverseWord.reverse_run xs ys none) hi h1
/-- Actual high-zero stripping/reversal, with both other reducer operands physically empty. -/
theorem trim_call (pc next:Label)
    (hc:program pc=.call (.reducer .trim) next) (before:Stack→List Bool) (xs ys:List Bool)
    (hl:before (trimStack .left)=[]) (hr:before (trimStack .right)=[])
    (hs:before (trimStack .scratch)=xs) (ho:before (trimStack .output)=ys) :
    Runs program (SemiprimeD1StackReduceExecution.trimTime xs+1) pc before next
      (Function.update (Function.update before (trimStack .scratch) []) (trimStack .output)
        (SemiprimeD1StackReduceExecution.trimReverse xs++ys)) :=by
  let start:=SemiprimeD1StackReduce.state (some .trim) none [] [] xs ys
  let stop:=SemiprimeD1StackReduce.state none none [] [] [] (SemiprimeD1StackReduceExecution.trimReverse xs++ys)
  have hi:Link.DataRel trimStack before start.store before:=by
    constructor
    · intro k;cases k
      · exact hl
      · exact hr
      · exact hs
      · exact ho
    · intro k _;rfl
  have h0:=Link.data_update trimStack trim_injective before start.store before hi .scratch []
  have h1:=Link.data_update trimStack trim_injective before _ _ h0 .output
    (SemiprimeD1StackReduceExecution.trimReverse xs++ys)
  have he:Function.update (Function.update start.store .scratch []) .output
      (SemiprimeD1StackReduceExecution.trimReverse xs++ys)=stop.store:=by funext k;cases k <;> rfl
  rw [he] at h1
  exact included_call program trimStack Label.reducer trim_injective R.code .trim (fun _=>rfl)
    pc next hc (SemiprimeD1StackReduceExecution.trimTime xs) start stop before _ rfl rfl
    (SemiprimeD1StackReduceExecution.trim_run xs ys none) hi h1
/-- Actual key increment consumes the old word and emits its REALoverflow prefix and wrapped bits. -/
theorem increment_call (before:Stack→List Bool) (word:List Bool)
    (hw:before oldCount=word) (hs:before (aux .incScratch)=[]) (ho:before (aux .incNext)=[]) :
    ∃q≤10*word.length+16,Runs program q .increment before .popOverflow
      (Function.update (Function.update before oldCount []) (aux .incNext)
        (SemiprimeD1StackIncrement.overflow word::SemiprimeD1StackIncrement.wrapped word)) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackIncrementBytecode.increment_run word []
  refine ⟨q+1,by omega,?_⟩
  let start:SemiprimeD1StackBytecode.State I.Stack I.Label:=⟨some I.entry,none,SemiprimeD1TensorTapeFieldMachine.contents word [] []⟩
  let stop:SemiprimeD1StackBytecode.State I.Stack I.Label:=⟨none,none,SemiprimeD1TensorTapeFieldMachine.contents [] []
    (SemiprimeD1StackIncrement.overflow word::SemiprimeD1StackIncrement.wrapped word)⟩
  have hi:Link.DataRel incrementStack before start.store before:=by
    constructor
    · intro k;cases k
      · exact hw
      · exact hs
      · exact ho
    · intro k _;rfl
  have h0:=Link.data_update incrementStack increment_injective before start.store before hi .input []
  have h1:=Link.data_update incrementStack increment_injective before _ _ h0 .output
    (SemiprimeD1StackIncrement.overflow word::SemiprimeD1StackIncrement.wrapped word)
  have he:Function.update (Function.update start.store .input []) .output
      (SemiprimeD1StackIncrement.overflow word::SemiprimeD1StackIncrement.wrapped word)=stop.store:=by funext k;cases k <;> rfl
  rw [he] at h1
  apply included_call program incrementStack Label.incrementCode increment_injective I.code I.entry (fun _=>rfl)
    .increment .popOverflow rfl q start stop before _ rfl rfl
  · simpa only [List.append_nil] using hr
  · exact hi
  · exact h1
/-- The actual eleven-role first-match scan runs only after the preserving physical catalogue copy. -/
theorem lookup_call (before:Stack→List Bool) (key:List Bool) (rows:List (List Bool×List Bool))
    (hi:∀k,before (lookupStack k)=(SemiprimeD1StackOwnerLookup.initial key (SemiprimeD1StackOwnerLookup.records rows [])).data k) :
    ∃q≤SemiprimeD1StackOwnerLookupBounds.runBound key rows+1,Runs program q .lookup before .clearReader
      (Sum.elim (SemiprimeD1StackOwnerLookup.done key rows []).data (fun k=>before (aux k))) :=by
  refine ⟨SemiprimeD1StackOwnerLookupExecution.loopTime key rows+2,?_,?_⟩
  · have ht:=SemiprimeD1StackOwnerLookupBounds.time_le key rows
    omega
  · apply SemiprimeD1StackProcedureCallsTrace.included_call program lookupStack Label.lookupCode Sum.inl_injective
      L.program .loop (fun _=>rfl) .lookup .clearReader rfl
      (SemiprimeD1StackOwnerLookupExecution.loopTime key rows+1)
      (SemiprimeD1StackOwnerLookup.initial key (SemiprimeD1StackOwnerLookup.records rows [])) (SemiprimeD1StackOwnerLookup.done key rows []) _ _
      rfl rfl rfl rfl (SemiprimeD1StackOwnerLookupExecution.source_run key rows [])
    · constructor
      · exact hi
      · intro k _;rfl
    · constructor
      · intro k;rfl
      · intro k hk
        rcases k with k|k
        · exact (hk k rfl).elim
        · rfl
/-- One literal local push preserves the entire other physical bank and all real outer returns. -/
theorem push_run (pc:Label) (next:Label) (k:Stack) (b:Bool) (before:Stack→List Bool)
    (hc:program pc=.base (.push k b next)) :
    Runs program 1 pc before next (Function.update before k (b::before k)) :=
  one_base program _ _ _ _ _ hc rfl rfl
/-- One literal local pop consumes ONLYthe actual physical Boolean head. -/
theorem pop_run (pc:Label) (empty low high:Label) (k:Stack) (before:Stack→List Bool) (xs:List Bool)
    (hc:program pc=.base (.pop k empty low high)) (hx:before k=xs) :
    Runs program 1 pc before (SemiprimeD1StackBytecode.choose empty low high xs.head?) (Function.update before k xs.tail) :=by
  apply one_base program pc _ (.pop k empty low high) before _ hc
  · simp only [SemiprimeD1StackBytecode.execute,hx]
  · simp only [SemiprimeD1StackBytecode.execute,hx]
/-- Real EOF peek does not silently discard any remaining singleton-result bytes. -/
theorem peek_run (pc:Label) (empty low high:Label) (k:Stack) (before:Stack→List Bool) (xs:List Bool)
    (hc:program pc=.base (.peek k empty low high)) (hx:before k=xs) :
    Runs program 1 pc before (SemiprimeD1StackBytecode.choose empty low high xs.head?) before :=by
  apply one_base program pc _ (.peek k empty low high) before before hc
  · simp only [SemiprimeD1StackBytecode.execute,hx]
  · rfl
/-- Every table/key/owner/row cleanup actually visits every byte and its final empty branch. -/
theorem drain_loop (pc:Label) (next:Label) (k:Stack)
    (hc:program pc=.base (.pop k next pc pc)) (before:Stack→List Bool) (xs:List Bool) (hx:before k=xs) :
    Runs program (xs.length+1) pc before next (Function.update before k []) :=by
  induction xs generalizing before with
  | nil=>exact pop_run pc next pc pc k before [] hc hx
  | cons b xs ih=>
    have h0:=pop_run pc next pc pc k before (b::xs) hc hx
    have h1:=ih (Function.update before k xs) (Function.update_self _ _ _)
    have hh:=join (by cases b <;> exact h0) h1
    simpa only [List.length_cons,Function.update_idem,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
/-- A literal same-program local call executes its ACTUALreturn instruction and preserves every outer return cell. -/
theorem local_call (pc entry next:Label)
    (hc:program pc=.call entry next)
    (q:Nat) (before after:Stack→List Bool)
    (hr:Runs program q entry before .counterReturn after) :
    Runs program (q+2) pc before next after :=by
  intro frames target h
  let mid:=SemiprimeD1StackCalls.execute (.call entry next) target
  have hm:SemiprimeD1StackCalls.run program 1 target=some mid:=by
    change SemiprimeD1StackCalls.step program target=some mid
    simp only [SemiprimeD1StackCalls.step,h.1,Option.map_some,hc,mid]
  have hat:At entry before (next::frames) mid:=by
    exact ⟨rfl,h.2.1,by simpa only [mid,SemiprimeD1StackCalls.execute] using congrArg (List.cons next) h.2.2⟩
  obtain ⟨finish,hf,hfAt⟩:=hr (next::frames) mid hat
  let last:SemiprimeD1StackCalls.State Stack Label:=⟨some next,finish.flag,some next,after,frames⟩
  have hl:SemiprimeD1StackCalls.run program 1 finish=some last:=by
    change SemiprimeD1StackCalls.step program finish=some last
    simp only [SemiprimeD1StackCalls.step,hfAt.1,Option.map_some,program,SemiprimeD1StackCalls.execute,hfAt.2.1,hfAt.2.2]
    rfl
  refine ⟨last,?_,rfl,rfl,rfl⟩
  have he:q+2=1+(q+1):=by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hl
end RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyPrimitives
