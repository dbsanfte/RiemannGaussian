/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketRows
/-! # Real packet-row copy, Field, lookup, frame, reverse and cleanup calls -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketRowsPrimitives
open SemiprimeD1StackPacketRows SemiprimeD1StackProcedureTrace
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
theorem field_call (part:Field) (pc next:Control)
    (hc:program (ctl pc)=.call (.field part (F.active .tagPop (none,false))) (ctl next))
    (before:Stack→List Bool) (word tail:List Bool)
    (hi:before (fieldStack part (.inl .input))=frame word tail)
    (ho:before (fieldStack part (.inl .output))=[])
    (hs:before (fieldStack part (.inl .scratch))=[])
    (hv:before (fieldStack part (.inr ()))=[]) :
    Runs program (8*word.length+7) (ctl pc) before (ctl next)
      (Function.update (Function.update (Function.update before (fieldStack part (.inl .input)) tail)
        (fieldStack part (.inl .output)) word) (fieldStack part (.inr ())) [true]) :=by
  let start:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let stop:SemiprimeD1StackBytecode.State F.Stack F.Label:=
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
  exact included_call program (fieldStack part) (Label.field part) (field_injective part) F.code
    (F.active .tagPop (none,false)) (fun _=>rfl) (ctl pc) (ctl next) hc (8*word.length+6) start stop before _ rfl rfl
    (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin h2
/-- Real preserving Frame writes a physical field onto its existing dictionary/vector tail. -/
theorem frame_call (right:Bool) (pc next:Control)
    (hc:program (ctl pc)=.call (.frame right 0) (ctl next)) (before:Stack→List Bool) (word buffer:List Bool)
    (hw:before (frameStack right 0)=word) (hb:before (frameStack right 1)=buffer) (hs:before (frameStack right 2)=[]) :
    Runs program (6*word.length+5) (ctl pc) before (ctl next)
      (Function.update before (frameStack right 1) (frame word buffer)) :=by
  let start:=SemiprimeD1StackFrame.state 0 none word buffer []
  let stop:=SemiprimeD1StackFrame.done word (frame word buffer)
  have hi:Link.DataRel (frameStack right) before start.store before:=by
    constructor
    · intro k;fin_cases k
      · exact hw
      · exact hb
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update (frameStack right) (frame_injective right) before start.store before hi (1:Fin 3) (frame word buffer)
  have he:Function.update start.store 1 (frame word buffer)=stop.store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program (frameStack right) (Label.frame right) (frame_injective right) SemiprimeD1StackFrame.code 0 (fun _=>rfl)
    (ctl pc) (ctl next) hc (6*word.length+4) start stop before _ rfl rfl
    (SemiprimeD1StackFrame.frame_words word buffer none) hi ho
/-- Every inner-owner/row/final reversal consumes its real source and pays all bytes and return cells. -/
theorem reverse_call (what:Reverse) (pc next:Control)
    (hc:program (ctl pc)=.call (.reverse what 0) (ctl next)) (before:Stack→List Bool) (xs ys:List Bool)
    (hx:before (reverseStack what 0)=xs) (hy:before (reverseStack what 1)=ys) :
    Runs program (2*xs.length+3) (ctl pc) before (ctl next)
      (Function.update (Function.update before (reverseStack what 0) []) (reverseStack what 1) (xs.reverse++ys)) :=by
  let start:=SemiprimeD1StackReverseWord.state none xs ys
  let stop:=SemiprimeD1StackReverseWord.done (xs.reverse++ys)
  have hi:Link.DataRel (reverseStack what) before start.store before:=by
    constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
    · intro k _;rfl
  have h0:=Link.data_update (reverseStack what) (reverse_injective what) before start.store before hi (0:Fin 2) []
  have h1:=Link.data_update (reverseStack what) (reverse_injective what) before _ _ h0 (1:Fin 2) (xs.reverse++ys)
  have he:Function.update (Function.update start.store 0 []) 1 (xs.reverse++ys)=stop.store:=by funext k;fin_cases k <;> rfl
  rw [he] at h1
  exact included_call program (reverseStack what) (Label.reverse what) (reverse_injective what)
    SemiprimeD1StackReverseWord.code 0 (fun _=>rfl) (ctl pc) (ctl next) hc (2*xs.length+2) start stop before _ rfl rfl
    (SemiprimeD1StackReverseWord.reverse_run xs ys none) hi h1
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
/-- The real parser's true-valid byte is physically consumed before returning the complete unframed word. -/
theorem field_valid (part:Field) (pc validPC:Control) (next:Label)
    (hc:program (ctl pc)=.call (.field part (F.active .tagPop (none,false))) (ctl validPC))
    (hp:program (ctl validPC)=.base (.pop parserValid (ctl .reject) (ctl .reject) next))
    (before:Stack→List Bool) (word tail:List Bool)
    (hi:before (fieldStack part (.inl .input))=frame word tail)
    (ho:before (fieldStack part (.inl .output))=[])
    (hs:before (fieldStack part (.inl .scratch))=[])
    (hv:before parserValid=[]) :
    Runs program (8*word.length+8) (ctl pc) before next
      (Function.update (Function.update before (fieldStack part (.inl .input)) tail)
        (fieldStack part (.inl .output)) word) :=by
  let after:=Function.update (Function.update before (fieldStack part (.inl .input)) tail)
    (fieldStack part (.inl .output)) word
  have hout:parserValid ≠ fieldStack part (.inl .output):=
    by
      intro h
      have he:=field_injective part (show fieldStack part (.inr ())=fieldStack part (.inl .output) from h)
      cases he
  have hin:parserValid ≠ fieldStack part (.inl .input):=
    by
      intro h
      have he:=field_injective part (show fieldStack part (.inr ())=fieldStack part (.inl .input) from h)
      cases he
  have hvalid:after parserValid=[]:=by
    dsimp only [after]
    rw [Function.update_of_ne hout,Function.update_of_ne hin,hv]
  have h0:=field_call part pc validPC hc before word tail hi ho hs hv
  change Runs program (8*word.length+7) _ _ _ (Function.update after parserValid [true]) at h0
  have h1:=pop_run validPC (ctl .reject) (ctl .reject) next parserValid
    (Function.update after parserValid [true]) [true] hp (Function.update_self _ _ _)
  change Runs program 1 _ _ _ (Function.update (Function.update after parserValid [true]) parserValid []) at h1
  have hz:Function.update after parserValid []=after:=by
    simpa only [hvalid] using (Function.update_eq_self parserValid after)
  rw [Function.update_idem,hz] at h1
  have h:=join h0 h1
  simpa only [Nat.add_assoc,SemiprimeD1StackBytecode.choose,List.head?_cons,after] using h
/-- Whole actual11-role lookup call; every private input/history/output and all outer return frames survive. -/
theorem lookup_call (right:Bool) (before:Stack→List Bool) (q:List Bool) (rows:List (List Bool×List Bool))
    (hi:∀k,before (lookupStack k)=(SemiprimeD1StackOwnerLookup.initial q (SemiprimeD1StackOwnerLookup.records rows [])).data k) :
    ∃t ≤ SemiprimeD1StackOwnerLookupBounds.runBound q rows+1,
      Runs program t (ctl (.lookup right)) before (ctl (.lookupFound right))
        (Sum.elim (SemiprimeD1StackOwnerLookup.done q rows []).data (fun k=>before (aux k))) :=by
  refine ⟨SemiprimeD1StackOwnerLookupExecution.loopTime q rows+2,?_,?_⟩
  · have h:=SemiprimeD1StackOwnerLookupBounds.time_le q rows
    omega
  · apply SemiprimeD1StackProcedureCallsTrace.included_call program lookupStack Label.lookupCode Sum.inl_injective
      L.program .loop (fun _=>rfl) (ctl (.lookup right)) (ctl (.lookupFound right)) rfl
      (SemiprimeD1StackOwnerLookupExecution.loopTime q rows+1)
      (SemiprimeD1StackOwnerLookup.initial q (SemiprimeD1StackOwnerLookup.records rows []))
      (SemiprimeD1StackOwnerLookup.done q rows []) before _ rfl rfl rfl rfl
      (SemiprimeD1StackOwnerLookupExecution.source_run q rows [])
    · exact ⟨hi,fun _ _=>rfl⟩
    · constructor
      · intro k;rfl
      · intro k hk
        rcases k with k|k
        · exact (hk k rfl).elim
        · rfl
/-- A real nonempty unread suffix physically passes presence, including a leading false final terminator. -/
theorem presence_run (right:Bool) (before:Stack→List Bool) (xs:List Bool)
    (hx:before lookupReader=xs) (hn:xs≠[]) :
    Runs program 1 (ctl (.lookupFound right)) before (ctl (.clearLookupReader right)) before :=by
  have h:=peek_run (.lookupFound right) (ctl .reject) (ctl (.clearLookupReader right))
    (ctl (.clearLookupReader right)) lookupReader before xs rfl hx
  cases xs with
  | nil=>exact (hn rfl).elim
  | cons b xs=>cases b <;> exact h
end RiemannGaussian.SemiprimeD1StackPacketRowsPrimitives
