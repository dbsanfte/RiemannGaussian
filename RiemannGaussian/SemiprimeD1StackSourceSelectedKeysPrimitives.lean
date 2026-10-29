/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectedKeys
/-! # Real preserving copy and literal selected-key-source operations -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectedKeysPrimitives
open SemiprimeD1StackSourceSelectedKeys
open SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Same literal program trace fragments compose with arbitrary actual caller return cells. -/
theorem join {m n:Nat} {pc mid finish:Label} {before between after:Stack→List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between finish after) :
    Runs program (m+n) pc before finish after :=runs_trans program _ _ _ _ _ _ _ _ h g
/-- Every paid preserving-copy call changes only its actual destination. -/
theorem copy_call (part:Copy) (pc next:Label) (hc:program pc=.call (.copier part 0) next)
    (bank:Stack→List Bool) (hd:bank (copyStack part 1)=[]) (hs:bank (copyStack part 2)=[]) :
    Runs program (5*(bank (copyStack part 0)).length+4) pc bank next
      (Function.update bank (copyStack part 1) (bank (copyStack part 0))) :=by
  let before:=SemiprimeD1StackCopy.state 0 none (bank (copyStack part 0)) [] []
  let after:=SemiprimeD1StackCopy.done (bank (copyStack part 0)) (bank (copyStack part 0)++[])
  have hin:Link.DataRel (copyStack part) bank before.store bank:=by
    constructor
    · intro i;fin_cases i
      · rfl
      · exact hd
      · exact hs
    · intro k _;rfl
  apply included_call program (copyStack part) (Label.copier part) (copy_injective part)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc (5*(bank (copyStack part 0)).length+3)
    before after _ _ rfl rfl (SemiprimeD1StackCopy.copy_words _ [] none) hin
  have h:=Link.data_update (copyStack part) (copy_injective part) bank before.store bank hin 1 (bank (copyStack part 0))
  have he:Function.update before.store 1 (bank (copyStack part 0))=after.store:=by
    dsimp only [after]
    rw [List.append_nil]
    funext i;fin_cases i <;> rfl
  simpa only [he] using h
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
/-- Both real preserving Frame calls retain their actual source and prefix the existing physical buffer/tail. -/
theorem frame_call (part:Frame) (pc next:Label)
    (hc:program pc=.call (.framer part 0) next) (before:Stack→List Bool) (word buffer:List Bool)
    (hw:before (frameStack part 0)=word) (hb:before (frameStack part 1)=buffer) (hs:before (frameStack part 2)=[]) :
    Runs program (6*word.length+5) pc before next
      (Function.update before (frameStack part 1) (SemiprimeSourceHistogramKeyBits.frame word buffer)) :=by
  let start:=SemiprimeD1StackFrame.state 0 none word buffer []
  let stop:=SemiprimeD1StackFrame.done word (SemiprimeSourceHistogramKeyBits.frame word buffer)
  have hi:Link.DataRel (frameStack part) before start.store before:=by
    constructor
    · intro k;fin_cases k
      · exact hw
      · exact hb
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update (frameStack part) (frame_injective part) before start.store before hi (1:Fin 3)
    (SemiprimeSourceHistogramKeyBits.frame word buffer)
  have he:Function.update start.store 1 (SemiprimeSourceHistogramKeyBits.frame word buffer)=stop.store:=by
    funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program (frameStack part) (Label.framer part) (frame_injective part) SemiprimeD1StackFrame.code 0
    (fun _=>rfl) pc next hc (6*word.length+4) start stop before _ rfl rfl
    (SemiprimeD1StackFrame.frame_words word buffer none) hi ho
/-- A real reversal consumes its source and prepends onto the actual history/output destination. -/
theorem reverse_call (part:Reverse) (pc next:Label)
    (hc:program pc=.call (.reversal part 0) next) (before:Stack→List Bool) (xs ys:List Bool)
    (hx:before (reverseStack part 0)=xs) (hy:before (reverseStack part 1)=ys) :
    Runs program (2*xs.length+3) pc before next
      (Function.update (Function.update before (reverseStack part 0) []) (reverseStack part 1) (xs.reverse++ys)) :=by
  let start:=SemiprimeD1StackReverseWord.state none xs ys
  let stop:=SemiprimeD1StackReverseWord.done (xs.reverse++ys)
  have hi:Link.DataRel (reverseStack part) before start.store before:=by
    constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
    · intro k _;rfl
  have h0:=Link.data_update (reverseStack part) (reverse_injective part) before start.store before hi (0:Fin 2) []
  have h1:=Link.data_update (reverseStack part) (reverse_injective part) before _ _ h0 (1:Fin 2) (xs.reverse++ys)
  have he:Function.update (Function.update start.store 0 []) 1 (xs.reverse++ys)=stop.store:=by
    funext k;fin_cases k <;> rfl
  rw [he] at h1
  exact included_call program (reverseStack part) (Label.reversal part) (reverse_injective part)
    SemiprimeD1StackReverseWord.code 0 (fun _=>rfl) pc next hc (2*xs.length+2) start stop before _ rfl rfl
    (SemiprimeD1StackReverseWord.reverse_run xs ys none) hi h1
/-- Every original occurrence field is physically parsed, paying the terminating delimiter and actual true-valid singleton. -/
theorem parse_call (part:Part) (bank:Stack→List Bool) (word tail:List Bool)
    (hi:bank (aux .reader)=SemiprimeSourceHistogramKeyBits.frame word tail)
    (ho:bank (variableKey part)=[]) (hs:bank (aux .fieldScratch)=[]) (hv:bank (aux .valid)=[]) :
    Runs program (8*word.length+7) (.parse part) bank (.valid part)
      (Function.update (Function.update (Function.update bank (aux .reader) tail) (variableKey part) word) (aux .valid) [true]) :=by
  let before:=SemiprimeD1TensorTapeFieldBytecode.initial (SemiprimeSourceHistogramKeyBits.frame word tail) []
  let after:SemiprimeD1StackBytecode.State Field.Stack Field.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:Link.DataRel (fieldStack part) bank before.store bank:=by
    constructor
    · intro k;rcases k with k|k
      · cases k
        · exact hi
        · exact hs
        · exact ho
      · cases k;exact hv
    · intro k _;rfl
  have h0:=Link.data_update (fieldStack part) (field_injective part) bank before.store bank hin (.inl .input) tail
  have h1:=Link.data_update (fieldStack part) (field_injective part) bank _ _ h0 (.inl .output) word
  have h2:=Link.data_update (fieldStack part) (field_injective part) bank _ _ h1 (.inr ()) [true]
  have he:Function.update (Function.update (Function.update before.store (.inl .input) tail) (.inl .output) word)
      (.inr ()) [true]=after.store:=by funext k;rcases k with k|k <;> cases k <;> rfl
  rw [he] at h2
  exact included_call program (fieldStack part) (Label.parser part) (field_injective part)
    Field.code (Field.active .tagPop (none,false)) (fun _=>rfl) (.parse part) (.valid part) rfl
    (8*word.length+6) before after bank _ rfl rfl (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin h2
/-- Complete real Env25 preserving lookup, with its actual copies/parsers/comparisons/marker/drain/return included. -/
theorem lookup_call (part:Part) (bank:Stack→List Bool) (ids:List (List Bool)) (chosen q pfx:List Bool)
    (hi:∀k,bank (environmentStack k)=(SemiprimeD1StackSourceEnvironmentExecution.lookupReady ids chosen q pfx).data k) :
    ∃t≤201*(q.length+1)*((SemiprimeD1StackSourceEnvironmentEncoding.dictionary ids).length+1)+1,
      Runs program t (.lookup part) bank (.readFound part)
        (Sum.elim (SemiprimeD1StackSourceEnvironmentExecution.lookupDone ids chosen q pfx).data (fun k=>bank (aux k))) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackSourceEnvironmentExecution.lookup_run ids chosen q pfx
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program environmentStack Label.environment environment_injective
    E.program (.local .lookup) (fun _=>rfl) (.lookup part) (.readFound part) rfl t
    (SemiprimeD1StackSourceEnvironmentExecution.lookupReady ids chosen q pfx)
    (SemiprimeD1StackSourceEnvironmentExecution.lookupDone ids chosen q pfx) bank _ rfl rfl rfl rfl hr
  · constructor
    · exact hi
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
end RiemannGaussian.SemiprimeD1StackSourceSelectedKeysPrimitives
