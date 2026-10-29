/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetBlocks
/-! # Actual block-source copies, field parser, frames, reversals and row logger
Every source byte and real return is charged by the corresponding frozen
primitive trace on the SAMEfixed31-role source program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackJetBlocksPrimitives
open SemiprimeD1StackJetBlocks SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
local notation "ctl" => Label.local
/-- Actual primitive fragments compose with all real outer caller frames intact. -/
theorem join {m n:Nat} {pc mid next:Label} {before between after:Stack→List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between next after) :
    Runs program (m+n) pc before next after :=runs_trans program m n pc mid next before between after h g
/-- Actual complete preserving copy, including both restoration loops and its real caller return. -/
theorem copy_call (what:Copy) (pc next:Control)
    (hc:program (ctl pc)=.call (.copy what 0) (ctl next)) (before:Stack→List Bool) (xs ys:List Bool)
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
  exact included_call program (copyStack what) (Label.copy what) (copy_injective what) SemiprimeD1StackCopy.code 0
    (fun _=>rfl) (ctl pc) (ctl next) hc (5*xs.length+3) start stop before _ rfl rfl
    (SemiprimeD1StackCopy.copy_words xs ys none) hi ho
/-- Actual source tape read by one of the actual coefficient parser. -/
def fieldInput :Stack :=fieldStack (.inl .input)
/-- Actual parsed output word for a actual coefficient field. -/
def fieldOutput :Stack :=fieldStack (.inl .output)
/-- Complete real field read, with actual true-valid marker retained until its physical pop. -/
theorem field_call (pc next:Control)
    (hc:program (ctl pc)=.call (.field (Field.active .tagPop (none,false))) (ctl next))
    (before:Stack→List Bool) (word tail:List Bool) (hi:before fieldInput=frame word tail)
    (ho:before fieldOutput=[]) (hs:before (aux .fieldScratch)=[]) (hv:before (aux .valid)=[]) :
    Runs program (8*word.length+7) (ctl pc) before (ctl next)
      (Function.update (Function.update (Function.update before fieldInput tail)
        fieldOutput word) (aux .valid) [true]) :=by
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
  exact included_call program fieldStack Label.field field_injective Field.code
    (Field.active .tagPop (none,false)) (fun _=>rfl) (ctl pc) (ctl next) hc (8*word.length+6) start stop before _ rfl rfl
    (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin h2
/-- Actual preserving raw binary-coefficient framing, with every source bit restored. -/
theorem frame_call (before:Stack→List Bool) (word buffer:List Bool)
    (hw:before (aux .word)=word) (hb:before (aux .frameBuffer)=buffer) (hs:before (aux .frameScratch)=[]) :
    Runs program (6*word.length+5) (ctl .frame) before (ctl .fieldTag)
      (Function.update before (aux .frameBuffer) (frame word buffer)) :=by
  let start:=SemiprimeD1StackFrame.state 0 none word buffer []
  let stop:=SemiprimeD1StackFrame.done word (frame word buffer)
  have hi:Link.DataRel frameStack before start.store before:=by
    constructor
    · intro k;fin_cases k
      · exact hw
      · exact hb
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update frameStack frame_injective before start.store before hi (1:Fin 3) (frame word buffer)
  have he:Function.update start.store 1 (frame word buffer)=stop.store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program frameStack Label.frame frame_injective SemiprimeD1StackFrame.code 0 (fun _=>rfl)
    (ctl .frame) (ctl .fieldTag) rfl (6*word.length+4) start stop before _ rfl rfl
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
/-- The REALrow logger consumes no supplied row answer; it frames the actual physical row and restores it. -/
theorem body_call (before:Stack→List Bool) (row hist:List Bool)
    (hr:before (aux .row)=row) (hs:before (aux .logScratch)=[]) (hh:before (aux .history)=hist) :
    ∃q≤ 6*(2*row.length+3)+1,Runs program q (ctl .logRow) before (ctl .clearRow)
      (Function.update before (aux .history) ((true::frame row []).reverse++hist)) :=by
  obtain ⟨q,hq,hRun⟩:=SemiprimeD1StackAssignmentBody.body_run row hist
  refine ⟨q+1,by omega,?_⟩
  let start:SemiprimeD1StackBytecode.State Body.Stack Body.Label:=⟨some Body.entry,none,SemiprimeD1StackAssignmentBody.contents row [] hist⟩
  let stop:SemiprimeD1StackBytecode.State Body.Stack Body.Label:=⟨none,none,SemiprimeD1StackAssignmentBody.contents row [] ((true::frame row []).reverse++hist)⟩
  have hi:Link.DataRel bodyStack before start.store before:=by
    constructor
    · intro k;cases k
      · exact hr
      · exact hs
      · exact hh
    · intro k _;rfl
  have ho:=Link.data_update bodyStack body_injective before start.store before hi .history ((true::frame row []).reverse++hist)
  have he:Function.update start.store .history ((true::frame row []).reverse++hist)=stop.store:=by funext k;cases k <;> rfl
  rw [he] at ho
  exact included_call program bodyStack Label.body body_injective Body.code Body.entry (fun _=>rfl)
    (ctl .logRow) (ctl .clearRow) rfl q start stop before _ rfl rfl hRun hi ho
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
end RiemannGaussian.SemiprimeD1StackJetBlocksPrimitives
