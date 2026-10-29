/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineInventory
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Actual preserving copies and paid byte scans/drains -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffinePrimitives
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineInventory SemiprimeD1StackProcedureTrace
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
    (hc:program pc=.call (.copy what 0) next) (before:Stack→List Bool) (xs ys:List Bool)
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
  exact included_call program (copyStack what) (Label.copy what) (copy_injective what) SemiprimeD1StackCopy.code 0
    (fun _=>rfl) pc next hc (5*xs.length+3) start stop before _ rfl rfl
    (SemiprimeD1StackCopy.copy_words xs ys none) hi ho
/-- One literal local push preserves the entire other physical bank and all real outer returns. -/
theorem push_run (pc:Label) (next:Label) (k:Stack) (b:Bool) (before:Stack→List Bool)
    (hc:program pc=.base (.push k b next)) :
    Runs program 1 pc before next (Function.update before k (b::before k)) :=
  one_base program _ _ _ _ _ hc rfl rfl
/-- One literal local pop consumes only the actual physical Boolean head. -/
theorem pop_run (pc:Label) (empty low high:Label) (k:Stack) (before:Stack→List Bool) (xs:List Bool)
    (hc:program pc=.base (.pop k empty low high)) (hx:before k=xs) :
    Runs program 1 pc before (SemiprimeD1StackBytecode.choose empty low high xs.head?) (Function.update before k xs.tail) :=by
  apply one_base program pc _ (.pop k empty low high) before _ hc
  · simp only [SemiprimeD1StackBytecode.execute,hx]
  · simp only [SemiprimeD1StackBytecode.execute,hx]
/-- Every actual source peek preserves the entire acquired word. -/
theorem peek_run (pc:Label) (empty low high:Label) (k:Stack) (before:Stack→List Bool) (xs:List Bool)
    (hc:program pc=.base (.peek k empty low high)) (hx:before k=xs) :
    Runs program 1 pc before (SemiprimeD1StackBytecode.choose empty low high xs.head?) before :=by
  apply one_base program pc _ (.peek k empty low high) before before hc
  · simp only [SemiprimeD1StackBytecode.execute,hx]
  · rfl
/-- Every quotient/remainder/GCD/magnitude cleanup actually visits every byte and its final empty branch. -/
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
    (hc:program pc=.call (.frame part 0) next) (before:Stack→List Bool) (word buffer:List Bool)
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
  exact included_call program (frameStack part) (Label.frame part) (frame_injective part) SemiprimeD1StackFrame.code 0
    (fun _=>rfl) pc next hc (6*word.length+4) start stop before _ rfl rfl
    (SemiprimeD1StackFrame.frame_words word buffer none) hi ho
/-- A literal same-program local call executes its ACTUALreturn instruction and preserves every outer return cell. -/
theorem local_call (pc entry stopped next:Label)
    (hc:program pc=.call entry next)
    (hret:program stopped=.ret) (q:Nat) (before after:Stack→List Bool)
    (hr:Runs program q entry before stopped after) :
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
    simp only [SemiprimeD1StackCalls.step,hfAt.1,Option.map_some,hret,SemiprimeD1StackCalls.execute,hfAt.2.1,hfAt.2.2]
    rfl
  refine ⟨last,?_,rfl,rfl,rfl⟩
  have he:q+2=1+(q+1):=by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hl
/-- Actual consuming two-tape reversal includes every bit, EOF, return and caller transition. -/
theorem reverse_call (second:Bool) (pc next:Label)
    (hc:program pc=.call (.reverse second 0) next) (before:Stack→List Bool) (xs ys:List Bool)
    (hx:before (reverseStack second 0)=xs) (hy:before (reverseStack second 1)=ys) :
    Runs program (2*xs.length+3) pc before next
      (Function.update (Function.update before (reverseStack second 0) []) (reverseStack second 1) (xs.reverse++ys)):=by
  let start:=SemiprimeD1StackReverseWord.state none xs ys
  let stop:=SemiprimeD1StackReverseWord.done (xs.reverse++ys)
  have hi:Link.DataRel (reverseStack second) before start.store before:=by
    constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
    · intro k _;rfl
  have h0:=Link.data_update (reverseStack second) (reverse_injective second) before start.store before hi (0:Fin 2) []
  have h1:=Link.data_update (reverseStack second) (reverse_injective second) before _ _ h0 (1:Fin 2) (xs.reverse++ys)
  have he:Function.update (Function.update start.store 0 []) 1 (xs.reverse++ys)=stop.store:=by funext k;fin_cases k <;> rfl
  rw [he] at h1
  exact included_call program (reverseStack second) (Label.reverse second) (reverse_injective second)
    SemiprimeD1StackReverseWord.code 0 (fun _=>rfl) pc next hc (2*xs.length+2) start stop before _ rfl rfl
    (SemiprimeD1StackReverseWord.reverse_run xs ys none) hi h1
/-- Complete actual four-role Field acquisition preserves every foreign source/cache byte. -/
theorem field_call (site:Field) (before:Stack→List Bool) (word tail:List Bool)
    (hi:before (fieldInput site)=frame word tail) (hs:before (oldAux .frameScratch)=[])
    (ho:before (fieldOutput site)=[]) (hv:before (oldAux .scan)=[]) :
    Runs program (8*word.length+7) (.local (.field site)) before (.local (.valid site))
      (Function.update (Function.update (Function.update before (fieldInput site) tail) (fieldOutput site) word) (oldAux .scan) [true]):=by
  let start:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let stop:SemiprimeD1StackBytecode.State F.Stack F.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:Link.DataRel (fieldStack site) before start.store before:=by
    constructor
    · intro k;rcases k with k|k
      · cases k with
        | input=>exact hi
        | scratch=>exact hs
        | output=>exact ho
      · cases k;exact hv
    · intro k _;rfl
  apply included_call program (fieldStack site) (Label.field site) (field_injective site) F.code
    (F.active .tagPop (none,false)) (fun _=>rfl) (.local (.field site)) (.local (.valid site)) rfl
    (8*word.length+6) start stop before _ rfl rfl (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin
  have h0:=Link.data_update (fieldStack site) (field_injective site) before start.store before hin (.inl .input) tail
  have h1:=Link.data_update (fieldStack site) (field_injective site) before _ _ h0 (.inl .output) word
  have h2:=Link.data_update (fieldStack site) (field_injective site) before _ _ h1 (.inr ()) [true]
  have he:Function.update (Function.update (Function.update start.store (.inl .input) tail) (.inl .output) word) (.inr ()) [true]=stop.store:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  simpa only [he,fieldStack] using h2
/-- Actual TRUE validity consumption clears its flag before the next literal continuation. -/
theorem field_read (site:Field) (before:Stack→List Bool) (word tail:List Bool)
    (hi:before (fieldInput site)=frame word tail) (hs:before (oldAux .frameScratch)=[])
    (ho:before (fieldOutput site)=[]) (hv:before (oldAux .scan)=[]) :
    Runs program (8*word.length+8) (.local (.field site)) before (afterField site)
      (Function.update (Function.update before (fieldInput site) tail) (fieldOutput site) word):=by
  have h0:=field_call site before word tail hi hs ho hv
  let after:=Function.update (Function.update (Function.update before (fieldInput site) tail) (fieldOutput site) word) (oldAux .scan) [true]
  have h1:=pop_run (.local (.valid site)) (.local .abort) (.local .abort) (afterField site) (oldAux .scan) after [true] rfl (Function.update_self _ _ _)
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h1
  have hn0:fieldInput site≠oldAux .scan:=by
    intro h
    have he:(.inl .input:F.Stack)=.inr ():=field_injective site (show fieldStack site (.inl .input)=fieldStack site (.inr ()) from h)
    cases he
  have hn1:fieldOutput site≠oldAux .scan:=by
    intro h
    have he:(.inl .output:F.Stack)=.inr ():=field_injective site (show fieldStack site (.inl .output)=fieldStack site (.inr ()) from h)
    cases he
  have he:Function.update after (oldAux .scan) []=Function.update (Function.update before (fieldInput site) tail) (fieldOutput site) word:=by
    dsimp only [after]
    rw [Function.update_idem,Function.update_comm hn1,Function.update_comm hn0]
    rw [←hv,Function.update_eq_self]
  rw [he] at h1
  have h:=join h0 h1
  convert h using 1
end RiemannGaussian.SemiprimeD1StackRecoveryAffinePrimitives
