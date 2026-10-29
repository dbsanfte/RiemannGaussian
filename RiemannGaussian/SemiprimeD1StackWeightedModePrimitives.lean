/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedMode
/-! # Actual primitive traces and real recursive calls for feasible weighted tuples -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModePrimitives
open SemiprimeD1StackWeightedMode SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => (Sum.inl : Control→Label)
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Literal copy input address. -/
def copySource (site:Copy) :Stack:=copyStack site 0
/-- Literal copy output address. -/
def copyTarget (site:Copy) :Stack:=copyStack site 1
/-- Actual separate copy operands. -/
theorem copy_ne (site:Copy) :copySource site≠copyTarget site:=by cases site <;> decide
/-- Copy restoration scratch never aliases its target. -/
theorem copy_scratch_ne (site:Copy) :Stack.copyScratch≠copyTarget site:=by cases site <;> decide
/-- One included preserving copy includes its real call and return. -/
theorem copy_call (site:Copy) (pc next:Control)
    (hc:program (ctl pc)=.call (copyLabel site 0) (ctl next))
    (s:Stack→List Bool) (xs ys:List Bool)
    (hx:s (copySource site)=xs) (hy:s (copyTarget site)=ys) (hz:s .copyScratch=[]) :
    Runs program (5*xs.length+4) (ctl pc) s (ctl next)
      (Function.update s (copyTarget site) (xs++ys)):=by
  apply included_call program (copyStack site) (copyLabel site) (copy_injective site)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) (ctl pc) (ctl next) hc (5*xs.length+3)
    (SemiprimeD1StackCopy.state 0 none xs ys []) (SemiprimeD1StackCopy.done xs (xs++ys)) s _
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
      · change Function.update s (copyTarget site) (xs++ys) (copySource site)=xs
        rw [Function.update_of_ne (copy_ne site),hx]
      · exact Function.update_self _ _ _
      · change Function.update s (copyTarget site) (xs++ys) .copyScratch=[]
        rw [Function.update_of_ne (copy_scratch_ne site),hz]
    · intro k hk
      exact Function.update_of_ne (fun he=>hk 1 he.symm) _ _
/-- Literal frame input address. -/
def frameSource (site:Frame) :Stack:=frameStack site 0
/-- Literal frame destination. -/
def frameTarget (site:Frame) :Stack:=frameStack site 1
/-- Actual frame input and output remain disjoint. -/
theorem frame_ne (site:Frame) :frameSource site≠frameTarget site:=by
  cases site with
  | path|tuple=>decide
  | save i=>fin_cases i <;> decide
/-- Every real framing scratch is disjoint from its destination. -/
theorem frame_scratch_ne (site:Frame) :Stack.frameScratch≠frameTarget site:=by
  cases site with
  | path|tuple=>decide
  | save i=>fin_cases i <;> decide
/-- One actual preserving frame, including the physical return transition. -/
theorem frame_call (site:Frame) (pc:Control) (next:Label)
    (hc:program (ctl pc)=.call (frameLabel site 0) next)
    (s:Stack→List Bool) (xs ys:List Bool)
    (hx:s (frameSource site)=xs) (hy:s (frameTarget site)=ys) (hz:s .frameScratch=[]) :
    Runs program (6*xs.length+5) (ctl pc) s next
      (Function.update s (frameTarget site) (frame xs ys)):=by
  apply included_call program (frameStack site) (frameLabel site) (frame_injective site)
    SemiprimeD1StackFrame.code 0 (fun _=>rfl) (ctl pc) next hc (6*xs.length+4)
    (SemiprimeD1StackFrame.state 0 none xs ys []) (SemiprimeD1StackFrame.done xs (frame xs ys)) s _
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
      · change Function.update s (frameTarget site) (frame xs ys) (frameSource site)=xs
        rw [Function.update_of_ne (frame_ne site),hx]
      · exact Function.update_self _ _ _
      · change Function.update s (frameTarget site) (frame xs ys) .frameScratch=[]
        rw [Function.update_of_ne (frame_scratch_ne site),hz]
    · intro k hk
      exact Function.update_of_ne (fun he=>hk 1 he.symm) _ _
/-- Literal physical field reader. -/
def parseInput (site:Parse) :Stack:=parseStack site (.inl .input)
/-- Literal physical field output. -/
def parseOutput (site:Parse) :Stack:=parseStack site (.inl .output)
/-- Each actual parser has four distinct addresses. -/
theorem parse_read_ne (site:Parse) :parseInput site≠parseOutput site:=by
  cases site with
  | weight|path=>decide
  | restore i=>fin_cases i <;> decide
/-- Actual one-field parse, with the true validity marker and real continuation return. -/
theorem field_call (site:Parse) (pc next:Control)
    (hc:program (ctl pc)=.call (parseLabel site (Field.active .tagPop (none,false))) (ctl next))
    (s:Stack→List Bool) (word tail:List Bool)
    (hi:s (parseInput site)=frame word tail) (ho:s (parseOutput site)=[])
    (hs:s .fieldScratch=[]) (hv:s .valid=[]) :
    Runs program (8*word.length+7) (ctl pc) s (ctl next)
      (Function.update (Function.update (Function.update s (parseInput site) tail) (parseOutput site) word) .valid [true]):=by
  let before:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let after:SemiprimeD1StackBytecode.State Field.Stack Field.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:Link.DataRel (parseStack site) s before.store s:=by
    constructor
    · intro k;rcases k with k|k
      · cases k <;> simpa only [parseInput,parseOutput,parseStack,before,
          SemiprimeD1TensorTapeFieldBytecode.initial,SemiprimeD1TensorTapeFieldMachine.contents] using
          (by first | exact hi | exact ho | exact hs)
      · cases k;exact hv
    · intro k _;rfl
  apply included_call program (parseStack site) (parseLabel site) (parse_injective site) Field.code
    (Field.active .tagPop (none,false)) (fun _=>rfl) (ctl pc) (ctl next) hc
    (8*word.length+6) before after s _ rfl rfl
    (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin
  have h0:=Link.data_update (parseStack site) (parse_injective site) s before.store s hin (.inl .input) tail
  have h1:=Link.data_update (parseStack site) (parse_injective site) s _ _ h0 (.inl .output) word
  have h2:=Link.data_update (parseStack site) (parse_injective site) s _ _ h1 (.inr ()) [true]
  have he:Function.update (Function.update (Function.update before.store (.inl .input) tail)
      (.inl .output) word) (.inr ()) [true]=after.store:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  simpa only [he,parseInput,parseOutput,parseStack] using h2
/-- Every emitted tuple is physically copied to the chronological reverse log. -/
theorem body_call (s:Stack→List Bool) (word hist:List Bool)
    (hw:s .tuple=word) (hs:s .copyScratch=[]) (hh:s .history=hist) :
    ∃t ≤ 6*(2*word.length+3)+1,Runs program t (ctl .emit) s (ctl (.cleanup 0))
      (Function.update s .history ((true::frame word []).reverse++hist)):=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackAssignmentBody.body_run word hist
  refine ⟨t+1,by omega,?_⟩
  apply included_call program bodyStack bodyLabel body_injective Body.code Body.entry (fun _=>rfl)
    (ctl .emit) (ctl (.cleanup 0)) rfl t
    (⟨some Body.entry,none,SemiprimeD1StackAssignmentBody.contents word [] hist⟩:
      SemiprimeD1StackBytecode.State Body.Stack Body.Label)
    (⟨none,none,SemiprimeD1StackAssignmentBody.contents word [] ((true::frame word []).reverse++hist)⟩:
      SemiprimeD1StackBytecode.State Body.Stack Body.Label) s _ rfl rfl hr
  · constructor
    · intro k;cases k <;> first | exact hw | exact hs | exact hh
    · intro k _;rfl
  · constructor
    · intro k;cases k
      · exact (Function.update_of_ne (by decide:Stack.tuple≠.history) _ _).trans hw
      · exact (Function.update_of_ne (by decide:Stack.copyScratch≠.history) _ _).trans hs
      · exact Function.update_self _ _ _
    · intro k hk
      exact Function.update_of_ne (fun he=>hk .history he.symm) _ _
/-- One real final reversal clears history and prepends its bytes to the seeded output. -/
theorem reverse_call (s:Stack→List Bool) (hist out:List Bool) (hh:s .history=hist) (ho:s .output=out) :
    Runs program (2*hist.length+3) (ctl .reverse) s (ctl .done)
      (Function.update (Function.update s .history []) .output (hist.reverse++out)):=by
  apply included_call program reverseStack reverseLabel reverse_injective SemiprimeD1StackReverseWord.code 0
    (fun _=>rfl) (ctl .reverse) (ctl .done) rfl (2*hist.length+2)
    (SemiprimeD1StackReverseWord.state none hist out) (SemiprimeD1StackReverseWord.done (hist.reverse++out)) s _
  · rfl
  · rfl
  · exact SemiprimeD1StackReverseWord.reverse_run hist out none
  · constructor
    · intro k;fin_cases k
      · exact hh
      · exact ho
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k
      · change Function.update (Function.update s .history []) .output (hist.reverse++out) .history=[]
        rw [Function.update_of_ne (by decide:Stack.history≠.output),Function.update_self]
      · exact Function.update_self _ _ _
    · intro k hk
      have h0:Stack.history≠k:=hk 0
      have h1:Stack.output≠k:=hk 1
      rw [Function.update_of_ne h1.symm,Function.update_of_ne h0.symm]
/-- One physical push at a literal control location. -/
theorem push_run (pc:Control) (next:Label) (k:Stack) (b:Bool) (s:Stack→List Bool)
    (hc:program (ctl pc)=.base (.push k b next)) :
    Runs program 1 (ctl pc) s next (Function.update s k (b::s k)):=by
  exact one_base program _ _ _ _ _ hc rfl rfl
/-- One physical pop at a known physical word, preserving all other tape cells. -/
theorem pop_run (pc:Control) (empty low high:Label) (k:Stack) (s:Stack→List Bool) (xs:List Bool)
    (hc:program (ctl pc)=.base (.pop k empty low high)) (hx:s k=xs) :
    Runs program 1 (ctl pc) s (SemiprimeD1StackBytecode.choose empty low high xs.head?)
      (Function.update s k xs.tail):=by
  apply one_base program _ _ _ _ _ hc
  · simp only [SemiprimeD1StackBytecode.execute,hx]
  · simp only [SemiprimeD1StackBytecode.execute,hx]
/-- Literal draining visits every actual bit and pays the final EOF. -/
theorem drain_loop (pc:Control) (next:Label) (k:Stack)
    (hc:program (ctl pc)=.base (.pop k next (ctl pc) (ctl pc)))
    (s:Stack→List Bool) (xs:List Bool) (hx:s k=xs) :
    Runs program (xs.length+1) (ctl pc) s next (Function.update s k []):=by
  induction xs generalizing s with
  | nil=>simpa only [List.length_nil,Nat.zero_add,List.head?_nil,List.tail_nil,SemiprimeD1StackBytecode.choose]
      using pop_run pc next (ctl pc) (ctl pc) k s [] hc hx
  | cons b xs ih=>
    have h0:=pop_run pc next (ctl pc) (ctl pc) k s (b::xs) hc hx
    have h1:=ih (Function.update s k xs) (Function.update_self _ _ _)
    have hh:=runs_trans program 1 (xs.length+1) (ctl pc) (ctl pc) next s (Function.update s k xs) _
      (by cases b <;> exact h0) h1
    simpa only [Function.update_idem,List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hh
/-- A recursive child has a real pushed return symbol and a real final pop, with all outer frames retained. -/
theorem recursive_call (pc next:Control) (s out:Stack→List Bool) (t:Nat)
    (hc:program (ctl pc)=.call (ctl .visit) (ctl next))
    (hr:Runs program t (ctl .visit) s (ctl .returning) out) :
    Runs program (t+2) (ctl pc) s (ctl next) out:=by
  intro frames target h
  rcases h with ⟨hp,hd,hf⟩
  let mid:=C.execute (.call (ctl .visit) (ctl next)) target
  have hm:C.run program 1 target=some mid:=by
    change SemiprimeD1StackCalls.step program target=some mid
    simp only [SemiprimeD1StackCalls.step,hp,Option.map_some,hc,mid]
  obtain ⟨finish,hRun,hAt⟩:=hr ((ctl next)::frames) mid (by
    simp only [At,mid,C.execute,hd,hf,and_self])
  let last:=C.execute .ret finish
  have hl:C.run program 1 finish=some last:=by
    change SemiprimeD1StackCalls.step program finish=some last
    simp only [SemiprimeD1StackCalls.step,hAt.1,Option.map_some,program,last]
  refine ⟨last,?_,?_,?_,?_⟩
  · rw [show t+2=1+(t+1) by omega,SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hRun,Option.bind_some]
    exact hl
  · simp only [last,C.execute,hAt.2.2]
  · simpa only [last,C.execute,hAt.2.2] using hAt.2.1
  · simp only [last,C.execute,hAt.2.2]
end RiemannGaussian.SemiprimeD1StackWeightedModePrimitives
