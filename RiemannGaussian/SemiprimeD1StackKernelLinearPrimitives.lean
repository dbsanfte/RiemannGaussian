/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinear
import RiemannGaussian.SemiprimeD1StackPhysicalLoops
/-! # Exact actual primitive calls for kernel factor acquisition -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearPrimitives
open SemiprimeD1StackKernelLinear SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic SemiprimeBitDivision
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Exact actual fragment concatenation preserves all real outer return frames. -/
theorem join {m n : ℕ} {pc mid next : Label} {before between after : Stack→List Bool}
    (h : Runs program m pc before mid between) (g : Runs program n mid between next after) :
    Runs program (m+n) pc before next after := runs_trans program m n pc mid next before between after h g
/-- Actual preserving copy, including restoration of its borrowed metadata scratch. -/
theorem copy_call (site : Copy) (pc next : Label)
    (hc : program pc=.call (.copy site 0) next)
    (before : Stack→List Bool) (xs ys : List Bool)
    (hx : before (copyStack site 0)=xs) (hy : before (copyStack site 1)=ys)
    (hs : before (copyStack site 2)=[]) :
    Runs program (5*xs.length+4) pc before next (Function.update before (copyStack site 1) (xs++ys)) := by
  let start:=SemiprimeD1StackCopy.state 0 none xs ys []
  let stop:=SemiprimeD1StackCopy.done xs (xs++ys)
  have hi : Link.DataRel (copyStack site) before start.store before := by
    constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update (copyStack site) (copy_injective site) before start.store before hi (1:Fin 3) (xs++ys)
  have he : Function.update start.store 1 (xs++ys)=stop.store := by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program (copyStack site) (Label.copy site) (copy_injective site)
    SemiprimeD1StackCopy.code 0 (fun _ => rfl) pc next hc (5*xs.length+3)
    start stop before _ rfl rfl (SemiprimeD1StackCopy.copy_words xs ys none) hi ho
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
/-- Literal one-bit push, preserving all foreign words and real caller frames. -/
theorem push_run (pc next:Label) (role:Stack) (bit:Bool) (before:Stack→List Bool)
    (hc:program pc=.base (.push role bit next)) :
    Runs program 1 pc before next (Function.update before role (bit::before role)) :=
  one_base program pc next _ before _ hc rfl rfl
/-- Literal physical head pop, including the actual empty branch. -/
theorem pop_run (pc empty low high:Label) (role:Stack) (before:Stack→List Bool) (word:List Bool)
    (hc:program pc=.base (.pop role empty low high)) (hw:before role=word) :
    Runs program 1 pc before (SemiprimeD1StackBytecode.choose empty low high word.head?)
      (Function.update before role word.tail) :=by
  apply one_base program pc _ _ before _ hc
  · simp only [SemiprimeD1StackBytecode.execute,hw]
  · simp only [SemiprimeD1StackBytecode.execute,hw]
/-- Actual cleanup visits every payload bit and its final EOF branch. -/
theorem drain_trace (role:Stack) (before:Stack→List Bool) (word:List Bool) (hw:before role=word) :
    Runs program (word.length+1) (.drain role) before (.local .returning) (Function.update before role []) :=by
  have h:=SemiprimeD1StackPhysicalLoops.drain program (.drain role) (.local .returning) role rfl before word
  have he:Function.update before role word=before:=by rw [←hw];exact Function.update_eq_self _ _
  rw [he] at h
  exact h
/-- Both actual call/return instructions are included in private cleanup cost. -/
theorem drain_call (pc next:Label) (role:Stack) (before:Stack→List Bool) (word:List Bool)
    (hc:program pc=.call (.drain role) next) (hw:before role=word) :
    Runs program (word.length+3) pc before next (Function.update before role []) :=by
  exact local_call pc (.drain role) (.local .returning) next hc rfl _ before _ (drain_trace role before word hw)
/-- Complete physical view, separating only actual fixed allocated fields. -/
def view (ar:A.Stack→List Bool) (dr:SemiprimeD1StackDivider.Aux→List Bool) (u:Aux→List Bool) : Stack→List Bool
  | .inl (.inl r)=>ar r | .inl (.inr r)=>dr r | .inr r=>u r
/-- Actual addition time, including physical caller return. -/
def addTime (xs ys:List Bool):Nat:=3*(max xs.length ys.length+1)+2*(addBits xs ys false).bits.length+3
/-- Complete real adder, with all twenty-five foreign roles retained. -/
theorem add_call (pc next:Label) (hc:program pc=.call (.add (.start false)) next)
    (dr:SemiprimeD1StackDivider.Aux→List Bool) (u:Aux→List Bool) (xs ys:List Bool) :
    Runs program (addTime xs ys) pc (view (SemiprimeD1StackAdder.store xs ys [] []) dr u) next
      (view (SemiprimeD1StackAdder.store [] [] [] (addBits xs ys false).bits) dr u) :=by
  let source:=SemiprimeD1StackAdder.state (some (.start false)) none xs ys [] []
  let stop:=SemiprimeD1StackAdder.state none none [] [] [] (addBits xs ys false).bits
  have hi:Link.DataRel arithmetic (view source.store dr u) source.store (view source.store dr u):=⟨fun _=>rfl,fun _ _=>rfl⟩
  have ho:Link.DataRel arithmetic (view source.store dr u) stop.store (view stop.store dr u):=by
    constructor
    · intro r;rfl
    · intro r hr
      rcases r with r|r
      · rcases r with r|r
        · exact False.elim (hr r rfl)
        · rfl
      · rfl
  exact included_call program arithmetic Label.add arithmetic_injective A.code (.start false) (fun _=>rfl)
    pc next hc _ source stop _ _ rfl rfl (SemiprimeD1StackAdderExecution.source_run xs ys false) hi ho
/-- Actual complete subtractor cost, including its caller return. -/
def subTime (xs ys:List Bool):Nat:=3*(max xs.length ys.length+1)+2*(subBits xs ys false).result.bits.length+4
/-- Complete real subtraction returns borrow::difference, retaining every foreign role. -/
theorem sub_call (pc next:Label) (hc:program pc=.call (.subtract (.start false)) next)
    (dr:SemiprimeD1StackDivider.Aux→List Bool) (u:Aux→List Bool) (xs ys:List Bool) :
    Runs program (subTime xs ys) pc (view (SemiprimeD1StackAdder.store xs ys [] []) dr u) next
      (view (SemiprimeD1StackAdder.store [] [] [] ((subBits xs ys false).borrow::(subBits xs ys false).result.bits)) dr u) :=by
  let source:=SemiprimeD1StackSubtractor.state (some (.start false)) none xs ys [] []
  let stop:=SemiprimeD1StackSubtractor.state none none [] [] [] ((subBits xs ys false).borrow::(subBits xs ys false).result.bits)
  have hi:Link.DataRel arithmetic (view source.store dr u) source.store (view source.store dr u):=⟨fun _=>rfl,fun _ _=>rfl⟩
  have ho:Link.DataRel arithmetic (view source.store dr u) stop.store (view stop.store dr u):=by
    constructor
    · intro r;rfl
    · intro r hr
      rcases r with r|r
      · rcases r with r|r
        · exact False.elim (hr r rfl)
        · rfl
      · rfl
  exact included_call program arithmetic Label.subtract arithmetic_injective S.code (.start false) (fun _=>rfl)
    pc next hc _ source stop _ _ rfl rfl (SemiprimeD1StackSubtractorExecution.source_run xs ys false) hi ho
end RiemannGaussian.SemiprimeD1StackKernelLinearPrimitives
