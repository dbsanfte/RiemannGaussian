/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactory
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryWiringFacts
/-! # Actual generic source fragments for the complete child factory
Generic physical banks and label parameters keep native graphs and input
metadata opaque. Every clock below belongs to the actual literal procedure.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryWiringFacts
open SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Exact chronological composition preserves all real outer returns. -/
theorem join {m n:Nat} {pc mid next:Label} {before between after:Stack→List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between next after):
    Runs program (m+n) pc before next after:=runs_trans program m n pc mid next before between after h g
/-- A genuine preserving copy includes both restoration loops and its real return. -/
theorem copy_call (site:Fin 38) (pc next:Label)
    (hc:program pc=.call (.copy site 0) next) (before:Stack→List Bool) (xs ys:List Bool)
    (hx:before (copyStack site 0)=xs) (hy:before (copyStack site 1)=ys) (hs:before (copyStack site 2)=[]):
    Runs program (5*xs.length+4) pc before next (Function.update before (copyStack site 1) (xs++ys)):=by
  let start:=SemiprimeD1StackCopy.state 0 none xs ys []
  let stop:=SemiprimeD1StackCopy.done xs (xs++ys)
  have hi:Link.DataRel (copyStack site) before start.store before:=by
    constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update (copyStack site) (copy_injective site) before start.store before hi (1:Fin 3) (xs++ys)
  have he:Function.update start.store 1 (xs++ys)=stop.store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program (copyStack site) (Label.copy site) (copy_injective site) SemiprimeD1StackCopy.code 0
    (fun _=>rfl) pc next hc (5*xs.length+3) start stop before _ rfl rfl
    (SemiprimeD1StackCopy.copy_words xs ys none) hi ho
/-- A genuine Frame preserves its source and prepends actual framed bytes. -/
theorem frame_call (site:Fin 25) (pc next:Label)
    (hc:program pc=.call (.frame site 0) next) (before:Stack→List Bool) (word buffer:List Bool)
    (hw:before (frameStack site 0)=word) (hb:before (frameStack site 1)=buffer) (hs:before (frameStack site 2)=[]):
    Runs program (6*word.length+5) pc before next
      (Function.update before (frameStack site 1) (SemiprimeSourceHistogramKeyBits.frame word buffer)):=by
  let start:=SemiprimeD1StackFrame.state 0 none word buffer []
  let stop:=SemiprimeD1StackFrame.done word (SemiprimeSourceHistogramKeyBits.frame word buffer)
  have hi:Link.DataRel (frameStack site) before start.store before:=by
    constructor
    · intro k;fin_cases k
      · exact hw
      · exact hb
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update (frameStack site) (frame_injective site) before start.store before hi (1:Fin 3)
    (SemiprimeSourceHistogramKeyBits.frame word buffer)
  have he:Function.update start.store 1 (SemiprimeSourceHistogramKeyBits.frame word buffer)=stop.store:=by
    funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program (frameStack site) (Label.frame site) (frame_injective site)
    SemiprimeD1StackFrame.code 0 (fun _=>rfl) pc next hc (6*word.length+4) start stop before _ rfl rfl
    (SemiprimeD1StackFrame.frame_words word buffer none) hi ho
/-- Real consuming reversal pays its source bytes and actual return. -/
theorem reverse_call (site:Fin 16) (pc next:Label)
    (hc:program pc=.call (.reverse site 0) next) (before:Stack→List Bool) (xs ys:List Bool)
    (hx:before (reverseStack site 0)=xs) (hy:before (reverseStack site 1)=ys):
    Runs program (2*xs.length+3) pc before next
      (Function.update (Function.update before (reverseStack site 0) []) (reverseStack site 1) (xs.reverse++ys)):=by
  let start:=SemiprimeD1StackReverseWord.state none xs ys
  let stop:=SemiprimeD1StackReverseWord.done (xs.reverse++ys)
  have hi:Link.DataRel (reverseStack site) before start.store before:=by
    constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
    · intro k _;rfl
  have h0:=Link.data_update (reverseStack site) (reverse_injective site) before start.store before hi (0:Fin 2) []
  have h1:=Link.data_update (reverseStack site) (reverse_injective site) before _ _ h0 (1:Fin 2) (xs.reverse++ys)
  have he:Function.update (Function.update start.store 0 []) 1 (xs.reverse++ys)=stop.store:=by funext k;fin_cases k <;> rfl
  rw [he] at h1
  exact included_call program (reverseStack site) (Label.reverse site) (reverse_injective site)
    SemiprimeD1StackReverseWord.code 0 (fun _=>rfl) pc next hc (2*xs.length+2) start stop before _ rfl rfl
    (SemiprimeD1StackReverseWord.reverse_run xs ys none) hi h1
/-- One actual literal push writes only its real Boolean cell. -/
theorem push_run (pc next:Label) (k:Stack) (b:Bool) (before:Stack→List Bool)
    (hc:program pc=.base (.push k b next)):
    Runs program 1 pc before next (Function.update before k (b::before k)):=
  one_base program pc next (.push k b next) before _ hc rfl rfl
/-- One actual literal pop consumes its physical Boolean head. -/
theorem pop_run (pc empty low high:Label) (k:Stack) (before:Stack→List Bool) (xs:List Bool)
    (hc:program pc=.base (.pop k empty low high)) (hx:before k=xs):
    Runs program 1 pc before (SemiprimeD1StackBytecode.choose empty low high xs.head?)
      (Function.update before k xs.tail):=by
  apply one_base program pc _ (.pop k empty low high) before _ hc
  · simp only [SemiprimeD1StackBytecode.execute,hx]
  · simp only [SemiprimeD1StackBytecode.execute,hx]
/-- Real physical EOF peek retains every payload byte. -/
theorem peek_run (pc empty low high:Label) (k:Stack) (before:Stack→List Bool) (xs:List Bool)
    (hc:program pc=.base (.peek k empty low high)) (hx:before k=xs):
    Runs program 1 pc before (SemiprimeD1StackBytecode.choose empty low high xs.head?) before:=by
  apply one_base program pc _ (.peek k empty low high) before before hc
  · simp only [SemiprimeD1StackBytecode.execute,hx]
  · rfl
/-- Real work-word cleanup pays every bit and its final empty pop. -/
theorem drain_loop (pc next:Label) (k:Stack)
    (hc:program pc=.base (.pop k next pc pc)) (before:Stack→List Bool) (xs:List Bool) (hx:before k=xs):
    Runs program (xs.length+1) pc before next (Function.update before k []):=by
  induction xs generalizing before with
  | nil=>exact pop_run pc next pc pc k before [] hc hx
  | cons b xs ih=>
    have h0:=pop_run pc next pc pc k before (b::xs) hc hx
    have h1:=ih (Function.update before k xs) (Function.update_self _ _ _)
    have h:=join (by cases b <;> exact h0) h1
    simpa only [List.length_cons,Function.update_idem,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
/-- One actual static jump preserves the entire physical bank. -/
theorem jump_run (pc next:Label) (before:Stack→List Bool) (hc:program pc=.base (.jump next)):
    Runs program 1 pc before next before:=one_base program pc next (.jump next) before before hc rfl rfl
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryPrimitives
