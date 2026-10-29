/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicCarryState
/-! # Actual fixed carry-pipeline primitive calls
These are exact instruction/subroutine traces on physical stores. They are
proof-only helpers; the closed public entry supplies no payload/result oracle.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicCarryPrimitives
open SemiprimeD1StackPublicCarry SemiprimeD1StackPublicCarryState SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- One actual auxiliary push, including its exact physical store update. -/
theorem push_aux (pc next : Label) (k : Aux) (b : Bool) (hc : program pc=.base (.push (.inr k) b next))
    (context : T.Stack→List Bool) (p : Payload) :
    Runs program 1 pc (view context p) next (view context (set p k (b::get p k))) := by
  apply one_base program pc next (.push (.inr k) b next) _ _ hc
  · rfl
  · rw [view_set];rfl
/-- One actual auxiliary pop selects only its physically read EOF/Boolean value. -/
theorem pop_aux (pc empty low high : Label) (k : Aux)
    (hc : program pc=.base (.pop (.inr k) empty low high)) (context : T.Stack→List Bool) (p : Payload) :
    Runs program 1 pc (view context p)
      (SemiprimeD1StackBytecode.choose empty low high (get p k).head?)
      (view context (set p k (get p k).tail)) := by
  apply one_base program pc _ (.pop (.inr k) empty low high) _ _ hc
  · rfl
  · rw [view_set];rfl
/-- Every cell of a cleared auxiliary role is actually popped. -/
theorem drain_aux (pc next : Label) (k : Aux)
    (hc : program pc=.base (.pop (.inr k) next pc pc)) (context : T.Stack→List Bool) (p : Payload) :
    Runs program ((get p k).length+1) pc (view context p) next (view context (set p k [])) := by
  have h:=SemiprimeD1StackPhysicalLoops.drain program pc next (.inr k) hc (view context p) (get p k)
  have hi : Function.update (view context p) (.inr k) (get p k)=view context p := Function.update_eq_self _ _
  rw [hi,←view_set] at h
  exact h
/-- Actual destination of each fixed preserving-copy purpose. -/
def copyDest : CopyKind→Aux | .bound=>.bound | .operand _=>.blockOut | .guardBound _=>.blockCount
/-- The fixed copy output is always an actual auxiliary role. -/
theorem copyDest_eq (kind : CopyKind) : copyStack kind 1=.inr (copyDest kind) := by cases kind <;> rfl
/-- Actual source word seen by a fixed physical copy; not a runtime getter. -/
def copied (context : T.Stack→List Bool) (p : Payload) (kind : CopyKind) : List Bool :=
  view context p (copyStack kind 0)
/-- Complete actual preserving copy, with its real restoration work and call. -/
theorem copy_call (kind : CopyKind) (pc next : Label) (hc : program pc=.call (.copy kind 0) next)
    (context : T.Stack→List Bool) (p : Payload) (hd : get p (copyDest kind)=[]) (hs : p.scratch=[]) :
    Runs program (5*(copied context p kind).length+4) pc (view context p) next
      (view context (set p (copyDest kind) (copied context p kind))) := by
  let word:=copied context p kind
  have hin : Link.DataRel (copyStack kind) (view context p)
      (SemiprimeD1StackCopy.state 0 none word [] []).store (view context p) := by
    constructor
    · intro k;fin_cases k
      · rfl
      · change view context p (copyStack kind 1)=[]
        rw [copyDest_eq];exact hd
      · exact hs
    · intro k _;rfl
  have hout:=Link.data_update (copyStack kind) (copy_injective kind) _ _ _ hin (1:Fin 3) word
  have he : Function.update (SemiprimeD1StackCopy.state 0 none word [] []).store 1 word=
      (SemiprimeD1StackCopy.done word word).store := by funext k;fin_cases k <;> rfl
  rw [he,copyDest_eq,←view_set] at hout
  apply included_call program (copyStack kind) (Label.copy kind) (copy_injective kind)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc (5*word.length+3)
    (SemiprimeD1StackCopy.state 0 none word [] []) (SemiprimeD1StackCopy.done word word)
    _ _ rfl rfl (by simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words word [] none) hin hout
/-- Actual original word source of a record field, never supplied source truth. -/
def framedWord (context : T.Stack→List Bool) (p : Payload) (field : Fin 4) : List Bool := view context p (frameWord field)
/-- Real Frame call prepends one actual preserved word to the existing record. -/
theorem frame_call (field : Fin 4) (context : T.Stack→List Bool) (p : Payload) (hs : p.scratch=[]) :
    Runs program (6*(framedWord context p field).length+5) (.frame field) (view context p) (afterFrame field)
      (view context (set p .vector (SemiprimeSourceHistogramKeyBits.frame (framedWord context p field) p.vector))) := by
  let word:=framedWord context p field
  let out:=SemiprimeSourceHistogramKeyBits.frame word p.vector
  have hin : Link.DataRel (frameStack field) (view context p)
      (SemiprimeD1StackFrame.state 0 none word p.vector []).store (view context p) := by
    constructor
    · intro k;fin_cases k <;> first | rfl | exact hs
    · intro k _;rfl
  have hout:=Link.data_update (frameStack field) (frame_injective field) _ _ _ hin (1:Fin 3) out
  have he : Function.update (SemiprimeD1StackFrame.state 0 none word p.vector []).store 1 out=
      (SemiprimeD1StackFrame.done word out).store := by funext k;fin_cases k <;> rfl
  rw [he] at hout
  change Link.DataRel (frameStack field) (view context p) (SemiprimeD1StackFrame.done word out).store
    (Function.update (view context p) (.inr .vector) out) at hout
  rw [←view_set] at hout
  apply included_call program (frameStack field) (Label.framer field) (frame_injective field)
    SemiprimeD1StackFrame.code 0 (fun _=>rfl) (.frame field) (afterFrame field) rfl (6*word.length+4)
    (SemiprimeD1StackFrame.state 0 none word p.vector []) (SemiprimeD1StackFrame.done word out)
    _ _ rfl rfl (SemiprimeD1StackFrame.frame_words word p.vector none) hin hout
/-- Complete physical comparator on ACTUAL fresh copies, returning its real bit
and clearing both copies and all comparison work. No ordering result is assumed. -/
theorem less_call (k : Fin 3) (context : T.Stack→List Bool) (p : Payload)
    (hs : p.scratch=[]) (hh : p.history=[]) (hv : p.valid=[]) :
    Runs program (SemiprimeD1StackWordLessExecution.totalTime p.blockOut p.blockCount+1)
      (.compare k) (view context p) (.tested k)
      (view context (set (set (set p .blockOut []) .blockCount []) .valid
        [SemiprimeD1StackWordLessExecution.answer p.blockOut p.blockCount])) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program lessStack Label.less less_injective
    L.program .start (fun _=>rfl) (.compare k) (.tested k) rfl
    (SemiprimeD1StackWordLessExecution.totalTime p.blockOut p.blockCount)
    (L.initial p.blockOut p.blockCount) (SemiprimeD1StackWordLessExecution.done p.blockOut p.blockCount)
    _ _ rfl rfl rfl rfl (SemiprimeD1StackWordLessExecution.source_run p.blockOut p.blockCount)
  · constructor
    · intro j;rcases j with j|j
      · cases j <;> first | rfl | exact hs | exact hh
      · cases j;exact hv
    · intro j _;rfl
  · constructor
    · intro j;rcases j with j|j
      · cases j <;> first | rfl | exact hs | exact hh
      · cases j;rfl
    · intro j hj;rcases j with j|j
      · rfl
      · cases j <;> first | rfl | exact (hj (.inl .left) rfl).elim | exact (hj (.inl .right) rfl).elim | exact (hj (.inr ()) rfl).elim
/-- Actual three word-cache drains on either accepted/rejected branch. -/
theorem clear_words (pass : Bool) (context : T.Stack→List Bool) (p : Payload) :
    Runs program (p.coefficient.length+p.previous.length+p.next.length+3) (.clear pass 0) (view context p)
      (if pass then .equation else .done)
      (view context (set (set (set p .coefficient []) .previous []) .next [])) := by
  have h0:=drain_aux (.clear pass 0) (.clear pass 1) .coefficient rfl context p
  have h1:=drain_aux (.clear pass 1) (.clear pass 2) .previous rfl context (set p .coefficient [])
  have h2:=drain_aux (.clear pass 2) (if pass then .equation else .done) .next rfl context (set (set p .coefficient []) .previous [])
  have h:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
  have ht : (p.coefficient.length+1)+(p.previous.length+1)+(p.next.length+1)=
      p.coefficient.length+p.previous.length+p.next.length+3 := by omega
  simpa only [SemiprimeD1StackPublicCarryState.get,SemiprimeD1StackPublicCarryState.set,ht] using h
end RiemannGaussian.SemiprimeD1StackPublicCarryPrimitives
