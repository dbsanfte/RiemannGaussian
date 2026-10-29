/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildVertexChoiceView
/-! # Actual activity pop, whole source call/return and enclosing true halt -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildVertexChoiceExecution
open SemiprimeD1StackChildVertexChoice SemiprimeD1StackChildVertexChoiceView
open SemiprimeD1StackProcedureTrace
/-- The actual bit chooses the literal call site; no native activation predicate executes. -/
def branch (bit : Bool) : Control:=if bit then .active else .inactive
/-- Entire stopped169-word bank, with real flags and returns empty. -/
def stopped (data : Stack→List Bool) : C.State Stack Label:=⟨none,none,none,data,[]⟩
/-- Literal singleton activity consumption, valid for arbitrary transient flags/outer frames. -/
theorem pop_run (a : A.Stack→List Bool) (bit : Bool) :
    Runs program 1 (.local .start) (bank a (fun _=>[]) [bit])
      (.local (branch bit)) (activeResult a) := by
  apply one_base program (.local .start) (.local (branch bit))
    (.pop activity (.local .abort) (.local .inactive) (.local .active)) _ _ rfl
  · cases bit <;> rfl
  · exact pop_activity a bit
/-- Every nested active call and real return is retained, including arbitrary enclosing returns. -/
theorem active_call (time : ℕ) (source out : C.State A.Stack A.Label)
    (hentry : source.pc=some (.local .start)) (hstart : source.frames=[])
    (hstop : out.pc=none) (hframes : out.frames=[])
    (hr : SemiprimeD1StackCalls.run A.program time source=some out) :
    Runs program (time+1) (.local .active) (activeResult source.data)
      (.local .done) (activeResult out.data) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program active Label.active active_injective
    A.program (.local .start) (fun _=>rfl) (.local .active) (.local .done) rfl
    time source out _ _ hentry hstart hstop hframes hr
  · exact active_rel source.data source.data
  · exact active_rel source.data out.data
/-- The inactive whole call changes exactly its32-role image; all other active words and shadows survive. -/
theorem inactive_call (a : A.Stack→List Bool) (time : ℕ) (source out : C.State U.Stack U.Label)
    (hin : ∀k,activeResult a (inactive k)=source.data k)
    (hentry : source.pc=some (.local .start)) (hstart : source.frames=[])
    (hstop : out.pc=none) (hframes : out.frames=[])
    (hr : SemiprimeD1StackCalls.run U.program time source=some out) :
    Runs program (time+1) (.local .inactive) (activeResult a)
      (.local .done) (inactiveResult a out.data) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program inactive Label.inactive inactive_injective
    U.program (.local .start) (fun _=>rfl) (.local .inactive) (.local .done) rfl
    time source out _ _ hentry hstart hstop hframes hr
  · exact ⟨hin,fun _ _=>rfl⟩
  · exact inactive_rel a out.data
/-- A complete caller run pays its literal pop, actual call, source trace and true halt. -/
theorem finish_run (a : A.Stack→List Bool) (bit : Bool) (time : ℕ) (data : Stack→List Bool)
    (h : Runs program (time+1) (.local (branch bit)) (activeResult a) (.local .done) data) :
    SemiprimeD1StackCalls.run program (time+3)
      (⟨some (.local .start),none,none,bank a (fun _=>[]) [bit],[]⟩ : C.State Stack Label)=
      some (stopped data) := by
  have ht:=runs_trans program _ _ _ _ _ _ _ _ (pop_run a bit) h
  obtain ⟨out,hr,ha⟩:=ht [] ⟨some (.local .start),none,none,bank a (fun _=>[]) [bit],[]⟩ ⟨rfl,rfl,rfl⟩
  have he : time+3=(1+(time+1))+1:=by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
  exact halt_run program (.local .done) rfl data [] out ha
/-- Whole eight-word active entry through its actual enclosing halt. -/
theorem active_run (parent order oldAxes oldp axes precision scope : List Bool)
    (time : ℕ) (out : C.State A.Stack A.Label) (hstop : out.pc=none) (hframes : out.frames=[])
    (hr : SemiprimeD1StackCalls.run A.program time
      (A.initial parent order oldAxes oldp axes precision scope)=some out) :
    SemiprimeD1StackCalls.run program (time+3)
      (initial parent order oldAxes oldp axes precision scope [true])=
      some (stopped (activeResult out.data)) :=
  finish_run _ true time _ (active_call time _ out rfl rfl hstop hframes hr)
/-- Whole eight-word inactive entry; only new headers feed the actual unit constructor. -/
theorem inactive_run (parent order oldAxes oldp axes precision scope : List Bool)
    (time : ℕ) (out : C.State U.Stack U.Label) (hstop : out.pc=none) (hframes : out.frames=[])
    (hr : SemiprimeD1StackCalls.run U.program time
      (SemiprimeD1StackChildUnitVertex.initial axes precision)=some out) :
    SemiprimeD1StackCalls.run program (time+3)
      (initial parent order oldAxes oldp axes precision scope [false])=
      some (stopped (inactiveResult (A.initial parent order oldAxes oldp axes precision scope).data out.data)) :=
  finish_run _ false time _ (inactive_call _ time _ out
    (inactive_initial parent order oldAxes oldp axes precision scope) rfl rfl hstop hframes hr)
end RiemannGaussian.SemiprimeD1StackChildVertexChoiceExecution
