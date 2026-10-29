/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprLiteral

/-! # Actual encoded literal evaluation and reusable physical base case
Both parser and fitter are literally included. Their outputs and validity bit
are consequences of their executed traces, never premises supplied by a caller.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackExprLiteralExecution
open SemiprimeD1StackExprLiteral SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)

/-- Actual pre-parser data, still containing the framed literal payload. -/
def beforeField (word tail cached : List Bool) : Stack→List Bool := input (frame word tail) cached
/-- Reached data after the physical parser has computed its true validity bit. -/
def parsed (word tail cached : List Bool) : Stack→List Bool :=
  store tail (Fit.store word cached [] [] []) [true]
/-- Actual parser flag has been consumed before the fitter call. -/
def beforeFit (word tail cached : List Bool) : Stack→List Bool :=
  store tail (Fit.store word cached [] [] []) []
/-- Exact final physical syntax suffix, template cache and literal output. -/
def finalData (word tail cached : List Bool) : Stack→List Bool :=
  store tail (Fit.store [] cached [] [] (SemiprimeD1StackWordFitExecution.result word cached)) []
/-- Clean terminal source state, retaining the real code suffix and cache. -/
def done (word tail cached : List Bool) : C.State Stack Label :=
  ⟨none,none,none,finalData word tail cached,[]⟩

/-- Both literal constructor tags are actually read, not inferred from a supplied AST. -/
theorem tags_run (word tail cached : List Bool) :
    Runs program 2 (ctl .start)
      (input (SemiprimeD1StackExprCodec.encode (.literal word) tail) cached)
      (ctl .fieldCall) (beforeField word tail cached) := by
  have h0 : Runs program 1 (ctl .start)
      (input (false::false::frame word tail) cached) (ctl .secondTag)
      (input (false::frame word tail) cached) := by
    apply one_base program (ctl .start) (ctl .secondTag)
      (.pop inputCode (ctl .bad) (ctl .secondTag) (ctl .bad)) _ _ rfl
    · rfl
    · funext k
      rcases k with k|k
      · rfl
      · rcases k with k|k <;> cases k <;> rfl
  have h1 : Runs program 1 (ctl .secondTag) (input (false::frame word tail) cached)
      (ctl .fieldCall) (beforeField word tail cached) := by
    apply one_base program (ctl .secondTag) (ctl .fieldCall)
      (.pop inputCode (ctl .bad) (ctl .fieldCall) (ctl .bad)) _ _ rfl
    · rfl
    · funext k
      rcases k with k|k
      · rfl
      · rcases k with k|k <;> cases k <;> rfl
  exact runs_trans program 1 1 _ _ _ _ _ _ h0 h1

/-- The actual field call acquires the payload and flag while preserving the
physical template and entire code suffix. No supplied split or verdict is used. -/
theorem field_call (word tail cached : List Bool) :
    Runs program (8*word.length+7) (ctl .fieldCall) (beforeField word tail cached)
      (ctl .checkValid) (parsed word tail cached) := by
  apply included_call program fieldStack fieldLabel fieldStack_injective Field.code
    (Field.active .tagPop (none,false)) (fun _=>rfl) (ctl .fieldCall) (ctl .checkValid) rfl
    (8*word.length+6) (Field.initial (frame word tail) [])
    (⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word)
      (fun _=>[true])⟩:SemiprimeD1StackBytecode.State Field.Stack Field.Label)
    (beforeField word tail cached) (parsed word tail cached)
  · rfl
  · rfl
  · exact SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []
  · constructor
    · intro k
      rcases k with k|k
      · cases k <;> rfl
      · cases k;rfl
    · intro k _;rfl
  · constructor
    · intro k
      rcases k with k|k
      · cases k <;> rfl
      · cases k;rfl
    · intro k hk
      rcases k with k|k
      · fin_cases k <;> first | rfl | exact False.elim (hk (.inl .output) rfl)
      · rcases k with k|k
        · cases k;exact False.elim (hk (.inl .input) rfl)
        · cases k;exact False.elim (hk (.inr ()) rfl)

/-- The parser's actual true flag is popped before entering arithmetic. -/
theorem check_flag (word tail cached : List Bool) :
    Runs program 1 (ctl .checkValid) (parsed word tail cached)
      (ctl .fitCall) (beforeFit word tail cached) := by
  apply one_base program (ctl .checkValid) (ctl .fitCall)
    (.pop valid (ctl .bad) (ctl .bad) (ctl .fitCall)) _ _ rfl
  · rfl
  · funext k
    rcases k with k|k
    · rfl
    · rcases k with k|k <;> cases k <;> rfl

/-- The real nested fitter consumes the acquired payload and preserves every
unmapped suffix/flag cell. Its template is the ACTUAL cached physical word. -/
theorem fit_call (word tail cached : List Bool) :
    Runs program (SemiprimeD1StackWordFitExecution.totalTime word cached+1)
      (ctl .fitCall) (beforeFit word tail cached) (ctl .done) (finalData word tail cached) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Sum.inl fitLabel Sum.inl_injective
    Fit.program .start (fun _=>rfl) (ctl .fitCall) (ctl .done) rfl
    (SemiprimeD1StackWordFitExecution.totalTime word cached) (Fit.initial word cached)
    (SemiprimeD1StackWordFitExecution.done word cached) (beforeFit word tail cached) (finalData word tail cached)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackWordFitExecution.source_run word cached
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact False.elim (hk k rfl)
      · rfl

/-- Reusable literal-body count, with the real final halt included. -/
def readyTime (word cached : List Bool) : ℕ :=
  (8*word.length+7)+1+(SemiprimeD1StackWordFitExecution.totalTime word cached+1)+1
/-- Whole literal count also pays the two original constructor-tag reads. -/
def totalTime (word cached : List Bool) : ℕ := 2+readyTime word cached

/-- Reusable completed literal body for a larger fixed recursive evaluator. -/
theorem ready (word tail cached : List Bool) :
    Runs program ((8*word.length+7)+1+(SemiprimeD1StackWordFitExecution.totalTime word cached+1))
      (ctl .fieldCall) (beforeField word tail cached) (ctl .done) (finalData word tail cached) :=
  runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _ (field_call word tail cached) (check_flag word tail cached))
    (fit_call word tail cached)

/-- Actual balanced source trace from an already-dispatched literal field. This
entry lets the whole evaluator share the original tag-dispatch instructions. -/
theorem ready_run (word tail cached : List Bool) :
    C.run program (readyTime word cached)
      (⟨some (ctl .fieldCall),none,none,beforeField word tail cached,[]⟩:C.State Stack Label)=
      some (done word tail cached) := by
  obtain ⟨finish,hf,ho⟩:=ready word tail cached []
    (⟨some (ctl .fieldCall),none,none,beforeField word tail cached,[]⟩:C.State Stack Label) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (finalData word tail cached) [] finish ho
  rw [readyTime,SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some,hh]
  rfl

/-- The encoded input is physically read to acquire and evaluate its literal.
The AST appears only in the proof-side specification of those supplied bytes. -/
theorem source_run (word tail cached : List Bool) :
    C.run program (totalTime word cached)
      (initial (SemiprimeD1StackExprCodec.encode (.literal word) tail) cached)=some (done word tail cached) := by
  have h:=runs_trans program _ _ _ _ _ _ _ _ (tags_run word tail cached) (ready word tail cached)
  obtain ⟨finish,hf,ho⟩:=h []
    (initial (SemiprimeD1StackExprCodec.encode (.literal word) tail) cached) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (finalData word tail cached) [] finish ho
  rw [totalTime,readyTime,show 2+((8*word.length+7)+1+
      (SemiprimeD1StackWordFitExecution.totalTime word cached+1)+1)=
      (2+((8*word.length+7)+1+(SemiprimeD1StackWordFitExecution.totalTime word cached+1)))+1 by omega,
    SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some,hh]
  rfl

end RiemannGaussian.SemiprimeD1StackExprLiteralExecution
