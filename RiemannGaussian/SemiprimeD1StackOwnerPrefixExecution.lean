/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerPrefixComponents
/-! # Complete literal original-record scan, including duplicate conflicts -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1StackOwnerPrefixExecution
open SemiprimeD1StackOwnerPrefix SemiprimeD1StackOwnerPrefixComponents SemiprimeD1StackProcedureTrace
open SemiprimeD1OwnerPrefixBits (records scan)
open SemiprimeSourceHistogramKeyBits (frame)

/-- Actual fragment composition within the same literal source. -/
theorem chain {m n : ℕ} {pc mid next : Label} {input middle output : Stack→List Bool}
    (h : Runs program m pc input mid middle) (g : Runs program n mid middle next output) :
    Runs program (m+n) pc input next output := runs_trans program _ _ _ _ _ _ _ _ h g
/-- A real record tag is consumed before the physical parser is entered. -/
theorem tag_run (low high : Bool) (query key : List Bool) (value : Bool) (reader : List Bool) :
    Runs program 1 (.loop low high) (data query (true::frame key (value::reader)) [] [] [] [] [])
      (.parse low high) (data query (frame key (value::reader)) [] [] [] [] []) := by
  apply one_base program (.loop low high) (.parse low high)
    (.pop (.inr .reader) (.high low high) (.high low high) (.parse low high)) _ _ rfl
  · rfl
  · funext k;rcases k with k|k <;> cases k <;> rfl
/-- The real parser's true-valid byte is read and physically cleared. -/
theorem parsed_run (low high : Bool) (query key reader : List Bool) :
    Runs program 1 (.parsed low high) (data query reader key [] [] [true] [])
      (.copyKey low high) (data query reader key [] [] [] []) := by
  apply one_base program (.parsed low high) (.copyKey low high)
    (.pop (.inr .valid) .abort .abort (.copyKey low high)) _ _ rfl
  · rfl
  · funext k;rcases k with k|k <;> cases k <;> rfl
/-- Only the actual numeric equality output selects the value-read branch. -/
theorem matched_run (low high same : Bool) (query reader : List Bool) :
    Runs program 1 (.matched low high) (data query reader [] [] [same] [] [])
      (.value low high same) (data query reader [] [] [] [] []) := by
  apply one_base program (.matched low high) (.value low high same)
    (.pop (.inl .output) .abort (.value low high false) (.value low high true)) _ _ rfl
  · cases same <;> rfl
  · funext k;rcases k with k|k <;> cases k <;> rfl
/-- One literal original value read updates the two COMPUTED finite flags. -/
theorem value_run (low high same value : Bool) (query reader : List Bool) :
    Runs program 1 (.value low high same) (data query (value::reader) [] [] [] [] [])
      (.loop (low && !(same && value)) (high && !(same && !value)))
      (data query reader [] [] [] [] []) := by
  apply one_base program (.value low high same)
    (.loop (low && !(same && value)) (high && !(same && !value)))
    (.pop (.inr .reader) .abort (.loop low (high && !same)) (.loop (low && !same) high)) _ _ rfl
  · cases value <;> cases same <;> cases low <;> cases high <;> rfl
  · funext k;rcases k with k|k <;> cases k <;> rfl
/-- The final physical record tag and BOTH actual answer pushes are paid. -/
theorem finish_run (low high : Bool) (query tail : List Bool) :
    Runs program 3 (.loop low high) (data query (false::tail) [] [] [] [] [])
      .done (data query tail [] [] [] [] [low,high]) := by
  have h0 : Runs program 1 (.loop low high) (data query (false::tail) [] [] [] [] [])
      (.high low high) (data query tail [] [] [] [] []) := by
    apply one_base program (.loop low high) (.high low high)
      (.pop (.inr .reader) (.high low high) (.high low high) (.parse low high)) _ _ rfl
    · rfl
    · funext k;rcases k with k|k <;> cases k <;> rfl
  have h1 : Runs program 1 (.high low high) (data query tail [] [] [] [] [])
      (.low low) (data query tail [] [] [] [] [high]) := by
    apply one_base program (.high low high) (.low low) (.push (.inr .output) high (.low low)) _ _ rfl
    · rfl
    · funext k;rcases k with k|k <;> cases k <;> rfl
  have h2 : Runs program 1 (.low low) (data query tail [] [] [] [] [high])
      .done (data query tail [] [] [] [] [low,high]) := by
    apply one_base program (.low low) .done (.push (.inr .output) low .done) _ _ rfl
    · rfl
    · funext k;rcases k with k|k <;> cases k <;> rfl
  exact chain h0 (chain h1 h2)
/-- Exact SAME-source loop count, never a control operand or an input clock. -/
def loopTime (query : List Bool) : List (List Bool×Bool)→ℕ
  | []=>3
  | (key,_)::rows=>8*key.length+5*query.length+
      SemiprimeD1StackWordEqualExecution.executionTime key query+16+loopTime query rows
/-- Whole actual scanner physically visits EVERY original record exactly once.
It preserves its query, arbitrary post-terminator bytes and all outer frames. -/
theorem loop_run (query : List Bool) (rows : List (List Bool×Bool))
    (tail : List Bool) (low high : Bool) :
    Runs program (loopTime query rows) (.loop low high) (data query (records rows tail) [] [] [] [] [])
      .done (data query tail [] [] [] [] [(scan query rows low high).1,(scan query rows low high).2]) := by
  induction rows generalizing low high with
  | nil=>exact finish_run low high query tail
  | cons row rows ih=>
    rcases row with ⟨key,value⟩
    let same:=decide (SemiprimeBitArithmetic.bitValue key=SemiprimeBitArithmetic.bitValue query)
    have h0:=tag_run low high query key value (records rows tail)
    have h1:=field_call low high query key (value::records rows tail)
    have h2:=parsed_run low high query key (value::records rows tail)
    have h3:=copy_call low high query (value::records rows tail) key
    have h4:=equal_call low high query (value::records rows tail) key
    have h5:=matched_run low high same query (value::records rows tail)
    have h6:=value_run low high same value query (records rows tail)
    have h7:=ih (low && !(same && value)) (high && !(same && !value))
    have h:=chain h0 (chain h1 (chain h2 (chain h3 (chain h4 (chain h5 (chain h6 h7))))))
    have ht : 1+((8*key.length+7)+(1+((5*query.length+4)+
        ((SemiprimeD1StackWordEqualExecution.executionTime key query+1)+(1+(1+loopTime query rows))))))=
        loopTime query ((key,value)::rows) := by
      change _=8*key.length+5*query.length+SemiprimeD1StackWordEqualExecution.executionTime key query+16+loopTime query rows
      omega
    rw [ht] at h
    exact h
/-- Complete exact trace includes the real halt and every physical parser call. -/
theorem source_run (query : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool) :
    C.run program (loopTime query rows+1) (initial query (records rows tail))=some (done query rows tail) := by
  obtain ⟨finish,hfinish,hout⟩:=loop_run query rows tail true true []
    (initial query (records rows tail)) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (done query rows tail).data [] finish hout
  rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
  rfl
end RiemannGaussian.SemiprimeD1StackOwnerPrefixExecution
