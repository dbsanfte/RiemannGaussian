/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerLookupComponents
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1StackOwnerLookupExecution
open SemiprimeD1StackOwnerLookup SemiprimeD1StackOwnerLookupComponents SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeBitArithmetic (bitValue)
theorem chain {m n:ℕ} {pc mid next:Label} {input middle output:Stack→List Bool}
    (h:Runs program m pc input mid middle) (g:Runs program n mid middle next output) :
    Runs program (m+n) pc input next output := runs_trans program _ _ _ _ _ _ _ _ h g
/-- Real row tag consumption. -/
theorem tag_run (query key value reader:List Bool) :
    Runs program 1 .loop (data query (true::frame key (frame value reader)) [] [] [] [] [] [])
      .parseKey (data query (frame key (frame value reader)) [] [] [] [] [] []) := by
  apply one_base program .loop .parseKey (.pop (.inr .reader) .done .done .parseKey) _ _ rfl
  · rfl
  · funext k;rcases k with k|k <;> cases k <;> rfl
/-- Actual parser validity is consumed. -/
theorem parsed_key_run (query key reader:List Bool) :
    Runs program 1 .parsedKey (data query reader key [] [] [true] [] [])
      .copyKey (data query reader key [] [] [] [] []) := by
  apply one_base program .parsedKey .copyKey (.pop (.inr .valid) .abort .abort .copyKey) _ _ rfl
  · rfl
  · funext k;rcases k with k|k <;> cases k <;> rfl
/-- Only the computed physical equality byte selects payload destination. -/
theorem matched_run (same:Bool) (query reader:List Bool) :
    Runs program 1 .matched (data query reader [] [] [same] [] [] [])
      (.parseValue same) (data query reader [] [] [] [] [] []) := by
  apply one_base program .matched (.parseValue same)
    (.pop (.inl .output) .abort (.parseValue false) (.parseValue true)) _ _ rfl
  · cases same <;> rfl
  · funext k;rcases k with k|k <;> cases k <;> rfl
/-- Owner payload parsing also consumes its own physical validity cell. -/
theorem parsed_value_run (same:Bool) (query reader value:List Bool) :
    Runs program 1 (.parsedValue same)
      (data query reader [] [] [] [true] (if same then [] else value) (if same then value else []))
      (if same then .done else .clear)
      (data query reader [] [] [] [] (if same then [] else value) (if same then value else [])) := by
  apply one_base program (.parsedValue same) (if same then .done else .clear)
    (.pop (.inr .valid) .abort .abort (if same then .done else .clear)) _ _ rfl
  · rfl
  · funext k;rcases k with k|k <;> cases k <;> rfl
/-- Failed row payloads are actually erased, including their EOF read. -/
theorem clear_run (query reader value:List Bool) :
    Runs program (value.length+1) .clear (data query reader [] [] [] [] value [])
      .loop (data query reader [] [] [] [] [] []) := by
  induction value with
  | nil=>
    apply one_base program .clear .loop (.pop (.inr .discard) .loop .clear .clear) _ _ rfl
    · rfl
    · funext k;rcases k with k|k <;> cases k <;> rfl
  | cons b value ih=>
    have hs:Runs program 1 .clear (data query reader [] [] [] [] (b::value) [])
        .clear (data query reader [] [] [] [] value []) := by
      apply one_base program .clear .clear (.pop (.inr .discard) .loop .clear .clear) _ _ rfl
      · cases b <;> rfl
      · funext k;rcases k with k|k <;> cases k <;> rfl
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using chain hs ih
/-- Nil-vector terminator consumption, with its exact unread suffix. -/
theorem finish_run (query tail:List Bool) :
    Runs program 1 .loop (data query (false::tail) [] [] [] [] [] [])
      .done (data query tail [] [] [] [] [] []) := by
  apply one_base program .loop .done (.pop (.inr .reader) .done .done .parseKey) _ _ rfl
  · rfl
  · funext k;rcases k with k|k <;> cases k <;> rfl
/-- Both actual field parsers, actual query copy, actual numeric comparison. -/
theorem row_run (query key value reader:List Bool) :
    let same:=decide (bitValue key=bitValue query)
    Runs program (8*key.length+5*query.length+8*value.length+
      SemiprimeD1StackWordEqualExecution.executionTime key query+23) .loop
      (data query (true::frame key (frame value reader)) [] [] [] [] [] [])
      (if same then .done else .clear)
      (data query reader [] [] [] [] (if same then [] else value) (if same then value else [])) := by
  dsimp only
  let same:=decide (bitValue key=bitValue query)
  have h0:=tag_run query key value reader
  have h1:=key_call query key (frame value reader)
  have h2:=parsed_key_run query key (frame value reader)
  have h3:=copy_call query (frame value reader) key
  have h4:=equal_call query (frame value reader) key
  have h5:=matched_run same query (frame value reader)
  have h6:=value_call same query value reader
  have h7:=parsed_value_run same query reader value
  have h:=chain h0 (chain h1 (chain h2 (chain h3 (chain h4 (chain h5 (chain h6 h7))))))
  have ht:1+((8*key.length+7)+(1+((5*query.length+4)+
      ((SemiprimeD1StackWordEqualExecution.executionTime key query+1)+(1+((8*value.length+7)+1))))))=
      8*key.length+5*query.length+8*value.length+SemiprimeD1StackWordEqualExecution.executionTime key query+23 := by omega
  rw [ht] at h
  exact h
/-- Trace length follows actual comparison branches; it is never an input. -/
def loopTime (query:List Bool) : List (List Bool×List Bool)→ℕ
  | []=>1
  | (key,value)::rows=>8*key.length+5*query.length+8*value.length+
    SemiprimeD1StackWordEqualExecution.executionTime key query+23+
      if bitValue key=bitValue query then 0 else value.length+1+loopTime query rows
/-- Whole SAME-program physical lookup, including each failed payload erase. -/
theorem loop_run (query:List Bool) (rows:List (List Bool×List Bool)) (tail:List Bool) :
    Runs program (loopTime query rows) .loop (data query (records rows tail) [] [] [] [] [] [])
      .done (data query (result query rows tail).2 [] [] [] [] [] (result query rows tail).1) := by
  induction rows with
  | nil=>exact finish_run query tail
  | cons row rows ih=>
    rcases row with ⟨key,value⟩
    have hr:=row_run query key value (records rows tail)
    by_cases h:bitValue key=bitValue query
    · simpa only [h,decide_true,ite_true,loopTime,Nat.add_zero,result,records] using hr
    · have hc:=clear_run query (records rows tail) value
      simp only [h,decide_false] at hr
      have ht:=chain hr (chain hc ih)
      simpa only [loopTime,h,ite_false,result,records] using ht
/-- Complete exact execution also includes its literal final halt. -/
theorem source_run (query:List Bool) (rows:List (List Bool×List Bool)) (tail:List Bool) :
    C.run program (loopTime query rows+1) (initial query (records rows tail))=some (done query rows tail) := by
  obtain ⟨finish,hfinish,hout⟩:=loop_run query rows tail [] (initial query (records rows tail)) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (done query rows tail).data [] finish hout
  rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
  rfl
end RiemannGaussian.SemiprimeD1StackOwnerLookupExecution
