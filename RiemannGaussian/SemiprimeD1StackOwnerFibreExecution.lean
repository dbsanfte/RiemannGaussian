/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerFibreEmit
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1StackOwnerFibreExecution
open SemiprimeD1StackOwnerFibre SemiprimeD1StackOwnerFibreComponents SemiprimeD1StackProcedureTrace
open SemiprimeD1StackOwnerFibreEmit (emit_run final_tag_run final_reverse_call)
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeBitArithmetic (bitValue)
theorem chain {m n:ℕ} {pc mid next:Label} {input middle output:Stack→List Bool}
    (h:Runs program m pc input mid middle) (g:Runs program n mid middle next output) :
    Runs program (m+n) pc input next output := runs_trans program _ _ _ _ _ _ _ _ h g
/-- Real row tag consumption. -/
theorem tag_run (query key value reader raw:List Bool) :
    Runs program 1 .loop (data query (true::frame key (frame value reader)) [] [] [] [] [] raw [] [])
      .parseKey (data query (frame key (frame value reader)) [] [] [] [] [] raw [] []) := by
  apply one_base program .loop .parseKey (.pop (.inr .reader) .finishTag .finishTag .parseKey) _ _ rfl
  · rfl
  · funext k;rcases k with k|k <;> cases k <;> rfl
/-- Actual parser validity is consumed. -/
theorem parsed_key_run (query key reader raw:List Bool) :
    Runs program 1 .parsedKey (data query reader key [] [] [true] [] raw [] [])
      .copyKey (data query reader key [] [] [] [] raw [] []) := by
  apply one_base program .parsedKey .copyKey (.pop (.inr .valid) .abort .abort .copyKey) _ _ rfl
  · rfl
  · funext k;rcases k with k|k <;> cases k <;> rfl
/-- Only the computed physical equality byte selects payload destination. -/
theorem matched_run (same:Bool) (query reader raw:List Bool) :
    Runs program 1 .matched (data query reader [] [] [same] [] [] raw [] [])
      (.parseValue same) (data query reader [] [] [] [] [] raw [] []) := by
  apply one_base program .matched (.parseValue same)
    (.pop (.inl .output) .abort (.parseValue false) (.parseValue true)) _ _ rfl
  · cases same <;> rfl
  · funext k;rcases k with k|k <;> cases k <;> rfl
/-- Owner payload parsing also consumes its own physical validity cell. -/
theorem parsed_value_run (same:Bool) (query reader value raw:List Bool) :
    Runs program 1 (.parsedValue same)
      (data query reader [] [] [] [true] value raw [] [])
      (if same then .emitTag else .clear)
      (data query reader [] [] [] [] value raw [] []) := by
  apply one_base program (.parsedValue same) (if same then .emitTag else .clear)
    (.pop (.inr .valid) .abort .abort (if same then .emitTag else .clear)) _ _ rfl
  · rfl
  · funext k;rcases k with k|k <;> cases k <;> rfl
/-- Failed row payloads are actually erased, including their EOF read. -/
theorem clear_run (query reader value raw:List Bool) :
    Runs program (value.length+1) .clear (data query reader [] [] [] [] value raw [] [])
      .loop (data query reader [] [] [] [] [] raw [] []) := by
  induction value with
  | nil=>
    apply one_base program .clear .loop (.pop (.inr .payload) .loop .clear .clear) _ _ rfl
    · rfl
    · funext k;rcases k with k|k <;> cases k <;> rfl
  | cons b value ih=>
    have hs:Runs program 1 .clear (data query reader [] [] [] [] (b::value) raw [] [])
        .clear (data query reader [] [] [] [] value raw [] []) := by
      apply one_base program .clear .clear (.pop (.inr .payload) .loop .clear .clear) _ _ rfl
      · cases b <;> rfl
      · funext k;rcases k with k|k <;> cases k <;> rfl
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using chain hs ih
/-- Nil-vector terminator consumption, with its exact unread suffix. -/
theorem finish_run (query tail raw:List Bool) :
    Runs program 1 .loop (data query (false::tail) [] [] [] [] [] raw [] [])
      .finishTag (data query tail [] [] [] [] [] raw [] []) := by
  apply one_base program .loop .finishTag (.pop (.inr .reader) .finishTag .finishTag .parseKey) _ _ rfl
  · rfl
  · funext k;rcases k with k|k <;> cases k <;> rfl
/-- Both actual field parsers, actual query copy, actual numeric comparison. -/
theorem row_run (query key value reader raw:List Bool) :
    let same:=decide (bitValue key=bitValue query)
    Runs program (8*key.length+5*query.length+8*value.length+
      SemiprimeD1StackWordEqualExecution.executionTime key query+23) .loop
      (data query (true::frame key (frame value reader)) [] [] [] [] [] raw [] [])
      (if same then .emitTag else .clear)
      (data query reader [] [] [] [] value raw [] []) := by
  dsimp only
  let same:=decide (bitValue key=bitValue query)
  have h0:=tag_run query key value reader raw
  have h1:=key_call query key (frame value reader) raw
  have h2:=parsed_key_run query key (frame value reader) raw
  have h3:=copy_call query (frame value reader) key raw
  have h4:=equal_call query (frame value reader) key raw
  have h5:=matched_run same query (frame value reader) raw
  have h6:=value_call same query value reader raw
  have h7:=parsed_value_run same query reader value raw
  have h:=chain h0 (chain h1 (chain h2 (chain h3 (chain h4 (chain h5 (chain h6 h7))))))
  have ht:1+((8*key.length+7)+(1+((5*query.length+4)+
      ((SemiprimeD1StackWordEqualExecution.executionTime key query+1)+(1+((8*value.length+7)+1))))))=
      8*key.length+5*query.length+8*value.length+SemiprimeD1StackWordEqualExecution.executionTime key query+23 := by omega
  rw [ht] at h
  exact h
/-- Trace count follows all actual row parses, comparisons, emissions and erases. -/
def loopTime (query:List Bool) : List (List Bool×List Bool)→ℕ
  | []=>1
  | (key,value)::rows=>8*key.length+5*query.length+8*value.length+
    SemiprimeD1StackWordEqualExecution.executionTime key query+23+
    (if bitValue key=bitValue query then 10*value.length+11 else 0)+
    (value.length+1)+loopTime query rows
/-- Exact selected-row concatenation in original factor-major order. -/
theorem selected_cons (query key value:List Bool) (rows:List (List Bool×List Bool)) :
    selected query ((key,value)::rows)=if bitValue key=bitValue query
      then (true::frame value [])++selected query rows else selected query rows := by
  by_cases h:bitValue key=bitValue query
  · simp only [selected,values,h,ite_true,List.foldr_cons,List.cons_append]
    rw [SemiprimeD1StackEdgeCatalogueEmit.frame_append]
  · simp only [selected,values,h,ite_false]
/-- The physical scan consumes EVERY row, preserving the exact selected order. -/
theorem loop_run (query:List Bool) (rows:List (List Bool×List Bool)) (tail raw:List Bool) :
    Runs program (loopTime query rows) .loop (data query (records rows tail) [] [] [] [] [] raw [] [])
      .finishTag (data query tail [] [] [] [] [] ((selected query rows).reverse++raw) [] []) := by
  induction rows generalizing raw with
  | nil=>simpa only [loopTime,records,SemiprimeD1StackOwnerLookup.records,selected,values,List.foldr_nil,List.reverse_nil,List.nil_append] using finish_run query tail raw
  | cons row rows ih=>
    rcases row with ⟨key,value⟩
    have hr:=row_run query key value (records rows tail) raw
    by_cases h:bitValue key=bitValue query
    · simp only [h,decide_true,ite_true] at hr
      have he:=emit_run query (records rows tail) value raw
      have hc:=clear_run query (records rows tail) value ((true::frame value []).reverse++raw)
      have hi:=ih ((true::frame value []).reverse++raw)
      have ht:=chain hr (chain he (chain hc hi))
      have htime:8*key.length+5*query.length+8*value.length+
          SemiprimeD1StackWordEqualExecution.executionTime key query+23+
          ((10*value.length+11)+((value.length+1)+loopTime query rows))=loopTime query ((key,value)::rows) := by
        simp only [loopTime,h,ite_true]
        omega
      rw [htime] at ht
      simpa only [records,SemiprimeD1StackOwnerLookup.records,selected_cons,h,ite_true,List.reverse_append,List.append_assoc] using ht
    · simp only [h,decide_false] at hr
      have hc:=clear_run query (records rows tail) value raw
      have ht:=chain hr (chain hc (ih raw))
      have htime:8*key.length+5*query.length+8*value.length+
          SemiprimeD1StackWordEqualExecution.executionTime key query+23+
          ((value.length+1)+loopTime query rows)=loopTime query ((key,value)::rows) := by
        simp only [loopTime,h,ite_false,Nat.add_zero]
        omega
      rw [htime] at ht
      simpa only [records,SemiprimeD1StackOwnerLookup.records,selected_cons,h,ite_false] using ht
/-- Vector terminator relationship is literal byte equality. -/
theorem selected_vector (query:List Bool) (rows:List (List Bool×List Bool)) :
    selected query rows++[false]=SemiprimeD1TensorTapeCodec.vectorBits (values query rows) := by
  unfold selected
  generalize values query rows=words
  induction words with
  | nil=>rfl
  | cons word words ih=>
    simp only [List.foldr_cons,List.cons_append,SemiprimeD1TensorTapeCodec.vectorBits]
    rw [←SemiprimeD1StackEdgeCatalogueEmit.frame_tail,ih]
/-- Complete actual trace length, including physical final delimiter/reversal/halt. -/
def totalTime (query:List Bool) (rows:List (List Bool×List Bool)) : ℕ :=
  loopTime query rows+2*(selected query rows).length+7
/-- Whole exact fixed-machine execution; no selected fibre is preloaded. -/
theorem source_run (query:List Bool) (rows:List (List Bool×List Bool)) (tail:List Bool) :
    C.run program (totalTime query rows) (initial query (records rows tail))=some (done query rows tail) := by
  have hl:=loop_run query rows tail []
  simp only [List.append_nil] at hl
  have hf:=chain (final_tag_run query tail (selected query rows).reverse)
    (final_reverse_call query tail (false::(selected query rows).reverse))
  have hh:=chain hl hf
  have ht:loopTime query rows+(1+(2*(false::(selected query rows).reverse).length+3))+1=totalTime query rows := by
    simp only [List.length_cons,List.length_reverse,totalTime]
    omega
  have ho:(false::(selected query rows).reverse).reverse=SemiprimeD1TensorTapeCodec.vectorBits (values query rows) := by
    simp only [List.reverse_cons,List.reverse_reverse,selected_vector]
  rw [ho] at hh
  obtain ⟨finish,hr,hout⟩:=hh [] (initial query (records rows tail)) ⟨rfl,rfl,rfl⟩
  have hend:=halt_run program .done rfl (done query rows tail).data [] finish hout
  rw [←ht,SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,hend]
  rfl
end RiemannGaussian.SemiprimeD1StackOwnerFibreExecution
