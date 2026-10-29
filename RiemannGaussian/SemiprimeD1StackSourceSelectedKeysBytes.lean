/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectedKeysLoop
import RiemannGaussian.SemiprimeD1StackSourceIncidenceBytes
/-! # Selected-key source bounds from actual retained cache/tape/output bytes
The imported incidence lemmas concern only literal framing and returned-payload
subword lengths. No previous query clock or original report clock is reused.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectedKeysBytes
open SemiprimeD1StackSourceSelectedKeys SemiprimeD1StackSourceSelectedKeysEncoding
open SemiprimeD1StackSourceSelectedKeysLookup SemiprimeD1StackSourceSelectedKeysLog
open SemiprimeD1StackSourceSelectedKeysBody SemiprimeD1StackSourceSelectedKeysLoop
namespace Env
export SemiprimeD1StackSourceEnvironmentEncoding (dictionary)
end Env
/-- Actual normalized selected-ID bytes occur inside the actual acquired marked dictionary. -/
theorem readID_length (i:Inputs) (key:List Bool) :(readID i.ids key).length ≤ (Env.dictionary i.ids).length :=
  SemiprimeD1StackSourceIncidenceBytes.readID_length i.ids key
/-- Both retained input sources are included in the one actual byte budget. -/
theorem basic_bounds (i:Inputs) :(tape i).length ≤ inputSize i ∧ (Env.dictionary i.ids).length ≤ inputSize i :=by
  unfold inputSize SemiprimeD1StackSourceEnvironmentBounds.cacheSize
  omega
/-- One occurrence is charged by its actual pair tag and both endpoint fields, without an externally supplied count. -/
theorem occurrence_count_le (i:Inputs) :i.rows.length ≤ inputSize i :=by
  have ht:=(basic_bounds i).1
  change (SemiprimeD1StackOwnerLookup.records i.rows []).length ≤ _ at ht
  rw [SemiprimeD1StackOwnerLookupBounds.records_length] at ht
  simp only [List.length_nil,Nat.add_zero] at ht
  omega
/-- Every parsed endpoint width belongs to its physically supplied occurrence tape. -/
theorem endpoint_widths (i:Inputs) (row:List Bool×List Bool) (h:row∈i.rows) :
    row.1.length ≤ inputSize i ∧ row.2.length ≤ inputSize i :=by
  have hr:=SemiprimeD1StackSourceIncidenceBytes.record_width_le row i.rows h
  have ht:=(basic_bounds i).1
  change (SemiprimeD1StackOwnerLookup.records i.rows []).length ≤ _ at ht
  omega
/-- Joint-key width includes its actual single owner-field delimiter and rawfactor-ID tail. -/
theorem joint_length (i:Inputs) (row:List Bool×List Bool) :(joint i.ids row).length ≤ 3*inputSize i+1 :=by
  have h0:=(readID_length i row.1).trans (basic_bounds i).2
  have h1:=(readID_length i row.2).trans (basic_bounds i).2
  unfold joint
  rw [SemiprimeSourceHistogramKeyBits.frame_length]
  omega
/-- Complete vector-row width includes its actual true tag and enclosing fullkey frame. -/
theorem chunk_length (i:Inputs) (row:List Bool×List Bool) :(chunk i.ids row).length ≤ 6*inputSize i+4 :=by
  have h:=joint_length i row
  unfold chunk
  rw [List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
  omega
/-- Full reversed-log size is derived internally from every actual occurrence's physical vector-row bytes. -/
theorem stream_length (i:Inputs) (rows:List (List Bool×List Bool)) :
    (stream i.ids rows).length ≤ rows.length*(6*inputSize i+4) :=by
  induction rows with
  | nil=>simpa only [stream,List.foldr_nil,List.length_nil,Nat.zero_mul] using (Nat.le_refl 0)
  | cons row rows ih=>
    have h:=chunk_length i row
    change (chunk i.ids row++stream i.ids rows).length ≤ _
    rw [List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
/-- Each real preserving lookup/copy/ID-save/drain stage has its own input-byte quadratic clock. -/
theorem lookupClock_le (i:Inputs) (word:List Bool) (hw:word.length ≤ inputSize i) :
    lookupClock i word ≤ 2000*(inputSize i)^2 :=by
  have hD:=(basic_bounds i).2
  have hID:=(readID_length i word).trans hD
  have hS:=inputSize_pos i
  have hm:=Nat.mul_le_mul (show word.length+1 ≤ inputSize i+1 by omega)
    (show (Env.dictionary i.ids).length+1 ≤ inputSize i+1 by omega)
  unfold lookupClock
  nlinarith only [hw,hD,hID,hS,hm]
/-- Both actual frames and the actual row reversal cost at most a fixed multiple of the physical input byte budget. -/
theorem frameTime_le (i:Inputs) (own fac:List Bool) :frameTime i own fac ≤ 100*inputSize i :=by
  have ho:=(readID_length i own).trans (basic_bounds i).2
  have hj:=joint_length i (own,fac)
  have hc:=chunk_length i (own,fac)
  have hS:=inputSize_pos i
  unfold frameTime
  omega
/-- Actual complete per-occurrence source, including physical parsing, lookup, framing and every cleanup drain. -/
theorem rowTime_le (i:Inputs) (own fac:List Bool) (ho:own.length ≤ inputSize i) (hf:fac.length ≤ inputSize i) :
    rowTime i own fac ≤ 10000*(inputSize i)^2 :=by
  have h0:=lookupClock_le i own ho
  have h1:=lookupClock_le i fac hf
  have h2:=frameTime_le i own fac
  have hID:=(readID_length i own).trans (basic_bounds i).2
  have hj:=joint_length i (own,fac)
  have hS:=inputSize_pos i
  unfold rowTime bodyTime
  nlinarith only [h0,h1,h2,hID,hj,ho,hf,hS]
/-- Whole actual occurrence scan pays the original multiplicity, never only distinct selected keys. -/
theorem rowsTime_le (i:Inputs) (rows:List (List Bool×List Bool))
    (hr:∀row∈rows,row.1.length ≤ inputSize i ∧ row.2.length ≤ inputSize i) :
    rowsTime i rows ≤ rows.length*(10000*(inputSize i)^2)+1 :=by
  induction rows with
  | nil=>simpa only [rowsTime,List.foldr_nil,List.length_nil,Nat.zero_mul,Nat.zero_add] using (Nat.le_refl 1)
  | cons row rows ih=>
    rcases row with ⟨own,fac⟩
    have hh:=hr (own,fac) List.mem_cons_self
    have ht:=rowTime_le i own fac hh.1 hh.2
    have hi:=ih (fun row h=>hr row (List.mem_cons_of_mem _ h))
    change rowTime i own fac+rowsTime i rows ≤ _
    rw [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
end RiemannGaussian.SemiprimeD1StackSourceSelectedKeysBytes
