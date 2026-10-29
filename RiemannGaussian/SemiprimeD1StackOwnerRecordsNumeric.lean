/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerRecordsLoop
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerRecordsNumeric
open SemiprimeD1StackOwnerRecords SemiprimeD1StackOwnerRecordsLoop SemiprimeD1StackOwnerRecordsEmit
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1OwnerPrefixBits (records records_length)
/-- Entire arbitrary caller tail is physically copied and then drained at EVERY owner. -/
theorem tail_length (fixed:List (List Bool×Bool)) (tail:List Bool) :tail.length≤(records fixed tail).length:=by
  rw [records_length];omega
theorem empty_length (fixed:List (List Bool×Bool)) (tail:List Bool) :
    (records fixed []).length≤(records fixed tail).length:=by rw [records_length,records_length];simp only [List.length_nil];omega
/-- Closed bound for a whole actual parse/copy/table/ordinal/log/cleanup iteration. -/
def rowCap (M P:Nat) :Nat:=10000*(M+1)*(P+1)
theorem row_budget_le (r:Row) (fixed:List (List Bool×Bool)) (tail:List Bool) (M:Nat)
    (hk:(keyOf r).length≤M) (hl:∀w∈wordsOf r,w.length≤M)
    (hv:∀w∈wordsOf r,SemiprimeBitArithmetic.bitValue w≤M) :
    rowBudget r fixed tail≤rowCap M (records fixed tail).length:=by
  have ht:=SemiprimeD1StackOwnerRecordBounds.timeBound_le (keyOf r) fixed (wordsOf r) r.property M hl hv
  have hb:=SemiprimeD1StackPortOrdinalStreamBounds.bank_length (wordsOf r) M hl
  have hd:=r.property
  have hp:=empty_length fixed tail
  have hs:=tail_length fixed tail
  have hb':(vectorBits (wordsOf r)).length≤2*(2*M+2)+1:=by nlinarith
  have hm:100*((keyOf r).length+1)*((records fixed []).length+1)≤
      100*(M+1)*((records fixed tail).length+1):=by gcongr
  unfold rowBudget rowCap
  nlinarith
/-- Every actual row byte is paid by the SAME real logger subtrace. -/
theorem row_bytes_le (r:Row) (fixed:List (List Bool×Bool)) (tail:List Bool) :
    (rowBytes r fixed).length≤rowBudget r fixed tail:=by
  have ht:(rowBytes r fixed).length≤E.timeBound (keyOf r) fixed (wordsOf r) r.property:=by
    unfold rowBytes SemiprimeD1StackOwnerRecordExecution.timeBound L.row
      SemiprimeD1StackOwnerRecord.R.recordTime
    simp only [List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
    omega
  unfold rowBudget;omega
/-- Complete emitted row bytes are bounded by the actual all-owner loop budget. -/
theorem bytes_budget (rows:List Row) (fixed:List (List Bool×Bool)) (tail:List Bool) :
    (bytes rows fixed).length≤loopBudget rows fixed tail:=by
  induction rows with
  | nil=>rfl
  | cons r rows ih=>
    have h:=row_bytes_le r fixed tail
    simp only [bytes,List.map_cons,List.flatten_cons,List.length_append,loopBudget,List.sum_cons] at *
    omega
/-- Summing actual original owner iterations introduces no supplied owner count. -/
theorem loop_budget_le (rows:List Row) (fixed:List (List Bool×Bool)) (tail:List Bool) (M:Nat)
    (hk:∀r∈rows,(keyOf r).length≤M) (hl:∀r∈rows,∀w∈wordsOf r,w.length≤M)
    (hv:∀r∈rows,∀w∈wordsOf r,SemiprimeBitArithmetic.bitValue w≤M) :
    loopBudget rows fixed tail≤rows.length*rowCap M (records fixed tail).length:=by
  induction rows with
  | nil=>simp only [loopBudget,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons r rows ih=>
    have h0:=row_budget_le r fixed tail M (hk r List.mem_cons_self)
      (hl r List.mem_cons_self) (hv r List.mem_cons_self)
    have h1:=ih (fun x hx=>hk x (List.mem_cons_of_mem r hx))
      (fun x hx=>hl x (List.mem_cons_of_mem r hx)) (fun x hx=>hv x (List.mem_cons_of_mem r hx))
    change rowBudget r fixed tail+loopBudget rows fixed tail≤_
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul];omega
end RiemannGaussian.SemiprimeD1StackOwnerRecordsNumeric
