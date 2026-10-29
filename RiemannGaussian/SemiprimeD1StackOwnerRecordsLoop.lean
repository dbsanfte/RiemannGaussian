/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerRecordsLog
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerRecordsLoop
open SemiprimeD1StackOwnerRecords SemiprimeD1StackOwnerRecordsView
open SemiprimeD1StackOwnerRecordsRead SemiprimeD1StackOwnerRecordsEmit
open SemiprimeD1StackProcedureTrace (Runs runs_trans)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1OwnerPrefixBits (records)
/-- Proof-side acquired row description with degree derived from the original graph.
No Row, list, degree or numeric scope value appears in the finite instruction table. -/
abbrev Row := {x:List Bool×List (List Bool) //x.2.length≤2}
/-- Proof-only key projection from an already acquired owner row. -/
abbrev keyOf (r:Row) :List Bool:=r.val.1
/-- Proof-only ordered scope-word projection from an already acquired owner row. -/
abbrev wordsOf (r:Row) :List (List Bool):=r.val.2
/-- Exact acquired catalogue grammar for the proof-side original row sequence. -/
def encoded (rows:List Row) :List Bool:=
  SemiprimeD1StackOwnerLookup.records (rows.map fun r=>(keyOf r,vectorBits (wordsOf r))) []
/-- Exact row bytes written by the actual table, ordinal and consuming logger source. -/
def rowBytes (r:Row) (fixed:List (List Bool×Bool)) :List Bool:=
  L.row (SemiprimeD1StackOwnerRecord.S.result (wordsOf r))
    (E.table (keyOf r) fixed [] (wordsOf r) r.property)
/-- All actual emitted row bytes in original owner order, before the final list tag. -/
def bytes (rows:List Row) (fixed:List (List Bool×Bool)) :List Bool:=
  (rows.map fun r=>rowBytes r fixed).flatten
/-- Whole actual row parse, prefix copy, source execution and retained-operand drain allowance. -/
def rowBudget (r:Row) (fixed:List (List Bool×Bool)) (tail:List Bool) :Nat:=
  (8*(keyOf r).length+8*(vectorBits (wordsOf r)).length+17)+
    (5*(records fixed tail).length+4)+(E.timeBound (keyOf r) fixed (wordsOf r) r.property+1)+
    ((keyOf r).length+tail.length+(vectorBits (wordsOf r)).length+3)
/-- One ACTUAL acquired owner row, including prefix copying, all34 source roles and physical drains. -/
theorem row_run (s:S.Stack→List Bool) (r:Row) (fixed:List (List Bool×Bool)) (tail reader hist out:List Bool) :
    ∃time≤rowBudget r fixed tail,Runs program time (.local .loop)
      (data s (payload [] [] [] hist out)
        (rowAux (true::SemiprimeSourceHistogramKeyBits.frame (keyOf r)
          (SemiprimeSourceHistogramKeyBits.frame (vectorBits (wordsOf r)) reader)) (records fixed tail)))
      (.local .loop)
      (data s (payload [] [] [] ((rowBytes r fixed).reverse++hist) out) (rowAux reader (records fixed tail))):=by
  let a:=rowAux reader (records fixed tail)
  have h0:=row_read s (keyOf r) (vectorBits (wordsOf r)) reader (records fixed tail) hist out
  have h1:=prefix_copy s (keyOf r) (vectorBits (wordsOf r)) reader (records fixed tail) hist out
  obtain ⟨t,ht,h2⟩:=record_call s a (keyOf r) fixed tail (wordsOf r) r.property hist out
  rw [done_payload] at h2
  have h3:=clear_run s a (keyOf r) tail (vectorBits (wordsOf r))
    ((L.row (SemiprimeD1StackOwnerRecord.S.result (wordsOf r))
      (E.table (keyOf r) fixed tail (wordsOf r) r.property)).reverse++hist) out
  have h:=runs_trans program _ _ _ _ _ _ _ _ h0
    (runs_trans program _ _ _ _ _ _ _ _ h1 (runs_trans program _ _ _ _ _ _ _ _ h2 h3))
  refine ⟨(8*(keyOf r).length+8*(vectorBits (wordsOf r)).length+17)+
    ((5*(records fixed tail).length+4)+(t+((keyOf r).length+tail.length+(vectorBits (wordsOf r)).length+3))),?_,?_⟩
  · unfold rowBudget;omega
  · exact h
/-- Exact source-catalogue loop budget, dependent only on actual parsed/copied bytes. -/
def loopBudget (rows:List Row) (fixed:List (List Bool×Bool)) (tail:List Bool) :Nat:=
  (rows.map fun r=>rowBudget r fixed tail).sum
/-- Every acquired owner is visited in original E order, including isolated owners and repeated scopes. -/
theorem loop_run (s:S.Stack→List Bool) (rows:List Row) (fixed:List (List Bool×Bool)) (tail hist out:List Bool) :
    ∃time≤loopBudget rows fixed tail,Runs program time (.local .loop)
      (data s (payload [] [] [] hist out) (rowAux (encoded rows) (records fixed tail)))
      (.local .loop)
      (data s (payload [] [] [] ((bytes rows fixed).reverse++hist) out) (rowAux [false] (records fixed tail))):=by
  induction rows generalizing hist with
  | nil=>
    refine ⟨0,Nat.zero_le _,?_⟩
    exact SemiprimeD1StackProcedureTrace.runs_refl program _ _
  | cons r rows ih=>
    obtain ⟨a,ha,h0⟩:=row_run s r fixed tail (encoded rows) hist out
    obtain ⟨b,hb,h1⟩:=ih ((rowBytes r fixed).reverse++hist)
    refine ⟨a+b,?_,?_⟩
    · simpa only [loopBudget,List.map_cons,List.sum_cons] using Nat.add_le_add ha hb
    · have h:=runs_trans program _ _ _ _ _ _ _ _ h0 h1
      simpa only [encoded,List.map_cons,SemiprimeD1StackOwnerLookup.records,bytes,
        List.flatten_cons,List.reverse_append,List.append_assoc] using h
end RiemannGaussian.SemiprimeD1StackOwnerRecordsLoop
