/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesFields
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesRead
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesOrder
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesCleanup
/-! # Complete actual row-to-entry acquisition and occurrence-preserving order
Every input row is parsed, read twice through actual binary indexed scans,
framed, logged and cleaned. Missing child coordinates produce empty payloads;
they never remove rows. One final actual reverse restores original row order.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesLoop
open SemiprimeD1StackRecoveryEntries SemiprimeD1StackRecoveryEntriesState
open SemiprimeD1StackRecoveryEntriesPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeD1StackRecoveryDenominatorEncoding (Row fields tape)
open SemiprimeD1StackRecoveryEntriesEncoding (childTape selectedChild)
open SemiprimeD1StackRecoveryEntriesOrder (chunks)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeBitArithmetic (bitValue)
namespace P
export SemiprimeD1StackRecoveryEntriesFields (parse_run time)
end P
namespace R
export SemiprimeD1StackRecoveryEntriesRead (read_run time)
end R
namespace L
export SemiprimeD1StackRecoveryEntriesLogger (row_run rowTime chunk reverse_call)
end L
namespace K
export SemiprimeD1StackRecoveryEntriesCleanup (source_run cleared_words mass)
end K
/-- Exact seven actually cleared source/cache word-byte lengths. -/
def clearMass (r:Row) (row child:List Bool):Nat:=
  (r 0).length+(r 1).length+(r 2).length+(r 3).length+(r 4).length+row.length+child.length
/-- Actual per-row cleanup work does not rescan prior output/history. -/
theorem mass_words (original reader:List Bool) (r:Row) (row child valid history buffer out:List Bool):
    K.mass (words original reader r row child valid history buffer out) 0=clearMass r row child:=by
  simp only [K.mass,SemiprimeD1StackRecoveryEntriesCleanup.cleanup,List.drop_zero,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,words]
  unfold clearMass
  omega
/-- Exact actually acquired encoded row cache, including the missing-node empty-vector sentinel. -/
def selectedRow (children:List (List (List Bool))) (r:Row):List Bool:=vectorBits ((children[bitValue (r 0)]?).getD [])
/-- SAME actual row-step clock, independent of previous entry history and output bytes. -/
def rowTime (children:List (List (List Bool))) (r:Row):Nat:=
  1+P.time r+R.time children r+L.rowTime r (selectedChild children (r 0) (r 1))+
    (clearMass r (selectedRow children r) (selectedChild children (r 0) (r 1))+7)
/-- One actual row produces one entry, preserving duplicates, zeros and both EOF defaults. -/
theorem row_run (children:List (List (List Bool))) (original:List Bool) (r:Row) (rs:List Row) (history out:List Bool):
    Runs program (rowTime children r) (.local .loop)
      (data (childTape children) (words original (tape (r::rs)) (fun _=>[]) [] [] [] history [] out)) (.local .loop)
      (data (childTape children) (words original (tape rs) (fun _=>[]) [] [] []
        ((L.chunk r (selectedChild children (r 0) (r 1))).reverse++history) [] out)):=by
  have h0:=pop_run (.local .loop) (.local .abort) (.local .finish) (.local (.field 0)) .reader (childTape children)
    (words original (tape (r::rs)) (fun _=>[]) [] [] [] history [] out) (true::fields r (tape rs)) rfl rfl
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
  rw [update_reader] at h0
  have h1:=P.parse_run (childTape children) original (fields r (tape rs)) r (tape rs) [] [] history [] out rfl
  have h2:=R.read_run children original (tape rs) r history [] out
  have h3:=L.row_run (childTape children) original (tape rs) r (selectedRow children r)
    (selectedChild children (r 0) (r 1)) history out
  have h4:=K.source_run (childTape children) (words original (tape rs) r (selectedRow children r)
    (selectedChild children (r 0) (r 1)) [] ((L.chunk r (selectedChild children (r 0) (r 1))).reverse++history) [] out)
  rw [mass_words,K.cleared_words] at h4
  exact join (join (join (join h0 h1) h2) h3) h4
/-- Exact own whole row-loop clock, including the single actual final reverse. -/
def budget (children:List (List (List Bool))):List Row → List Bool → Nat
  | [],history=>1+(2*history.length+3)
  | r::rs,history=>rowTime children r+budget children rs ((L.chunk r (selectedChild children (r 0) (r 1))).reverse++history)
/-- Whole actual entry loop restores original row order after one final physical reverse. -/
theorem loop_run (children:List (List (List Bool))) (rs:List Row) (original history out:List Bool):
    Runs program (budget children rs history) (.local .loop)
      (data (childTape children) (words original (tape rs) (fun _=>[]) [] [] [] history [] out)) (.local .done)
      (data (childTape children) (words original [] (fun _=>[]) [] [] [] [] []
        (history.reverse++chunks children rs++out))):=by
  induction rs generalizing history with
  | nil=>
    have h0:=pop_run (.local .loop) (.local .abort) (.local .finish) (.local (.field 0)) .reader (childTape children)
      (words original [false] (fun _=>[]) [] [] [] history [] out) [false] rfl rfl
    simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
    rw [update_reader] at h0
    have h1:=L.reverse_call true (.local .finish) (.local .done) (childTape children)
      (words original [] (fun _=>[]) [] [] [] history [] out) rfl
    change Runs program (2*history.length+3) (.local .finish)
      (data (childTape children) (words original [] (fun _=>[]) [] [] [] history [] out)) (.local .done)
      (data (childTape children) (Function.update (Function.update (words original [] (fun _=>[]) [] [] [] history [] out) .history []) .output (history.reverse++out))) at h1
    rw [update_history,update_out] at h1
    simpa only [budget,chunks,List.append_nil,tape] using join h0 h1
  | cons r rs ih=>
    have h0:=row_run children original r rs history out
    have h1:=ih ((L.chunk r (selectedChild children (r 0) (r 1))).reverse++history)
    have h:=join h0 h1
    simpa only [budget,chunks,List.reverse_append,List.reverse_reverse,List.append_assoc] using h
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesLoop
