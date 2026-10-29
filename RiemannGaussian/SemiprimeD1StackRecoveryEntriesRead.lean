/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesCalls
/-! # Actual two-level child acquisition with literal EOF defaults
The outer lookup acquires one actual encoded row. A missing row is physically
normalized by one false push, then the inner binary lookup reads the coefficient.
Both original source tapes and every parsed row byte remain retained.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesRead
open SemiprimeD1StackRecoveryEntries SemiprimeD1StackRecoveryEntriesState
open SemiprimeD1StackRecoveryEntriesPrimitives SemiprimeD1StackRecoveryEntriesCalls
open SemiprimeD1StackProcedureTrace
open SemiprimeD1StackRecoveryEntriesEncoding (childTape selectedChild)
open SemiprimeD1StackRecoveryDenominatorEncoding (Row)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeBitArithmetic (bitValue)
/-- Actual missing-row byte normalization, a literal false sentinel rather than a child answer. -/
def normalized:List Bool → List Bool
  | []=>[false]
  | b::bs=>b::bs
/-- The physical normalization test and optional literal push have their own actual clock. -/
def normalizeTime:List Bool → Nat
  | []=>2
  | _::_=>1
/-- One actual peek and, exactly at physical EOF, one actual false push. -/
theorem normalize_run (children:List Bool) (w:Aux → List Bool) (row:List Bool) (hr:w .selectedRow=row):
    Runs program (normalizeTime row) (.local .normalize) (data children w) (.local .inner)
      (data children (Function.update w .selectedRow (normalized row))):=by
  have h0:=peek_run (.local .normalize) (.local .emptyRow) (.local .inner) (.local .inner) .selectedRow children w row rfl hr
  cases row with
  | nil=>
    have h1:=push_run (.local .emptyRow) (.local .inner) .selectedRow false children w rfl
    rw [hr] at h1
    exact join h0 h1
  | cons b bs=>
    have he:Function.update w .selectedRow (b::bs)=w:=by rw [←hr];exact Function.update_eq_self _ _
    rw [show normalized (b::bs)=b::bs from rfl,he]
    cases b <;> exact h0
/-- Actual outer selected-row bytes, before its real missing-row normalization. -/
def outerBytes (children:List (List (List Bool))) (node:List Bool):List Bool:=
  ((children.map vectorBits)[bitValue node]?).getD []
/-- The actual normalized cache is exactly the encoded original child row or encoded empty default. -/
theorem normalized_outer (children:List (List (List Bool))) (node:List Bool):
    normalized (outerBytes children node)=vectorBits ((children[bitValue node]?).getD []):=by
  unfold outerBytes
  rw [List.getElem?_map]
  cases h:children[bitValue node]? with
  | none=>rfl
  | some row=>cases row <;> rfl
/-- Exact actual outer scan, physical EOF normalization and inner scan elapsed count. -/
def time (children:List (List (List Bool))) (r:Row):Nat:=
  (IX.timeBound (children.map vectorBits) (r 0)+1)+normalizeTime (outerBytes children (r 0))+
    (IX.timeBound ((children[bitValue (r 0)]?).getD []) (r 1)+1)
/-- Complete real node/index acquisition from ONLY actual nested child bytes and actual parsed binary fields. -/
theorem read_run (children:List (List (List Bool))) (original reader:List Bool) (r:Row) (history buffer out:List Bool):
    Runs program (time children r) (.local .outer)
      (data (childTape children) (words original reader r [] [] [] history buffer out)) (.local (.frame 0))
      (data (childTape children) (words original reader r
        (vectorBits ((children[bitValue (r 0)]?).getD [])) (selectedChild children (r 0) (r 1)) [] history buffer out)):=by
  have h0:=index_call false (childTape children) (words original reader r [] [] [] history buffer out) (children.map vectorBits) rfl rfl
  change Runs program (IX.timeBound (children.map vectorBits) (r 0)+1) (.local .outer)
    (data (childTape children) (words original reader r [] [] [] history buffer out)) (.local .normalize)
    (data (childTape children) (Function.update (words original reader r [] [] [] history buffer out) .selectedRow (outerBytes children (r 0)))) at h0
  rw [update_row] at h0
  have h1:=normalize_run (childTape children) (words original reader r (outerBytes children (r 0)) [] [] history buffer out) (outerBytes children (r 0)) rfl
  rw [update_row,normalized_outer] at h1
  have h2:=index_call true (childTape children)
    (words original reader r (vectorBits ((children[bitValue (r 0)]?).getD [])) [] [] history buffer out)
    ((children[bitValue (r 0)]?).getD []) rfl rfl
  change Runs program (IX.timeBound ((children[bitValue (r 0)]?).getD []) (r 1)+1) (.local .inner)
    (data (childTape children) (words original reader r (vectorBits ((children[bitValue (r 0)]?).getD [])) [] [] history buffer out))
    (.local (.frame 0)) (data (childTape children) (Function.update
      (words original reader r (vectorBits ((children[bitValue (r 0)]?).getD [])) [] [] history buffer out) .child (selectedChild children (r 0) (r 1)))) at h2
  rw [update_child] at h2
  exact join (join h0 h1) h2
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesRead
