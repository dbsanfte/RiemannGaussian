/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketRowsLog
/-! # Entire paired physical EOF/colour-field loop, with no coordinate operand
The actual two raw streams determine the loop length. Every empty colour field
still has one real false delimiter and is parsed/logged. Only two simultaneous
physical EOFs finish the loop; no native row count is decoded or supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketRowsLoop
open SemiprimeD1StackPacketRows SemiprimeD1StackPacketRowsPrimitives SemiprimeD1StackPacketRowsRowView
open SemiprimeD1StackPacketRowsEncoding (row rowsPrefix serialize_cons_nonempty)
open SemiprimeD1StackPacketRowsLog SemiprimeD1StackProcedureTrace
namespace R
export SemiprimeD1PacketRows (serialize)
end R
local notation "ctl" => Label.local
/-- The two actual fixed raw stream roles, interpreted only in proof statements. -/
def streams (left right:List (List Bool)) (side:Bool) :List Bool :=if side then R.serialize right else R.serialize left
/-- Complete actual reverse-row histories after scanning the remaining raw colour fields. -/
def finalHistories (histories:Bool→List Bool) (left right:List (List Bool)) (side:Bool) :List Bool :=
  (rowsPrefix (if side then right else left)).reverse++histories side
/-- Exact actual two-EOF or paired-field logger clock. -/
def loopTime :List (List Bool)→List (List Bool)→Nat
  | [],[]=>2
  | l::ls,r::rs=>19*l.length+19*r.length+42+loopTime ls rs
  | _,_=>2
/-- A nonempty real row stream passes the actual peek even when its first byte is the empty-field false delimiter. -/
theorem nonempty_peek (pc:Control) (empty next:Label) (k:Stack) (before:Stack→List Bool) (xs:List Bool)
    (hc:program (ctl pc)=.base (.peek k empty next next)) (hx:before k=xs) (hn:xs≠[]) :
    Runs program 1 (ctl pc) before next before :=by
  have h:=peek_run pc empty next next k before xs hc hx
  cases xs with
  | nil=>exact (hn rfl).elim
  | cons b xs=>cases b <;> exact h
/-- Whole actual paired loop logs every original field once and finishes only at real simultaneous EOF. -/
theorem loop_run (key catalogue:List Bool) (left right:List (List Bool))
    (histories outputs:Bool→List Bool) (hlen:left.length=right.length) :
    Runs program (loopTime left right) (ctl .leftEOF)
      (rowView key catalogue (streams left right) (fun _=>[]) histories outputs [])
      (ctl .reverseLeft)
      (rowView key catalogue (streams [] []) (fun _=>[]) (finalHistories histories left right) outputs []) :=by
  induction left generalizing right histories with
  | nil=>
    cases right with
    | cons r rs=>simp only [List.length_nil,List.length_cons] at hlen;omega
    | nil=>
      have h0:=peek_run .leftEOF (ctl .rightEOF) (ctl .rightNonempty) (ctl .rightNonempty) (rowBytes false)
        (rowView key catalogue (streams [] []) (fun _=>[]) histories outputs []) [] rfl rfl
      have h1:=peek_run .rightEOF (ctl .reverseLeft) (ctl .reject) (ctl .reject) (rowBytes true)
        (rowView key catalogue (streams [] []) (fun _=>[]) histories outputs []) [] rfl rfl
      have he:finalHistories histories [] []=histories:=by funext side;cases side <;> rfl
      rw [he]
      exact join h0 h1
  | cons l ls ih=>
    cases right with
    | nil=>simp only [List.length_nil,List.length_cons] at hlen;omega
    | cons r rs=>
      let before:=rowView key catalogue (streams (l::ls) (r::rs)) (fun _=>[]) histories outputs []
      have h0:=nonempty_peek .leftEOF (ctl .rightEOF) (ctl .rightNonempty) (rowBytes false)
        before (R.serialize (l::ls)) rfl rfl (serialize_cons_nonempty l ls)
      have h1:=nonempty_peek .rightNonempty (ctl .reject) (ctl (.parseColour false)) (rowBytes true)
        before (R.serialize (r::rs)) rfl rfl (serialize_cons_nonempty r rs)
      have h2:=colour_run false key catalogue (streams (l::ls) (r::rs)) histories outputs l (R.serialize ls) rfl
      let midStreams:=Function.update (streams (l::ls) (r::rs)) false (R.serialize ls)
      let midHistories:=Function.update histories false ((row l).reverse++histories false)
      have h3:=colour_run true key catalogue midStreams midHistories outputs r (R.serialize rs) rfl
      have hs:Function.update midStreams true (R.serialize rs)=streams ls rs:=by funext side;cases side <;> rfl
      let nextHistories:Bool→List Bool:=fun side=>if side then (row r).reverse++histories true else (row l).reverse++histories false
      have hh:Function.update midHistories true ((row r).reverse++midHistories true)=nextHistories:=by funext side;cases side <;> rfl
      rw [hs,hh] at h3
      have h4:=ih rs nextHistories (by simp only [List.length_cons] at hlen;omega)
      have hf:finalHistories nextHistories ls rs=finalHistories histories (l::ls) (r::rs):=by
        funext side
        cases side <;> simp only [finalHistories,nextHistories,Bool.false_eq_true,ite_false,ite_true,
          rowsPrefix,List.flatMap_cons,List.reverse_append,List.append_assoc]
      rw [hf] at h4
      have h:=join (join (join (join h0 h1) h2) h3) h4
      have ht:1+1+(19*l.length+20)+(19*r.length+20)+loopTime ls rs=19*l.length+19*r.length+42+loopTime ls rs:=by omega
      simpa only [ht,before,loopTime] using h
/-- Actual paired field/EOF work is linear in both complete raw row payloads, including zero-field delimiters. -/
theorem loopTime_le (left right:List (List Bool)) (hlen:left.length=right.length) :
    loopTime left right ≤ 100*((R.serialize left).length+(R.serialize right).length+1) :=by
  induction left generalizing right with
  | nil=>cases right with
    | nil=>simp only [loopTime,R.serialize,List.length_nil];omega
    | cons r rs=>simp only [List.length_nil,List.length_cons] at hlen;omega
  | cons l ls ih=>cases right with
    | nil=>simp only [List.length_nil,List.length_cons] at hlen;omega
    | cons r rs=>
      have h:=ih rs (by simp only [List.length_cons] at hlen;omega)
      simp only [loopTime,R.serialize,SemiprimeSourceHistogramKeyBits.frame_length]
      omega
end RiemannGaussian.SemiprimeD1StackPacketRowsLoop
