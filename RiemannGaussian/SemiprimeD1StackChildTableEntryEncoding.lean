/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildTableEntry
import RiemannGaussian.SemiprimeD1ChildTableCopyTape
/-! # Actual retained context and individual coefficient output banks -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildTableEntryEncoding
open SemiprimeD1StackChildTableEntry
open SemiprimeD1TensorTapeCodec (vectorBits tape)
open SemiprimeD1StackUnaryDivmod (unary)
namespace Context
export SemiprimeD1StackJetContextCorrectness (finalData)
end Context
/-- Actual auxiliary tape values only; no such structure inhabits runtime control. -/
structure Words where
  /-- Retained complete serialized parent table. -/
  parentTable:List Bool:=[]
  /-- Retained actual vector of unary port indices. -/
  order:List Bool:=[]
  /-- Physically acquired remaining new-rank markers. -/
  remaining:List Bool:=[]
  /-- Physically acquired remaining old-rank markers. -/
  oldRemaining:List Bool:=[]
  /-- Actual parsed original coefficient or literal zero word. -/
  coefficient:List Bool:=[]
  /-- Actual field validity singleton. -/
  valid:List Bool:=[]
  /-- Actual shared restoring copy/parser/frame work. -/
  scratch:List Bool:=[]
  /-- Actual single tagged coefficient row buffer. -/
  buffer:List Bool:=[]
  /-- Actual reverse chronological coefficient log. -/
  history:List Bool:=[]
  /-- Actual final coefficient vector. -/
  output:List Bool:=[]
  /-- Actual final success singleton. -/
  success:List Bool:=[]
  /-- Paid physical copy of the whole stopped parent-entry vector. -/
  parentEntry:List Bool:=[]
/-- Fixed twelve-address view of physical helper tapes. -/
def words (w:Words):Aux→List Bool
  | .parentTable=>w.parentTable | .order=>w.order | .remaining=>w.remaining | .oldRemaining=>w.oldRemaining
  | .coefficient=>w.coefficient | .valid=>w.valid | .scratch=>w.scratch | .buffer=>w.buffer
  | .history=>w.history | .output=>w.output | .success=>w.success | .parentEntry=>w.parentEntry
/-- A literal helper update is a single physical word update. -/
theorem words_update (w:Words) (k:Aux) (xs:List Bool):Function.update (words w) k xs=words
    {parentTable:=if k=.parentTable then xs else w.parentTable,order:=if k=.order then xs else w.order,
     remaining:=if k=.remaining then xs else w.remaining,oldRemaining:=if k=.oldRemaining then xs else w.oldRemaining,
     coefficient:=if k=.coefficient then xs else w.coefficient,valid:=if k=.valid then xs else w.valid,
     scratch:=if k=.scratch then xs else w.scratch,buffer:=if k=.buffer then xs else w.buffer,
     history:=if k=.history then xs else w.history,output:=if k=.output then xs else w.output,
     success:=if k=.success then xs else w.success,parentEntry:=if k=.parentEntry then xs else w.parentEntry}:=by
  funext j;cases k <;> cases j <;> rfl
/-- Exact current input headers, assignment and actual table/order, with no supplied cache. -/
theorem initial_bank (table order assignment oldAxes oldp newAxes newp:List Bool):
    (initial table order assignment oldAxes oldp newAxes newp).data=
      bank (J.initial oldAxes oldp).data (J.initial newAxes newp).data (G.contents [] assignment [] [] [] [])
        (T.contents [] [] [] [] []) (R.store [] [] [] [] [] [] [] []) (words {parentTable:=table,order:=order}):=by
  apply congrArg (bank (J.initial oldAxes oldp).data (J.initial newAxes newp).data
    (G.contents [] assignment [] [] [] []) (T.contents [] [] [] [] []) (R.store [] [] [] [] [] [] [] []))
  funext k;cases k <;> rfl
/-- SAME-program ready entry reuses the whole actually acquired old/new context banks and acquires every other result itself. -/
def ready (oldAxes newAxes:List Nat) (oldp newp table order assignment:List Bool):C.State Stack Label:=
  ⟨some (.local .ready),none,none,
    bank (Context.finalData oldAxes oldp) (Context.finalData newAxes newp) (G.contents [] assignment [] [] [] [])
      (T.contents [] [] [] [] []) (R.store [] [] [] [] [] [] [] []) (words {parentTable:=table,order:=order}),[]⟩
/-- Literal independent modular reduction of ALL old and appended-zero coefficients. -/
def lifted (newp:List Bool) (oldWords:List (List Bool)) (zeros:Nat):List (List Bool):=
  (oldWords++List.replicate zeros []).map (fun word=>(SemiprimeD1JetScalarBits.reduce (SemiprimeBitArithmetic.bitValue newp) word).bits)
/-- Complete successful bank retains all30 actual context cache fields, all7 source words and the actually copied parent entry. -/
def result (oldAxes newAxes:List Nat) (oldp newp table order assignment:List Bool)
    (oldWords:List (List Bool)):Stack→List Bool:=
  bank (Context.finalData oldAxes oldp) (Context.finalData newAxes newp) (G.contents [] assignment [] [] [] [])
    (T.contents [] [] [] [] []) (R.store [] [] [] [] [] [] [] [])
    (words {parentTable:=table,order:=order,output:=vectorBits (lifted newp oldWords (newAxes.prod-oldAxes.prod)),success:=[true],parentEntry:=vectorBits oldWords})
/-- Actual whole halt clears both transient flags and all genuine return cells. -/
def done (oldAxes newAxes:List Nat) (oldp newp table order assignment:List Bool)
    (oldWords:List (List Bool)):C.State Stack Label:=
  ⟨none,none,none,result oldAxes newAxes oldp newp table order assignment oldWords,[]⟩
/-- One literal chronological coefficient chunk; a false is a valid empty-word delimiter. -/
def row (word:List Bool):List Bool:=true::SemiprimeSourceHistogramKeyBits.frame word []
/-- Reverse history is physically accumulated and finally reversed once. -/
def history (ws:List (List Bool)):List Bool:=ws.flatMap row
/-- Literal chunk sequence plus false is the exact vector codec. -/
theorem history_vector (ws:List (List Bool)):history ws++[false]=vectorBits ws:=by
  induction ws with
  | nil=>rfl
  | cons word ws ih=>
    change (row word++history ws)++[false]=true::SemiprimeSourceHistogramKeyBits.frame word (vectorBits ws)
    rw [List.append_assoc,ih]
    simp only [row,List.cons_append,SemiprimeD1TensorTapeCodec.frame_append,List.nil_append]
/-- Positive appended-axis lineage proves the exact literal number of added coefficients, without a runtime product operand. -/
theorem extra_count (old extra:List Nat) (_hp:0<extra.prod):
    (extra++old).prod-old.prod=old.prod*(extra.prod-1):=by
  rw [List.prod_append,Nat.mul_comm]
  simpa only [Nat.mul_one] using (Nat.mul_sub_left_distrib old.prod extra.prod 1).symm
/-- Exact per-entry old integer lift, including smaller new precision and every old coordinate. -/
theorem lifted_original (old:SemiprimeD1JetAxes.Context) (extra:List Nat) (newp:List Bool)
    (oldWords:List (List Bool)) (hp:0<extra.prod):
    lifted newp oldWords ((extra++old.axes).prod-old.axes.prod)=
      (SemiprimeD1ChildTableCopy.lift old extra (SemiprimeBitArithmetic.bitValue newp) oldWords).words:=by
  rw [lifted,extra_count old.axes extra hp,SemiprimeD1ChildTableCopy.lift_words]
  rfl
end RiemannGaussian.SemiprimeD1StackChildTableEntryEncoding
