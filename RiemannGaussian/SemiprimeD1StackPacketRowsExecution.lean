/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketRowsAcquire
import RiemannGaussian.SemiprimeD1StackPacketRowsLoop
import RiemannGaussian.SemiprimeD1StackPacketRowsFinish
/-! # Entire actual two-input packet-row source
The query IDs and colour fields below interpret actual source-produced bytes;
they are proof arguments, never additional physical inputs or control values.
Both rows are acquired from the actual catalogue before any colour is emitted.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketRowsExecution
open SemiprimeD1StackPacketRows SemiprimeD1StackPacketRowsPrimitives SemiprimeD1StackPacketRowsView
open SemiprimeD1StackPacketRowsRowView SemiprimeD1StackPacketRowsEncoding
open SemiprimeD1StackPacketRowsAcquire SemiprimeD1StackPacketRowsLoop SemiprimeD1StackPacketRowsFinish
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl" => Label.local
/-- Complete nineteen-role successful result, preserving both original input words and no workspace. -/
def result (key catalogue:List Bool) (left right:List (List Bool)) :Stack→List Bool :=
  view key catalogue [] [] [] [] [] [] [true] [] [] [] [] [] (vectorBits left) (vectorBits right)
/-- Actual final state has clear transient flags and no unresolved real source calls. -/
def done (key catalogue:List Bool) (left right:List (List Bool)) :C.State Stack Label :=
  ⟨none,none,none,result key catalogue left right,[]⟩
/-- Own complete copy/parser/lookup/paired-loop/logger/reversal/flag/halt cap. -/
def timeBound (owner factor:List Bool) (rows:List (List Bool×List Bool)) (left right:List (List Bool)) :Nat :=
  acquireBound owner factor rows+loopTime left right+
    (2*(rowsPrefix left).length+2*(rowsPrefix right).length+6)+2
/-- The whole actual successful source acquires both complete rows without any runtime coordinate-count or answer operand. -/
theorem source_trace (owner factor:List Bool) (rows:List (List Bool×List Bool))
    (left right:List (List Bool)) (hl:present owner rows=true) (hr:present factor rows=true)
    (hleft:payload owner rows=SemiprimeD1PacketRows.serialize left)
    (hright:payload factor rows=SemiprimeD1PacketRows.serialize right) (hlen:left.length=right.length) :
    ∃t,t+1 ≤ timeBound owner factor rows left right ∧
      Runs program t (ctl .start) (initial (frame owner factor) (SemiprimeD1StackOwnerLookup.records rows [])).data
        (ctl .done) (result (frame owner factor) (SemiprimeD1StackOwnerLookup.records rows []) left right) :=by
  let key:=frame owner factor
  let catalogue:=SemiprimeD1StackOwnerLookup.records rows []
  obtain ⟨a,ha,h0⟩:=acquire_run owner factor rows hl hr
  rw [hleft,hright] at h0
  have h1:=loop_run key catalogue left right (fun _=>[]) (fun _=>[false]) hlen
  let histories:=finalHistories (fun _=>[]) left right
  have h2:=finish_run key catalogue histories
  have ho:(fun side=>(histories side).reverse++[false])=
      (fun side=>vectorBits (if side then right else left)):=by
    funext side
    cases side <;> simp only [histories,finalHistories,List.append_nil,List.reverse_reverse,prefix_vector]
  rw [ho] at h2
  have ht:(2*(histories false).length+2*(histories true).length+6)=
      2*(rowsPrefix left).length+2*(rowsPrefix right).length+6:=by
    simp only [histories,finalHistories,List.append_nil,List.length_reverse,Bool.false_eq_true,ite_false,ite_true]
  rw [ht] at h2
  let ready:=rowView key catalogue (fun _=>[]) (fun _=>[]) (fun _=>[])
    (fun side=>vectorBits (if side then right else left)) []
  have h3:=push_run .accept (ctl .done) success true ready rfl
  change Runs program 1 _ _ _ (Function.update ready success [true]) at h3
  have he:Function.update ready success [true]=result key catalogue left right:=by
    funext k
    rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  rw [he] at h3
  have h:=join (join (join h0 h1) h2) h3
  exact ⟨_,by unfold timeBound;omega,h⟩
/-- Actual entire source includes the final physical halt, with both original inputs retained. -/
theorem source_run (owner factor:List Bool) (rows:List (List Bool×List Bool))
    (left right:List (List Bool)) (hl:present owner rows=true) (hr:present factor rows=true)
    (hleft:payload owner rows=SemiprimeD1PacketRows.serialize left)
    (hright:payload factor rows=SemiprimeD1PacketRows.serialize right) (hlen:left.length=right.length) :
    ∃t ≤ timeBound owner factor rows left right,SemiprimeD1StackCalls.run program t
      (initial (frame owner factor) (SemiprimeD1StackOwnerLookup.records rows []))=
      some (done (frame owner factor) (SemiprimeD1StackOwnerLookup.records rows []) left right) :=by
  obtain ⟨t,ht,hrun⟩:=source_trace owner factor rows left right hl hr hleft hright hlen
  obtain ⟨out,he,hAt⟩:=hrun [] (initial (frame owner factor) (SemiprimeD1StackOwnerLookup.records rows [])) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result (frame owner factor) (SemiprimeD1StackOwnerLookup.records rows []) left right) [] out hAt
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,he,Option.bind_some];exact hh⟩
end RiemannGaussian.SemiprimeD1StackPacketRowsExecution
