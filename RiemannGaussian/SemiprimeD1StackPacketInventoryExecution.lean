/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryLoop
import RiemannGaussian.SemiprimeD1StackPacketInventoryPrepare
import RiemannGaussian.SemiprimeD1StackPacketInventoryFinish
/-! # Entire actual two-input sparse packet inventory source
Every input read, row decode, OLD counter, orientation, override, first discovery,
placement frame, cleanup, final reversal and halt executes in this single source.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryExecution
open SemiprimeD1StackPacketInventory SemiprimeD1StackPacketInventoryPrimitives
open SemiprimeD1StackPacketInventoryEncoding SemiprimeD1StackPacketInventoryBanks
open SemiprimeD1StackPacketInventoryLoop SemiprimeD1StackPacketInventoryPrepare
open SemiprimeD1StackPacketInventoryFinish SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl"=>Label.local
/-- Complete paid source cap, formed only by sums of actual source fragment caps. -/
def timeBound (a:Nat) (pairs:Pairs):Nat:=
  5*(vectorBits (keys pairs)).length+8+replayBound a empty pairs+
    2*(history (acquire a (keys pairs)).placements).length+6
/-- Actual entire source trace reaches its exact59-word result, including empty occurrence streams. -/
theorem source_trace (a:Nat) (pairs:Pairs) (hv:Valid a pairs):
    ∃t,t+1 ≤ timeBound a pairs ∧ Runs program t (ctl .start)
      (source a (keys pairs)).data (ctl .done)
      (result (vectorBits (keys pairs)) (alphabet a) (acquire a (keys pairs))):=by
  have h0:=prepare_run (vectorBits (keys pairs)) (alphabet a)
  have hm:SemiprimeD1StackPacketInventorySeen.Markers empty.seen:=by intro r hr;cases hr
  obtain ⟨t1,ht1,h1⟩:=replay_run a pairs hv empty hm (vectorBits (keys pairs))
  have h2:=finish_run (vectorBits (keys pairs)) (alphabet a) (acquire a (keys pairs))
  have h:=join (join h0 h1) h2
  refine ⟨_,?_,h⟩
  unfold timeBound
  omega
/-- Whole actual final halt, with both transient flags and every real nested return cleared. -/
theorem source_run (a:Nat) (pairs:Pairs) (hv:Valid a pairs):
    ∃t ≤ timeBound a pairs,SemiprimeD1StackCalls.run program t (source a (keys pairs))=
      some (done (vectorBits (keys pairs)) (alphabet a) (acquire a (keys pairs))):=by
  obtain ⟨t,ht,h⟩:=source_trace a pairs hv
  obtain ⟨out,he,hAt⟩:=h [] (source a (keys pairs)) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl
    (result (vectorBits (keys pairs)) (alphabet a) (acquire a (keys pairs))) [] out hAt
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,he,Option.bind_some];exact hh⟩
end RiemannGaussian.SemiprimeD1StackPacketInventoryExecution
