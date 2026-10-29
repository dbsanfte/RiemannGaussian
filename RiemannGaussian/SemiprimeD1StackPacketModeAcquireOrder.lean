/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketModeAcquireDouble
import RiemannGaussian.SemiprimeD1StackPacketModeAcquireCount
/-! # Actual order-marker loop acquires precisely2^(i+1) tile markers
Each actual order marker executes the complete real doubling source.
All source clocks below sum those literal fragments; no tile-count answer is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketModeAcquireOrder
open SemiprimeD1StackPacketModeAcquire SemiprimeD1StackPacketModeAcquireEncoding
open SemiprimeD1StackPacketModeAcquirePrimitives SemiprimeD1StackPacketModeAcquireDouble
open SemiprimeD1StackProcedureTrace
local notation "ctl"=>Label.local
/-- Exact clock of the actual order loop, including its actual final EOF pop. -/
def loopTime:Nat→Nat→Nat
  | 0,_=>1
  | i+1,tiles=>1+(5*tiles+4)+loopTime i (2*tiles)
/-- Each real marker triggers one real doubling, preserving every retained input and other actual mode role. -/
theorem loop_run (original order precision packets:List Bool) (i tiles:Nat) :
    Runs program (loopTime i tiles) (ctl .orderLoop)
      (bank (words original order precision packets (List.replicate i true) (List.replicate tiles true) []))
      (ctl .enumerate)
      (bank (words original order precision packets [] (List.replicate (tiles*2^i) true) [])) :=by
  induction i generalizing tiles with
  | zero=>
    have h:=pop_run .orderLoop (ctl .enumerate) (ctl .abort) (ctl .reverseTiles) (aux .todo)
      (bank (words original order precision packets [] (List.replicate tiles true) [])) [] rfl rfl
    rw [update_todo] at h
    simpa only [loopTime,pow_zero,Nat.mul_one,List.replicate_zero,List.head?_nil,List.tail_nil,
      SemiprimeD1StackBytecode.choose,words] using h
  | succ i ih=>
    have h0:=pop_run .orderLoop (ctl .enumerate) (ctl .abort) (ctl .reverseTiles) (aux .todo)
      (bank (words original order precision packets (List.replicate (i+1) true) (List.replicate tiles true) []))
      (true::List.replicate i true) rfl rfl
    simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
    rw [update_todo] at h0
    have h1:=double_run original order precision packets (List.replicate i true) tiles
    have h2:=ih (2*tiles)
    have h:=join (join h0 h1) h2
    have he:2*tiles*2^i=tiles*2^(i+1):=by rw [pow_succ];ring
    rw [he] at h
    exact h
/-- The actual materialized final tile word pays every intermediate doubling. -/
theorem loopTime_le (i tiles:Nat) :loopTime i tiles ≤(i+1)*(5*tiles*2^i+5) :=by
  induction i generalizing tiles with
  | zero=>simp only [loopTime,pow_zero,Nat.mul_one,Nat.zero_add,Nat.one_mul];omega
  | succ i ih=>
    have hc:=ih (2*tiles)
    have he:5*(2*tiles)*2^i+5=5*tiles*2^(i+1)+5:=by rw [pow_succ];ring
    rw [he] at hc
    have hp:1 ≤(2:Nat)^(i+1):=Nat.pow_pos (by decide)
    have hs:5*tiles+5 ≤5*tiles*2^(i+1)+5:=by
      have h:=Nat.mul_le_mul_left (5*tiles) hp
      omega
    simp only [loopTime]
    nlinarith only [hc,hs]
/-- Real count/seed/order prefix clock, using actual source-marker lengths. -/
def orderTime (i:Nat):Nat:=5*i+4+1+1+loopTime i 2
/-- The actual copied order markers, two seed pushes and entire doubling loop acquire the exact mode-source tile input. -/
theorem source_order_run (original precision:List Bool) (packets i:Nat) :
    Runs program (orderTime i) (ctl .copyOrder)
      (bank (SemiprimeD1StackPacketModeAcquireCount.words original (List.replicate i true) precision [] packets))
      (ctl .enumerate)
      (bank { modes:=M.input (List.replicate packets true) (List.replicate (2^(i+1)) true) precision
              packets:=original
              order:=List.replicate i true }) :=by
  let before:=SemiprimeD1StackPacketModeAcquireCount.words original (List.replicate i true) precision [] packets
  have h0:=copy_call .order .copyOrder .seedOne rfl (bank before) (List.replicate i true) [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (bank before) (aux .todo) (List.replicate i true++[])) at h0
  rw [List.append_nil,update_todo,List.length_replicate] at h0
  have h1:=push_tile .seedOne .seedTwo rfl original (List.replicate i true) precision
    (List.replicate packets true) (List.replicate i true) [] 0
  have h2:=push_tile .seedTwo .orderLoop rfl original (List.replicate i true) precision
    (List.replicate packets true) (List.replicate i true) [] 1
  have h3:=loop_run original (List.replicate i true) precision (List.replicate packets true) i 2
  have ht:2*2^i=2^(i+1):=by rw [pow_succ];ring
  rw [ht] at h3
  exact join (join (join h0 h1) h2) h3
end RiemannGaussian.SemiprimeD1StackPacketModeAcquireOrder
