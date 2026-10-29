/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketOrientationExecution
/-! # Own linear physical-byte clock for the whole literal orientation source
No colour/index numeric value is expanded. Every comparator, copy, field,
frame, reversal, cursor pop and real call/return belongs to the same trace.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketOrientationClock
open SemiprimeD1StackPacketOrientation SemiprimeD1StackPacketOrientationExecution
open SemiprimeD1StackPacketOrientationLoop SemiprimeD1StackPacketOrientationLayout
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- All three retained physical input words and one boundary cell. -/
def inputSize (left right index:List Bool):Nat:=left.length+right.length+index.length+1
/-- Fixed linear source cap in actual physical bytes. -/
def polynomial (left right index:List Bool):Nat:=10000*inputSize left right index
/-- Actual whole source cap is linear in physical vector/index lengths, not numeric values or old reports. -/
theorem timeBound_le (left right:List (List Bool)) (index:List Bool) (hlen:left.length=right.length):
    timeBound left right index ≤ polynomial (vectorBits left) (vectorBits right) index :=by
  have hl:=loopBound_le left right hlen
  have hc:=chunks_length left right
  have hs:=slots_length left right index hlen
  have hh:=high_length left right index
  unfold timeBound polynomial inputSize
  omega
/-- Whole actual source with its own physical-byte bound and exact stopped bank. -/
theorem source_run_bounded (left right:List (List Bool)) (index:List Bool) (hlen:left.length=right.length):
    ∃t ≤ polynomial (vectorBits left) (vectorBits right) index,SemiprimeD1StackCalls.run program t
      (initial (vectorBits left) (vectorBits right) index)=some (done left right index) :=by
  obtain ⟨t,ht,h⟩:=source_run left right index hlen
  exact ⟨t,ht.trans (timeBound_le left right index hlen),h⟩
/-- SAME literal-source time certificate; its witness is extracted from the actual full trace. -/
noncomputable def sourceOrient (left right:List (List Bool)) (index:List Bool) (hlen:left.length=right.length):
    StateTransition.EvalsToInTime (SemiprimeD1StackCalls.step program)
      (initial (vectorBits left) (vectorBits right) index) (some (done left right index))
      (polynomial (vectorBits left) (vectorBits right) index) :=by
  let h:=source_run_bounded left right index hlen
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Genuine finite compiled machine with the same whole source and linear byte clock. -/
noncomputable def machineOrient (left right:List (List Bool)) (index:List Bool) (hlen:left.length=right.length):
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (vectorBits left) (vectorBits right) index))
      (some (SemiprimeD1StackCalls.configuration (done left right index)))
      (polynomial (vectorBits left) (vectorBits right) index) :=
  SemiprimeD1StackCalls.evalsCorrect (aux .leftInput) (aux .keyOutput) (SemiprimeD1StackPacketOrientation.Label.local .start)
    program _ _ _ (sourceOrient left right index hlen)
end RiemannGaussian.SemiprimeD1StackPacketOrientationClock
