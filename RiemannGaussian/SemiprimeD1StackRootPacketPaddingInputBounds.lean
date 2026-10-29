/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPacketPaddingEncoding
/-! # Every actual frequency/rounding operand is paid by its real original-input producer -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPacketPaddingInputBounds
open SemiprimeD1StackRootPacketPadding SemiprimeD1StackRootPacketPaddingEncoding
open SemiprimeBitArithmetic (bitValue)
/-- Only actual input bytes and the actual original-input acquisition cap enter this envelope. -/
def envelope (bits:List Bool) :Nat :=bits.length+SemiprimeD1StackRootSelectionAcquireBounds.runBound bits+1
/-- Each producer operand and one literal boundary cell are paid. -/
theorem envelope_parts (bits:List Bool) :1 ≤envelope bits ∧ bits.length ≤envelope bits ∧
    SemiprimeD1StackRootSelectionAcquireBounds.runBound bits ≤envelope bits :=by
  unfold envelope
  omega
/-- Every stopped original source word is bounded from that SAME actual source execution. -/
theorem root_word_bound (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0 < bitValue bits) (k:R.Stack) :((rootDone bits hN).data k).length ≤envelope bits :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackRootSelectionAcquireBounds.source_run_bounded bits hc hN
  have h:=SemiprimeD1StackReturnLink.run_data_bound R.program t bits.length _ _
    (SemiprimeD1StackRootSelectionAcquireStorage.initial_length bits) hr k
  change ((rootDone bits hN).data k).length ≤bits.length+t at h
  unfold envelope
  omega
/-- Actual acquired keys and actual acquired unary dimension pay the entire next physical source input. -/
theorem padding_input_bound (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0 < bitValue bits) :
    SemiprimeD1StackSourcePacketPaddingEncoding.inputSize (keys bits hN) (A.dimension bits) ≤3*envelope bits :=by
  have hk:=root_word_bound bits hc hN R.output
  rw [root_keys bits hN] at hk
  have ha:=root_word_bound bits hc hN (R.parameterStack SemiprimeD1StackRootParameters.exponent)
  rw [root_dimension bits hc hN,List.length_replicate] at ha
  have hpos:1 ≤envelope bits:=(envelope_parts bits).1
  unfold SemiprimeD1StackSourcePacketPaddingEncoding.inputSize SemiprimeD1StackSourceKeyFrequencyEncoding.inputSize
  omega
/-- The two actual preserving copies have only the already paid source-word lengths as costs. -/
theorem copy_time_bound (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0 < bitValue bits) :
    SemiprimeD1StackRootPacketPaddingInput.paddingCopyTime (rootDone bits hN).data ≤18*envelope bits :=by
  have hk:=root_word_bound bits hc hN R.output
  have ha:=root_word_bound bits hc hN (R.parameterStack SemiprimeD1StackRootParameters.exponent)
  have hpos:1 ≤envelope bits:=(envelope_parts bits).1
  unfold SemiprimeD1StackRootPacketPaddingInput.paddingCopyTime
  omega
/-- The actual full frequency+rounding source is polynomial in the actual original-input producer envelope. -/
theorem padding_clock_bound (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0 < bitValue bits) :E.polynomial (keys bits hN) (A.dimension bits) ≤
      (100000000000*3^5)*(envelope bits)^5 :=by
  have h:=Nat.mul_le_mul_left 100000000000 (Nat.pow_le_pow_left (padding_input_bound bits hc hN) 5)
  simpa only [SemiprimeD1StackSourcePacketPaddingBounds.polynomial,mul_pow,Nat.mul_assoc] using h
end RiemannGaussian.SemiprimeD1StackRootPacketPaddingInputBounds
