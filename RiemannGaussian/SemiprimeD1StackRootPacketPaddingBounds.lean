/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPacketPaddingExecution
import RiemannGaussian.SemiprimeD1StackRootPacketPaddingInputBounds
/-! # Own complete original-input packet-padding source clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPacketPaddingBounds
open SemiprimeD1StackRootPacketPadding SemiprimeD1StackRootPacketPaddingEncoding
open SemiprimeD1StackRootPacketPaddingExecution SemiprimeD1StackRootPacketPaddingInputBounds
open SemiprimeBitArithmetic (bitValue)
/-- Fixed whole-source coefficient, before every original binary N. -/
def clockCoefficient :Nat :=100000000000*3^5+100
/-- The same whole finite program has a fifth-degree paid-producer cap. -/
def runBound (bits:List Bool) :Nat :=clockCoefficient*(envelope bits)^5
/-- The real producer, both copies, actual frequency/rounding call and halt are all charged. -/
theorem timeBound_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits) :
    timeBound bits hN ≤runBound bits :=by
  obtain ⟨hpos,_,hroot⟩:=envelope_parts bits
  have hcopy:=copy_time_bound bits hc hN
  have hpadding:=padding_clock_bound bits hc hN
  have hlinear:envelope bits ≤(envelope bits)^5:=by
    simpa only [pow_one] using Nat.pow_le_pow_right hpos (by decide:1 ≤5)
  unfold timeBound runBound clockCoefficient
  nlinarith only [hpos,hroot,hcopy,hpadding,hlinear]
/-- Exact stopped original padding bank within the SAME complete original-input source cap. -/
theorem source_run_bounded (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits) :
    ∃t ≤runBound bits,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits hN) :=by
  obtain ⟨t,ht,hr⟩:=source_run bits hc hN
  exact ⟨t,ht.trans (timeBound_le bits hc hN),hr⟩
end RiemannGaussian.SemiprimeD1StackRootPacketPaddingBounds
