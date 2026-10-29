/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootSelectionAcquireExecution
import RiemannGaussian.SemiprimeD1StackRootSelectionAcquireInputBounds
/-! # Own original-input whole-program acquisition bound
The only exponential factor comes from the actual row producer. Its fixed
power is preserved through the genuinely executed whole selection source.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootSelectionAcquireBounds
open SemiprimeD1StackRootSelectionAcquire SemiprimeD1StackRootSelectionAcquireEncoding
open SemiprimeD1StackRootSelectionAcquireExecution SemiprimeD1StackRootSelectionAcquireInputBounds
open SemiprimeBitArithmetic (bitValue)
/-- Fixed coefficient before every original N and before every actual acquired row/selection. -/
def clockCoefficient :Nat :=10^500*5^100+100
/-- Own original-input cap uses only paid source allowances, with no semantic result oracle. -/
def runBound (bits:List Bool) :Nat :=clockCoefficient*(envelope bits)^100
/-- The actual complete selection stage is charged to the actual original-input producer envelope. -/
theorem selection_clock_bound (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0 < bitValue bits) :
    E.polynomial (net bits hN) (dimension bits) ≤(10^500*5^100)*(envelope bits)^100 :=by
  have h:=Nat.mul_le_mul_left (10^500) (Nat.pow_le_pow_left (selection_input_bound bits hc hN) 100)
  simpa only [SemiprimeD1StackSourceSelectionAcquireBounds.polynomial,mul_pow,Nat.mul_assoc] using h
set_option exponentiation.threshold 512 in
/-- SAME whole actual clock pays acquisition, four copies, all three calls and halt. -/
theorem timeBound_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0 < bitValue bits) :timeBound bits hN ≤runBound bits :=by
  obtain ⟨hpos,hbits,hrows,hparameters⟩:=envelope_parts bits
  have hcopy:=acquisition_copy_bound bits hc hN
  have hselection:=selection_clock_bound bits hc hN
  have hlinear:envelope bits ≤(envelope bits)^100:=by
    simpa only [pow_one] using Nat.pow_le_pow_right hpos (by decide:1 ≤100)
  unfold parameterBound at hparameters
  unfold timeBound runBound clockCoefficient
  nlinarith only [hpos,hbits,hrows,hparameters,hcopy,hselection,hlinear]
/-- The identical actual source halts under its own complete original-input cap. -/
theorem source_run_bounded (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0 < bitValue bits) :
    ∃q ≤runBound bits,SemiprimeD1StackCalls.run program q (initial bits)=some (done bits hN) :=by
  obtain ⟨q,hq,hr⟩:=source_run bits hc hN
  exact ⟨q,hq.trans (timeBound_le bits hc hN),hr⟩
end RiemannGaussian.SemiprimeD1StackRootSelectionAcquireBounds
