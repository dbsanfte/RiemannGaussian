/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootRecoveryWidthExecution
/-! # Own whole original-input width-source clock
The original root clock is retained once. Both actual unary metadata copies
and the complete width source add a fixed original-bitlength polynomial.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootRecoveryWidthBounds
open SemiprimeD1StackRootRecoveryWidth SemiprimeD1StackRootRecoveryWidthEncoding
open SemiprimeD1StackRootRecoveryWidthExecution SemiprimeD1StackRootRecoveryWidthInput
open SemiprimeBitArithmetic (bitValue)
namespace WO
export SemiprimeD1StackRecoveryWidthOriginal (sizingCoefficient globalClockCoefficient original_envelope original_clock)
end WO
/-- Fixed coefficient pays both actual metadata copies and the real complete width source. -/
def clockCoefficient:Nat:=10*WO.sizingCoefficient+WO.globalClockCoefficient+20
/-- SAME whole-source clock retains the actual root once and pays all added acquisition by a fixed polynomial. -/
def runBound (bits:List Bool):Nat:=
  SemiprimeD1StackRootPacketPaddingBounds.runBound bits+clockCoefficient*(bits.length+1)^120
/-- The two copied byte lengths equal the actual acquired unary metadata values. -/
theorem copy_time (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits):
    widthCopyTime (rootDone bits hN).data=5*(O.originalA bits+O.originalM bits)+8:=by
  unfold widthCopyTime
  change 5*(((SemiprimeD1StackRootPacketPaddingEncoding.done bits hN).data O.exponentRole).length+
    ((SemiprimeD1StackRootPacketPaddingEncoding.done bits hN).data O.edgesRole).length)+8=_
  rw [SemiprimeD1StackRecoveryWidthOriginal.root_exponent bits hc hN,
    SemiprimeD1StackRecoveryWidthOriginal.root_edges bits hN]
  simp only [SemiprimeD1StackUnaryDivmod.unary,List.length_replicate]
/-- Every actual original-input operation belongs to this SAME enclosing clock, with no native report transport. -/
theorem timeBound_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits):
    timeBound bits hN ≤ runBound bits:=by
  have hen:=WO.original_envelope bits hc hN
  have hp:(bits.length+1)^10 ≤ (bits.length+1)^120:=Nat.pow_le_pow_right (by omega) (by decide:10 ≤ 120)
  have ham:O.originalA bits+O.originalM bits ≤
      SemiprimeD1StackRecoveryWidthEncoding.inputEnvelope (O.originalA bits) (O.originalM bits):=by
    change O.originalA bits+O.originalM bits ≤ O.originalA bits+O.originalM bits+2^(O.originalA bits+1)+1
    exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  have hmeta:O.originalA bits+O.originalM bits ≤ WO.sizingCoefficient*(bits.length+1)^120:=
    (ham.trans hen).trans (Nat.mul_le_mul_left WO.sizingCoefficient hp)
  have hw:=WO.original_clock bits hc hN
  have hcopy:=copy_time bits hc hN
  have hpos:1 ≤ (bits.length+1)^120:=Nat.one_le_pow _ _ (by omega)
  unfold timeBound runBound clockCoefficient
  rw [hcopy]
  nlinarith only [hmeta,hw,hpos]
/-- Actual genuine binary-input source halts with the whole root and width banks under its own bound. -/
theorem source_run_bounded (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits):
    ∃q ≤ runBound bits,SemiprimeD1StackCalls.run program q (initial bits)=some (done bits hN):=by
  obtain ⟨q,hq,hr⟩:=source_run bits hc hN
  exact ⟨q,hq.trans (timeBound_le bits hc hN),hr⟩
end RiemannGaussian.SemiprimeD1StackRootRecoveryWidthBounds
