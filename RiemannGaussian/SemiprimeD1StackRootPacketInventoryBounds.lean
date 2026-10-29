/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPacketInventoryExecution
import RiemannGaussian.SemiprimeD1StackRootPacketInventoryInputBounds
/-! # Own complete original-input shared-root/inventory clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPacketInventoryBounds
open SemiprimeD1StackRootPacketInventory SemiprimeD1StackRootPacketInventoryEncoding
open SemiprimeD1StackRootPacketInventoryExecution SemiprimeD1StackRootPacketInventoryInputBounds
open SemiprimeBitArithmetic (bitValue)
/-- One fixed coefficient before every original binary input. -/
def clockCoefficient:Nat:=1000000000000*3^4+100
/-- The actual producer envelope is raised to a fixed fourth power ONCE at this root join. -/
def runBound (bits:List Bool):Nat:=clockCoefficient*(envelope bits)^4
/-- Shared original-input producer, both real copies, full inventory and halt are all paid. -/
theorem timeBound_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits):
    timeBound bits hN ≤ runBound bits:=by
  have hp:1 ≤ envelope bits:=by unfold envelope;omega
  have hr:SemiprimeD1StackRootRecoveryWidthBounds.runBound bits ≤ envelope bits:=by unfold envelope;omega
  have hc0:=copy_time_bound bits hc hN
  have hi:=inventory_clock_bound bits hc hN
  have hlin:envelope bits ≤ (envelope bits)^4:=Nat.le_pow (by decide:0 < 4)
  unfold timeBound runBound clockCoefficient
  nlinarith only [hp,hr,hc0,hi,hlin]
/-- SAME whole finite program genuinely halts from binary N within its own entire-source clock. -/
theorem source_run_bounded (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits):
    ∃q ≤ runBound bits,SemiprimeD1StackCalls.run program q (initial bits)=some (done bits hN):=by
  obtain ⟨q,hq,hr⟩:=source_run bits hc hN
  exact ⟨q,hq.trans (timeBound_le bits hc hN),hr⟩
end RiemannGaussian.SemiprimeD1StackRootPacketInventoryBounds
