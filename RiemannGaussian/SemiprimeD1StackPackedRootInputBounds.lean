/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootInputExecution
/-! # Own whole-source sum bound without a previous-runtime power recurrence -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedRootInputBounds
open SemiprimeD1StackPackedRootInput SemiprimeD1StackPackedRootInputEncoding
open SemiprimeD1StackPackedRootInputExecution
open SemiprimeBitArithmetic (bitValue)
/-- Whole actual original-source clocks plus a fixed quadratic handoff/context allowance. -/
def runBound (bits : List Bool) : ℕ :=
  SemiprimeD1StackRootPacketInventoryBounds.runBound bits+
    SemiprimeD1StackMarkedRootRecordsBounds.runBound bits+3000*(bits.length+1)^2+100
/-- The real ready continuation is paid by its own closed source bound. -/
theorem timeBound_le (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    timeBound bits hN ≤ runBound bits := by
  have hw:=SemiprimeD1StackMarkedRootRecordsReady.readyBound_le bits hc hN
  have hs : bits.length+1 ≤ (bits.length+1)^2 := Nat.le_pow (by decide : 0<(2 : ℕ))
  unfold timeBound runBound
  omega
/-- SAME whole finite program, SAME exact2505-word stop, from original binary N alone. -/
theorem source_run_bounded (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    ∃t ≤ runBound bits,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits hN) := by
  obtain ⟨t,ht,hr⟩:=source_run bits hc hN
  exact ⟨t,ht.trans (timeBound_le bits hc hN),hr⟩
end RiemannGaussian.SemiprimeD1StackPackedRootInputBounds
