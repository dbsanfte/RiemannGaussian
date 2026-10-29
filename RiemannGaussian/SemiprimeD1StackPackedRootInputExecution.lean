/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootInputCalls
/-! # One actual original-binary-input trace through marked records and context -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedRootInputExecution
open SemiprimeD1StackPackedRootInput SemiprimeD1StackPackedRootInputEncoding
open SemiprimeD1StackPackedRootInputPrimitives SemiprimeD1StackPackedRootInputCalls
open SemiprimeD1StackProcedureTrace SemiprimeBitArithmetic
/-- Fixed sum of SAME actual component clocks, one physical N copy and true halt. -/
def timeBound (bits : List Bool) (hN : 0<bitValue bits) : ℕ :=
  SemiprimeD1StackRootPacketInventoryBounds.runBound bits+
    SemiprimeD1StackMarkedRootRecordsExecution.readyBound bits hN+
      2000*(bits.length+1)^2+5*bits.length+8
/-- Complete own2505-role trace: acquire old bank once, mark actual tables, copy N, acquire context. -/
theorem source_trace (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    ∃t,t+1 ≤ timeBound bits hN ∧
      Runs program t (.local .start) (input bits) (.local .done) (result bits hN) := by
  obtain ⟨a,ha,h0⟩:=root_call bits hc hN
  obtain ⟨b,hb,h1⟩:=marked_call bits hc hN
  obtain ⟨c,hc0,h3⟩:=context_call bits hN
  have h2:=copy_N bits hN
  refine ⟨a+(b+((5*bits.length+4)+c)),?_,join h0 (join h1 (join h2 h3))⟩
  unfold timeBound
  omega
/-- SAME complete N-only program physically reaches its real halt with every bank retained. -/
theorem source_run (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    ∃t ≤ timeBound bits hN,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits hN) := by
  obtain ⟨t,ht,h⟩:=source_trace bits hc hN
  obtain ⟨finish,hf,hs⟩:=h [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (.local .done) rfl (result bits hN) [] finish hs
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
end RiemannGaussian.SemiprimeD1StackPackedRootInputExecution
