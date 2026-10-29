/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootRecoveryWidthEncoding
/-! # Whole actual binary-N-only recovery-width acquisition
Both metadata values come from the SAME actual retained producer bank. Both
whole real sources, both preserving copies and the final halt execute here.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootRecoveryWidthExecution
open SemiprimeD1StackRootRecoveryWidth SemiprimeD1StackRootRecoveryWidthEncoding
open SemiprimeD1StackRootRecoveryWidthInput SemiprimeD1StackRootRecoveryWidthCalls
open SemiprimeD1StackRootRecoveryWidthPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
local notation "ctl"=>Label.local
/-- Actual original binary-input program computes its own grid and complete width template. -/
theorem source_trace (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits):
    ∃q,q+1 ≤ timeBound bits hN ∧ Runs program q (ctl .start) (input bits) (ctl .done) (result bits hN):=by
  obtain ⟨r,hr,h0⟩:=root_call bits hc hN (fun _=>[])
  have h1:=width_input_run (rootDone bits hN).data (root_scratch bits hN)
  rw [widthReady_original bits hc hN] at h1
  obtain ⟨w,hw,h2⟩:=width_call (O.originalA bits) (O.originalM bits) (rootDone bits hN).data
  have h:=join (join h0 h1) h2
  refine ⟨_,?_,h⟩
  unfold timeBound
  omega
/-- The same literal program genuinely halts from binary N alone after all actual acquisition. -/
theorem source_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits):
    ∃q ≤ timeBound bits hN,SemiprimeD1StackCalls.run program q (initial bits)=some (done bits hN):=by
  obtain ⟨q,hq,hr⟩:=source_trace bits hc hN
  obtain ⟨out,he,ha⟩:=hr [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result bits hN) [] out ha
  refine ⟨q+1,hq,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,he,Option.bind_some]
  exact hh
/-- Every original2139 source/cache/selection/frequency/padding word survives. -/
theorem root_retained (bits:List Bool) (hN:0 < bitValue bits) (k:R.Stack):
    (done bits hN).data (rootStack k)=(rootDone bits hN).data k:=rfl
/-- Entire actual72-role width-source output/cache bank is retained exactly. -/
theorem width_retained (bits:List Bool) (hN:0 < bitValue bits) (k:W.Stack):
    (done bits hN).data (widthStack k)=(widthDone bits).data k:=rfl
/-- Exact original false width-template bytes from the original binary input. -/
theorem output_original (bits:List Bool) (hN:0 < bitValue bits):
    (done bits hN).data output=
      List.replicate (SemiprimeD1RecoveryNodeBits.width (O.originalA bits) (O.originalM bits)) false:=rfl
end RiemannGaussian.SemiprimeD1StackRootRecoveryWidthExecution
