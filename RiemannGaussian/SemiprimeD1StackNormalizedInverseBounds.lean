/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseOuterBounds
import RiemannGaussian.SemiprimeD1StackNormalizedInverseOutputBounds
import RiemannGaussian.SemiprimeD1StackNormalizedInverseExecution
/-! # Whole actual normalized inverse has a fixed polynomial bit clock
All physical array scans, unary index copies/pops, fitted R36 source calls,
coefficient framing/reversal, every58-role boundary and real returns are paid.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseBounds
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseStateBounds SemiprimeD1StackNormalizedInverseOuterBounds
open SemiprimeD1StackNormalizedInverseOutputBounds SemiprimeD1StackNormalizedInverseExecution
open SemiprimeD1StackNormalizedInverseEncoding SemiprimeD1StackNormalizedInverseReadBuffers
/-- Coefficient and degree are fixed BEFORE every denominator array, q and W template. -/
def polynomial (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) : ℕ :=
  10^42*(inputSize a q width)^10
/-- SAME actual whole source clock, with cached-prefix lengths and every complete coefficient individually charged. -/
theorem runBound_le (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) :
    runBound a q width ≤ polynomial a q width := by
  have ha:=acquireBound_le a q width
  have hf:=SemiprimeD1StackNormalizedInverseOutputBounds.finishTime_le a q width
  have hc:=beforeCleanup_mass a q width
  have hs:=inputSize_caps a q width
  have hs8:(inputSize a q width)^8 ≤ (inputSize a q width)^10:=Nat.pow_le_pow_right hs.1 (by decide:8≤10)
  have hs2:(inputSize a q width)^2 ≤ (inputSize a q width)^10:=Nat.pow_le_pow_right hs.1 (by decide:2≤10)
  have hp:1 ≤ (inputSize a q width)^10:=Nat.one_le_pow _ _ hs.1
  unfold runBound polynomial
  nlinarith only [ha,hf,hc,hs8,hs2,hp]
/-- ALL typed physical arrays and ALL actual unary q/W words terminate with exact native bytes within this fixed clock. -/
theorem source_run_bounded (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) :
    ∃t≤polynomial a q width,SemiprimeD1StackCalls.run program t (initial (tape a) (unary q) width)=some (done a q width) := by
  obtain ⟨t,ht,hr⟩:=source_run a q width
  exact ⟨t,ht.trans (runBound_le a q width),hr⟩
/-- Actual fixed58-role prepared source machine; the denominator producer/literal caller are separate. -/
noncomputable def machineSource (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (tape a) (unary q) width))
      (some (SemiprimeD1StackCalls.configuration (done a q width))) (polynomial a q width) := by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .denominator) (aux .output) (ctl .start) program
  let h:=source_run_bounded a q width
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackNormalizedInverseBounds
