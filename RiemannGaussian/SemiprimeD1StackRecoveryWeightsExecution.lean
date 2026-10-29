/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsSetup
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsOuter
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsFinishView
/-! # Complete actual six-input local-weight source, exact chronological array and true halt -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsExecution
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeightsCalls SemiprimeD1StackRecoveryWeightsOuterView
open SemiprimeD1StackRecoveryWeightsIndices SemiprimeD1StackProcedureTrace
open SemiprimeRationalBits (RationalWord)
namespace Spec
export SemiprimeD1StackRecoveryWeightsSpec (array)
end Spec
/-- Exact stopped full60-word bank, retaining all original raw words and no private work. -/
def result (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool):Stack→List Bool:=
  bank (outer inverse powers scalar q width 0 (SemiprimeD1StackNormalizedInverse.tape (Spec.array width q scalar inverse powers)))
/-- True halted state, with actual source flags and real internal return frames empty. -/
def done (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool):C.State Stack Label:=
  ⟨none,none,none,result inverse powers scalar q width,[]⟩
/-- SAME actual setup/complete nested loops/final53 physical sweep and halt. -/
def timeBound (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool):Nat:=
  5*q+5+SemiprimeD1StackRecoveryWeightsOuter.timeBound inverse powers scalar q width q [false]+
    53*(SemiprimeD1StackNormalizedInverseCleanup.mass (Old.store
      (outer inverse powers scalar q width 0 (SemiprimeD1StackNormalizedInverse.tape (Spec.array width q scalar inverse powers))).toWords)+1)+1
/-- Exact array bytes agree with the descending/prepend loop, before any value or validity reasoning. -/
theorem rows_array (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool):
    SemiprimeD1StackRecoveryWeightsOuter.rows inverse powers scalar q width q [false]=
      SemiprimeD1StackNormalizedInverse.tape (Spec.array width q scalar inverse powers):=rfl
/-- Whole prepared entry physically acquires every local coefficient and all cleanup words. -/
theorem source_trace (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool):
    ∃time ≤ timeBound inverse powers scalar q width-1,
      Runs program time (.local .start)
        (input (SemiprimeD1StackNormalizedInverse.tape inverse) (SemiprimeD1StackNormalizedInverse.tape powers)
          (SemiprimeD1StackNormalizedInverse.signed scalar) scalar.denominator (unary q) width)
        (.local .done) (result inverse powers scalar q width):=by
  have h0:=SemiprimeD1StackRecoveryWeightsSetup.setup_run inverse powers scalar q width
  obtain ⟨m,hm,h1⟩:=SemiprimeD1StackRecoveryWeightsOuter.outer_run inverse powers scalar q width q [false] le_rfl
  rw [rows_array] at h1
  obtain ⟨s,hs,h2⟩:=SemiprimeD1StackRecoveryWeightsCleanup.final_run
    (outer inverse powers scalar q width 0 (SemiprimeD1StackNormalizedInverse.tape (Spec.array width q scalar inverse powers)))
  rw [SemiprimeD1StackRecoveryWeightsFinishView.clean_outer] at h2
  refine ⟨5*q+5+m+s,?_,P.join (P.join h0 h1) h2⟩
  dsimp only [timeBound]
  omega
/-- The same whole finite program reaches actual halt; no native report clock is transported. -/
theorem source_run (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool):
    ∃time ≤ timeBound inverse powers scalar q width,SemiprimeD1StackCalls.run program time
      (initial (SemiprimeD1StackNormalizedInverse.tape inverse) (SemiprimeD1StackNormalizedInverse.tape powers)
        (SemiprimeD1StackNormalizedInverse.signed scalar) scalar.denominator (unary q) width)=some (done inverse powers scalar q width):=by
  obtain ⟨time,ht,hr⟩:=source_trace inverse powers scalar q width
  obtain ⟨finish,hfin,hAt⟩:=hr [] (initial (SemiprimeD1StackNormalizedInverse.tape inverse) (SemiprimeD1StackNormalizedInverse.tape powers)
    (SemiprimeD1StackNormalizedInverse.signed scalar) scalar.denominator (unary q) width) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (.local .done) rfl (result inverse powers scalar q width) [] finish hAt
  refine ⟨time+1,?_,?_⟩
  · have hp:0<timeBound inverse powers scalar q width:=by unfold timeBound;omega
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfin,Option.bind_some]
    exact hh
/-- SAME actual60-role genuine FinTM2, including all real return cells and no result/count callback. -/
noncomputable def weightsInTime (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool):
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (SemiprimeD1StackNormalizedInverse.tape inverse)
        (SemiprimeD1StackNormalizedInverse.tape powers) (SemiprimeD1StackNormalizedInverse.signed scalar) scalar.denominator (unary q) width))
      (some (SemiprimeD1StackCalls.configuration (done inverse powers scalar q width))) (timeBound inverse powers scalar q width):=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .denominator) (aux .output) (.local .start) program
  let h:=source_run inverse powers scalar q width
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsExecution
