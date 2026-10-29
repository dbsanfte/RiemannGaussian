/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEuclidGCDExecution
/-! # Uniform original-binary-byte polynomial bound for the actual Euclid source -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackEuclidGCDBounds
open SemiprimeD1StackEuclidGCD SemiprimeD1StackEuclidGCDEncoding SemiprimeD1StackEuclidGCDSpec
open SemiprimeD1StackEuclidGCDSetup SemiprimeD1StackEuclidGCDLoop SemiprimeD1StackEuclidGCDExecution
/-- A uniform coefficient and degree fixed before both original input words. -/
def polynomial (left right:List Bool) :Nat:=100000000*(inputSize left right)^4
/-- Real original-byte scanning, copies and initial trim are linear even for arbitrarily padded zeros. -/
theorem setupTime_le (left right:List Bool) :setupTime left right≤100*(inputSize left right):=by
  have ht:=SemiprimeD1StackReduceExecution.trimTime_le right.reverse
  simp only [List.length_reverse] at ht
  unfold setupTime inputSize
  omega
/-- Same complete source clock is polynomial in original binary byte lengths, with no numeric unary expansion. -/
theorem runBound_le (left right:List Bool) :runBound left right≤ polynomial left right:=by
  let S:=inputSize left right
  have hS:1≤ S:=by dsimp [S,inputSize];omega
  have hL:left.length≤ S:=by dsimp [S,inputSize];omega
  have hR:(SemiprimeD1StackSourceEnvironmentEncoding.normalize right).length≤ S:=
    (SemiprimeD1StackSourceEnvironmentEncoding.normalize_length right).trans (by dsimp [S,inputSize];omega)
  have hs:=setupTime_le left right
  have hl:=loopTime_le (fuelLength left right) left (SemiprimeD1StackSourceEnvironmentEncoding.normalize right) S hS hL hR
  have hf:fuelLength left right≤2*S:=by dsimp [fuelLength,S,inputSize];omega
  have hm: (fuelLength left right)*(1000*S^2+20*S+1)≤2*S*(1000*S^2+20*S+1):=
    Nat.mul_le_mul_right _ hf
  have h13:S≤ S^3:=Nat.le_pow (by decide:0<(3:Nat))
  have h23:S^2≤ S^3:=Nat.pow_le_pow_right hS (by decide:2≤3)
  have h34:S^3≤ S^4:=Nat.pow_le_pow_right hS (by decide:3≤4)
  change runBound left right≤100000000*S^4
  unfold runBound
  change setupTime left right≤100*S at hs
  nlinarith only [hs,hl,hm,hS,h13,h23,h34]
/-- Exact stopped source output within the fixed binary-input polynomial bound. -/
theorem source_run_bounded (left right:List Bool) :
    ∃q≤ polynomial left right,SemiprimeD1StackCalls.run program q (initial left right)=some (done left right):=
  ⟨runBound left right,runBound_le left right,source_run left right⟩
/-- The actual fixed compiled machine has this SAME whole-source clock. -/
noncomputable def machineSource (left right:List Bool) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (initial left right))
      (some (SemiprimeD1StackCalls.configuration (done left right))) (polynomial left right):=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .left) (aux .output) .start program
  let h:=source_run_bounded left right
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackEuclidGCDBounds
