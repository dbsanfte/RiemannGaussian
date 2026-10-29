/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsOuterView
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsCalls
/-! # Actual output sentinel and paid q copy from the six-word front door -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsSetup
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeightsCalls SemiprimeD1StackRecoveryWeightsOuterView
open SemiprimeD1StackRecoveryWeightsIndices SemiprimeD1StackProcedureTrace
open SemiprimeRationalBits (RationalWord)
/-- Actual initial bank is exactly the original boundary without a hidden output/count. -/
theorem input_outer (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool):
    input (SemiprimeD1StackNormalizedInverse.tape inverse) (SemiprimeD1StackNormalizedInverse.tape powers)
      (SemiprimeD1StackNormalizedInverse.signed scalar) scalar.denominator (unary q) width=
      bank (outer inverse powers scalar q width 0 []):=by
  funext role
  rcases role with (r|r)|r
  · rfl
  · rcases r with r|r
    · rfl
    · cases r <;> rfl
  · rfl
/-- One actual sentinel push and the complete restoring q copy precede the outer loop. -/
theorem setup_run (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool):
    Runs program (5*q+5) (.local .start)
      (input (SemiprimeD1StackNormalizedInverse.tape inverse) (SemiprimeD1StackNormalizedInverse.tape powers)
        (SemiprimeD1StackNormalizedInverse.signed scalar) scalar.denominator (unary q) width)
      (.local .outer) (bank (outer inverse powers scalar q width q [false])):=by
  rw [input_outer]
  have h0:=P.push_run (.local .start) (.local .copyCount) (aux .output) false (bank (outer inverse powers scalar q width 0 [])) rfl
  change Runs program 1 _ _ _ (Function.update (bank (outer inverse powers scalar q width 0 [])) (aux .output) [false]) at h0
  rw [update_aux,update_output] at h0
  have h1:=P.copy_call .count (.local .copyCount) (.local .outer) rfl
    (bank (outer inverse powers scalar q width 0 [false])) (unary q) [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (bank (outer inverse powers scalar q width 0 [false])) (aux .remaining) (unary q++[])) at h1
  rw [List.append_nil,update_remaining] at h1
  convert P.join h0 h1 using 1
  simp only [unary,List.length_replicate]
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsSetup
