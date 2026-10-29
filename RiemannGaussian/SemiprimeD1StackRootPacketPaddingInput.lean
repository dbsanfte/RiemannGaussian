/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPacketPaddingPrimitives
/-! # Actual selected-key/dimension transfers with the retained source scratch -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPacketPaddingInput
open SemiprimeD1StackRootPacketPadding SemiprimeD1StackRootPacketPaddingView
open SemiprimeD1StackRootPacketPaddingPrimitives SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Only the literal next source's two input fields are populated. -/
def paddingReady (root:R.Stack→List Bool) :Q.Stack→List Bool :=
  Function.update (Function.update (fun _=>[])
    (Q.frequencyStack (SemiprimeD1StackSourceKeyFrequency.aux .source)) (root R.output))
    (Q.aux .exponent) (root (R.parameterStack SemiprimeD1StackRootParameters.exponent))
/-- The two actual writes yield exactly the next real source's honest physical input bank. -/
theorem paddingReady_input (root:R.Stack→List Bool) :paddingReady root=
    (Q.initial (root R.output) (root (R.parameterStack SemiprimeD1StackRootParameters.exponent))).data :=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
  · cases k <;> rfl
/-- Both restoring copies pay every actual key/dimension byte and both real returns. -/
def paddingCopyTime (root:R.Stack→List Bool) :Nat :=
  5*((root R.output).length+(root (R.parameterStack SemiprimeD1StackRootParameters.exponent)).length)+8
/-- The original producer bank is retained literally, including its reused scratch restored to empty. -/
theorem padding_input_run (root:R.Stack→List Bool) (hs:root R.copyScratch=[]) :
    Runs program (paddingCopyTime root) (ctl (.copy .keys)) (data root (fun _=>[]))
      (ctl .padding) (data root (paddingReady root)) :=by
  let s0:Q.Stack→List Bool:=fun _=>[]
  let s1:=Function.update s0 (Q.frequencyStack (SemiprimeD1StackSourceKeyFrequency.aux .source)) (root R.output)
  let s2:=Function.update s1 (Q.aux .exponent) (root (R.parameterStack SemiprimeD1StackRootParameters.exponent))
  have h0:=copy_call .keys (data root s0) (root R.output) [] rfl rfl hs
  simp only [List.append_nil] at h0
  change Runs program _ _ _ _ (Function.update (data root s0)
    (paddingStack (Q.frequencyStack (SemiprimeD1StackSourceKeyFrequency.aux .source))) (root R.output)) at h0
  rw [data_padding] at h0
  have h1:=copy_call .dimension (data root s1) (root (R.parameterStack SemiprimeD1StackRootParameters.exponent)) [] rfl rfl hs
  simp only [List.append_nil] at h1
  change Runs program _ _ _ _ (Function.update (data root s1)
    (paddingStack (Q.aux .exponent)) (root (R.parameterStack SemiprimeD1StackRootParameters.exponent))) at h1
  rw [data_padding] at h1
  have h:=join h0 h1
  change Runs program _ _ _ (ctl .padding) _ at h
  change Runs program _ _ _ _ (data root s2)
  convert h using 1
  unfold paddingCopyTime
  omega
end RiemannGaussian.SemiprimeD1StackRootPacketPaddingInput
