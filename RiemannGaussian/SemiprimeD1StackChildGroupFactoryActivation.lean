/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryCalls
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryColour
/-! # Whole real activation iteration for every old vertex
The selected ID is acquired from the actual environment, and the actual
catalogue row supplies the colour. Isolated vertices use this same iteration.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivation
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryCalls SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace Col
export SemiprimeD1StackChildGroupFactoryColour (view result time source_trace)
end Col
/-- The activation loop carries just four physical work words across iterations. -/
def data (i:Inputs) (todo key hist map:List Bool):Stack→List Bool
  | .inr (.inr (.inr (.inr (.inr .vertexTodo))))=>todo
  | .inr (.inr (.inr (.inr (.inr .vertexKey))))=>key
  | .inr (.inr (.inr (.inr (.inr .activationHistory))))=>hist
  | .inr (.inr (.inr (.inr (.inr .activationMap))))=>map
  | k=>input i k
/-- Reading the computed equality byte and logging one Boolean requires three literal instructions. -/
theorem flag_trace (before:Stack→List Bool) (flag:Bool)
    (hf:before (arithmetic .output)=[flag]):
    Runs program 3 (.local 1 9) before (.local 1 14)
      (Function.update (Function.update (Function.update before (arithmetic .output) [])
        (aux .flagScratch) (flag::before (aux .flagScratch)))
        (aux .activationHistory) (flag::before (aux .activationHistory))):=by
  have h0:=pop_run (.local 1 9) abort (.local 1 10) (.local 1 12)
    (arithmetic .output) before [flag] rfl hf
  have h1:=push_run (if flag then .local 1 12 else .local 1 10)
    (if flag then .local 1 13 else .local 1 11) (aux .flagScratch) flag
    (Function.update before (arithmetic .output) []) (by cases flag <;> rfl)
  have h2:=push_run (if flag then .local 1 13 else .local 1 11) (.local 1 14)
    (aux .activationHistory) flag
    (Function.update (Function.update before (arithmetic .output) [])
      (aux .flagScratch) (flag::before (aux .flagScratch))) (by cases flag <;> rfl)
  have h1':Runs program 1 (if flag then .local 1 12 else .local 1 10)
      (Function.update before (arithmetic .output) []) (if flag then .local 1 13 else .local 1 11)
      (Function.update (Function.update before (arithmetic .output) [])
        (aux .flagScratch) (flag::before (aux .flagScratch))):=by
    simpa [Function.update_apply,arithmetic,aux] using h1
  have h2':Runs program 1 (if flag then .local 1 13 else .local 1 11)
      (Function.update (Function.update before (arithmetic .output) [])
        (aux .flagScratch) (flag::before (aux .flagScratch))) (.local 1 14)
      (Function.update (Function.update (Function.update before (arithmetic .output) [])
        (aux .flagScratch) (flag::before (aux .flagScratch)))
        (aux .activationHistory) (flag::before (aux .activationHistory))):=by
    simpa [Function.update_apply,arithmetic,aux] using h2
  have h0':Runs program 1 (.local 1 9) before (if flag then .local 1 12 else .local 1 10)
      (Function.update before (arithmetic .output) []):=by
    cases flag <;> exact h0
  exact join h0' (join h1' h2')
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivation
