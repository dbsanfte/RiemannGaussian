/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinearView
/-! # Actual center-plus-y acquisition and retained binary sum -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearSum
open SemiprimeD1StackKernelLinear SemiprimeD1StackKernelLinearPrimitives
open SemiprimeD1StackKernelLinearView SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic
/-- Actual full binary sum retained before displacement subtraction. -/
def value (w:Words):List Bool:=(addBits w.center w.y false).bits
/-- Sum-source actual copy, adder, cache and cleanup clock. -/
def timeBound (w:Words):Nat:=
  (5*w.center.length+4)+(5*w.y.length+4)+addTime w.center w.y+(5*(value w).length+4)+((value w).length+3)
/-- Complete actual sum front door, with every foreign word retained. -/
theorem source_trace (w:Words) (hs:w.scratch=[]) (hb:w.buffer=[]):
    Runs program (timeBound w) (.local .centerAdd) (data w) (.local .bufferSub)
      (data {w with buffer:=value w}):=by
  have h0:=copy_call .centerAdd (.local .centerAdd) (.local .yAdd) rfl
    (arithmeticData w [] [] []) w.center [] rfl rfl hs
  simp only [List.append_nil] at h0
  change Runs program _ _ _ _ (Function.update (arithmeticData w [] [] []) (arithmetic .left) w.center) at h0
  rw [arithmeticData_left_update] at h0
  have h1:=copy_call .yAdd (.local .yAdd) (.local .add) rfl
    (arithmeticData w w.center [] []) w.y [] rfl rfl hs
  simp only [List.append_nil] at h1
  change Runs program _ _ _ _ (Function.update (arithmeticData w w.center [] []) (arithmetic .right) w.y) at h1
  rw [arithmeticData_right_update] at h1
  have h2:=add_call (.local .add) (.local .sum) rfl (fun _=>[]) (words w) w.center w.y
  have h3:=copy_call .sum (.local .sum) (.local .clearSum) rfl
    (arithmeticData w [] [] (value w)) (value w) [] rfl hb hs
  simp only [List.append_nil] at h3
  change Runs program _ _ _ _ (Function.update (arithmeticData w [] [] (value w)) (aux .buffer) (value w)) at h3
  rw [arithmeticData_aux_update] at h3
  have h4:=drain_call (.local .clearSum) (.local .bufferSub) (arithmetic .output)
    (arithmeticData {w with buffer:=value w} [] [] (value w)) (value w) rfl rfl
  rw [arithmeticData_output_update] at h4
  have hh:=join h0 (join h1 (join h2 (join h3 h4)))
  simpa only [timeBound,value,SemiprimeD1StackKernelLinearView.set,arithmeticData_empty,Nat.add_assoc] using hh
end RiemannGaussian.SemiprimeD1StackKernelLinearSum
