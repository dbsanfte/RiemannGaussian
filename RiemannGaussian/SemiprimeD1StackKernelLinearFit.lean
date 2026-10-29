/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinearView
/-! # Actual original-width fitting and displacement subtraction -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearFit
open SemiprimeD1StackKernelLinear SemiprimeD1StackKernelLinearPrimitives
open SemiprimeD1StackKernelLinearCalls SemiprimeD1StackKernelLinearView
open SemiprimeD1StackProcedureTrace SemiprimeBitArithmetic SemiprimeBitDivision
/-- Complete five-role actual fit at an original-word arithmetic boundary. -/
theorem fit_trace (second:Bool) (pc next:Label) (hc:program pc=.call (.fit second .start) next)
    (w:Words) (word:List Bool) (hr:w.remaining=[])
    (hd:words w (if second then .j else .displacement)=[]):
    Runs program (fitTime word w.k) pc (arithmeticData w [] [] word) next
      (data (SemiprimeD1StackKernelLinearView.set w (if second then .j else .displacement)
        (SemiprimeD1StackWordFitExecution.result word w.k))):=by
  have hi:∀r,arithmeticData w [] [] word (fitStack second r)=
      SemiprimeD1StackWordFit.store word w.k [] [] [] r:=by
    intro r;fin_cases r
    · rfl
    · rfl
    · exact hr
    · rfl
    · exact hd
  have h:=fit_call second pc next hc (arithmeticData w [] [] word) word w.k hi
  change Runs program _ _ _ _
    (Function.update (Function.update (arithmeticData w [] [] word) (arithmetic .output) [])
      (aux (if second then .j else .displacement)) (SemiprimeD1StackWordFitExecution.result word w.k)) at h
  rw [arithmeticData_output_update,arithmeticData_aux_update,arithmeticData_empty] at h
  exact h
/-- Exact original displacement word produced by real subtraction and fitting. -/
def displacement (w:Words):List Bool:=
  SemiprimeD1StackWordFitExecution.result (subBits w.buffer w.x false).result.bits w.k
/-- Every actual displacement operand copy, borrow pop and fit call is paid. -/
def displacementTime (w:Words):Nat:=
  (5*w.buffer.length+4)+(5*w.x.length+4)+subTime w.buffer w.x+1+
    fitTime (subBits w.buffer w.x false).result.bits w.k
/-- Actual false borrow licenses the fit; no mathematical displacement is a runtime operand. -/
theorem displacement_trace (w:Words) (hs:w.scratch=[]) (hr:w.remaining=[]) (hd:w.displacement=[])
    (hb:(subBits w.buffer w.x false).borrow=false):
    Runs program (displacementTime w) (.local .bufferSub) (data w) (.local .tCopy)
      (data {w with displacement:=displacement w}):=by
  have h0:=copy_call .bufferSub (.local .bufferSub) (.local .xSub) rfl
    (arithmeticData w [] [] []) w.buffer [] rfl rfl hs
  simp only [List.append_nil] at h0
  change Runs program _ _ _ _ (Function.update (arithmeticData w [] [] []) (arithmetic .left) w.buffer) at h0
  rw [arithmeticData_left_update] at h0
  have h1:=copy_call .xSub (.local .xSub) (.local .displacementSub) rfl
    (arithmeticData w w.buffer [] []) w.x [] rfl rfl hs
  simp only [List.append_nil] at h1
  change Runs program _ _ _ _ (Function.update (arithmeticData w w.buffer [] []) (arithmetic .right) w.x) at h1
  rw [arithmeticData_right_update] at h1
  have h2:=sub_call (.local .displacementSub) (.local .displacementBorrow) rfl (fun _=>[]) (words w) w.buffer w.x
  rw [hb] at h2
  have h3:=pop_run (.local .displacementBorrow) (.local .abort) (.local .displacementFit) (.local .abort)
    (arithmetic .output) (arithmeticData w [] [] ((subBits w.buffer w.x false).borrow::(subBits w.buffer w.x false).result.bits))
    ((subBits w.buffer w.x false).borrow::(subBits w.buffer w.x false).result.bits) rfl rfl
  simp only [List.head?_cons,List.tail_cons,hb,SemiprimeD1StackBytecode.choose,arithmeticData_output_update] at h3
  have h4:=fit_trace false (.local .displacementFit) (.local .tCopy) rfl w
    (subBits w.buffer w.x false).result.bits hr hd
  simp only [Bool.false_eq_true,ite_false] at h4
  have hh:=join h0 (join h1 (join h2 (join h3 h4)))
  simpa only [displacementTime,displacement,arithmeticData_empty,SemiprimeD1StackKernelLinearView.set,Nat.add_assoc] using hh
/-- Actual retained t is copied, fitted and consumed; its original padding is charged. -/
theorem grid_trace (w:Words) (hs:w.scratch=[]) (hr:w.remaining=[]) (hj:w.j=[]):
    Runs program ((5*w.t.length+4)+fitTime w.t w.k) (.local .tCopy) (data w) (.local .alphaCopy)
      (data {w with j:=SemiprimeD1StackWordFitExecution.result w.t w.k}):=by
  have h0:=copy_call .tFit (.local .tCopy) (.local .tFit) rfl
    (arithmeticData w [] [] []) w.t [] rfl rfl hs
  simp only [List.append_nil] at h0
  change Runs program _ _ _ _ (Function.update (arithmeticData w [] [] []) (arithmetic .output) w.t) at h0
  rw [arithmeticData_output_update] at h0
  have h1:=fit_trace true (.local .tFit) (.local .alphaCopy) rfl w w.t hr hj
  simpa only [arithmeticData_empty,ite_true,SemiprimeD1StackKernelLinearView.set] using join h0 h1
end RiemannGaussian.SemiprimeD1StackKernelLinearFit
