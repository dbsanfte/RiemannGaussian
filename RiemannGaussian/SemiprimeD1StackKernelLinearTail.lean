/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinearDivisionView
/-! # Both actual normalization branches before common final cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearTail
open SemiprimeD1StackKernelLinear SemiprimeD1StackKernelLinearView
open SemiprimeD1StackKernelLinearPrimitives SemiprimeD1StackKernelLinearCalls
open SemiprimeD1StackKernelLinearDivisionView SemiprimeD1StackProcedureTrace
/-- Exact literal zero-factor branch: content alpha, constant empty, slope ONE. -/
theorem zero_trace (w:Words) (mag:List Bool) (hs:w.scratch=[]) (hz:w.slope=[]):
    Runs program ((w.content.length+3)+(5*w.alpha.length+4)+1) (.local .zeroContent) (arithmeticData w [] [] mag)
      (.local .clearDelta) (arithmeticData {w with content:=w.alpha,slope:=[true]} [] [] mag):=by
  have h0:=drain_call (.local .zeroContent) (.local .zeroCopy) (aux .content) (arithmeticData w [] [] mag) w.content rfl rfl
  simp only [arithmeticData_aux_update,SemiprimeD1StackKernelLinearView.set] at h0
  have h1:=copy_call .alphaContent (.local .zeroCopy) (.local .zeroSlope) rfl
    (arithmeticData {w with content:=[]} [] [] mag) w.alpha [] rfl rfl hs
  simp only [List.append_nil] at h1
  change Runs program _ _ _ _ (Function.update (arithmeticData {w with content:=[]} [] [] mag) (aux .content) w.alpha) at h1
  simp only [arithmeticData_aux_update,SemiprimeD1StackKernelLinearView.set] at h1
  have h2:=push_run (.local .zeroSlope) (.local .clearDelta) (aux .slope) true (arithmeticData {w with content:=w.alpha} [] [] mag) rfl
  change Runs program 1 _ _ _ (Function.update (arithmeticData {w with content:=w.alpha} [] [] mag) (aux .slope) (true::w.slope)) at h2
  simp only [arithmeticData_aux_update,SemiprimeD1StackKernelLinearView.set] at h2
  simpa only [hz,Nat.add_assoc] using join h0 (join h1 h2)
/-- Actual odd-suffix copy and both original-magnitude cleanup calls. -/
def prepareTime (w:Words) (mag:List Bool):Nat:=(5*w.scan.length+4)+(w.scan.length+3)+(mag.length+3)
/-- The entire real divider bank is actually cleared before the division call. -/
theorem prepare_trace (w:Words) (mag:List Bool) (hs:w.scratch=[]) (hc:w.constant=[]):
    Runs program (prepareTime w mag) (.local .constantCopy) (arithmeticData w [] [] mag)
      (.local .dividend) (data {w with constant:=w.scan,scan:=[]}):=by
  have h0:=copy_call .constant (.local .constantCopy) (.local .clearScan) rfl
    (arithmeticData w [] [] mag) w.scan [] rfl hc hs
  simp only [List.append_nil] at h0
  change Runs program _ _ _ _ (Function.update (arithmeticData w [] [] mag) (aux .constant) w.scan) at h0
  rw [arithmeticData_aux_update] at h0
  have h1:=drain_call (.local .clearScan) (.local .clearMagnitude) (aux .scan)
    (arithmeticData {w with constant:=w.scan} [] [] mag) w.scan rfl rfl
  rw [arithmeticData_aux_update] at h1
  have h2:=drain_call (.local .clearMagnitude) (.local .dividend) (arithmetic .output)
    (arithmeticData {w with constant:=w.scan,scan:=[]} [] [] mag) mag rfl rfl
  rw [arithmeticData_output_update,arithmeticData_empty] at h2
  simpa only [prepareTime,SemiprimeD1StackKernelLinearView.set,Nat.add_assoc] using join h0 (join h1 h2)
/-- Exact real quotient word, preserving all original high-zero padding. -/
def quotient (w:Words):List Bool:=(SemiprimeBitDivision.divideLoop w.alpha w.content).quotient
/-- Exact real remainder word, explicitly retained until common cleanup. -/
def remainder (w:Words):List Bool:=(SemiprimeBitDivision.divideLoop w.alpha w.content).remainder
/-- Own complete copies, whole divider and quotient-cache clock. -/
def divideTime (w:Words):Nat:=
  (5*w.alpha.length+4)+(5*w.content.length+4)+
    (SemiprimeD1StackDividerExecution.executionTime w.alpha w.content+1)+(5*(quotient w).length+4)
/-- Actual restoring division obtains the slope, with no quotient/valuation supplied. -/
theorem divide_trace (w:Words) (hs:w.scratch=[]) (hz:w.slope=[]):
    Runs program (divideTime w) (.local .dividend) (data w) (.local .clearDelta)
      (divisionData {w with slope:=quotient w} [] [] (remainder w) (quotient w)):=by
  have h0:=copy_call .alphaDividend (.local .dividend) (.local .divisor) rfl
    (divisionData w [] [] [] []) w.alpha [] rfl rfl hs
  simp only [List.append_nil] at h0
  change Runs program _ _ _ _ (Function.update (divisionData w [] [] [] []) (divider (.inr .input)) w.alpha) at h0
  rw [divisionData_input_update] at h0
  have h1:=copy_call .contentDivisor (.local .divisor) (.local .divide) rfl
    (divisionData w w.alpha [] [] []) w.content [] rfl rfl hs
  simp only [List.append_nil] at h1
  change Runs program _ _ _ _ (Function.update (divisionData w w.alpha [] [] []) (divider (.inr .divisor)) w.content) at h1
  rw [divisionData_divisor_update] at h1
  have h2:=divide_call (.local .divide) (.local .quotient) rfl (words w) w.alpha w.content
  have h3:=copy_call .quotient (.local .quotient) (.local .clearDelta) rfl
    (divisionData w [] [] (remainder w) (quotient w)) (quotient w) [] rfl hz hs
  simp only [List.append_nil] at h3
  change Runs program _ _ _ _ (Function.update (divisionData w [] [] (remainder w) (quotient w)) (aux .slope) (quotient w)) at h3
  rw [divisionData_aux_update] at h3
  simpa only [divideTime,divisionData_empty,SemiprimeD1StackKernelLinearView.set,Nat.add_assoc] using
    join h0 (join h1 (join h2 h3))
end RiemannGaussian.SemiprimeD1StackKernelLinearTail
