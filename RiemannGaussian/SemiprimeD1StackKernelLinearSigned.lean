/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinearView
import RiemannGaussian.SemiprimeD1StackKernelLinearSpec
/-! # Original-orientation signed factor subtraction with paid reverse branch -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearSigned
open SemiprimeD1StackKernelLinear SemiprimeD1StackKernelLinearPrimitives
open SemiprimeD1StackKernelLinearView SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic SemiprimeBitDivision
/-- Own actual first subtraction clock includes both copies, borrow and sign. -/
def firstTime (w:Words):Nat:=(5*w.j.length+4)+(5*w.displacement.length+4)+subTime w.j w.displacement+2
/-- Actual first subtraction and sign push, before any reverse subtraction. -/
theorem first_trace (w:Words) (hs:w.scratch=[]) (hz:w.sign=[]) (negative:Bool)
    (hb:(subBits w.j w.displacement false).borrow=negative):
    Runs program (firstTime w) (.local .normalize) (data w)
      (.local (if negative then .clearWrapped else .deltaCopy))
      (arithmeticData {w with sign:=[negative]} [] [] (subBits w.j w.displacement false).result.bits):=by
  have h0:=copy_call .jLeft (.local .normalize) (.local .dRight) rfl
    (arithmeticData w [] [] []) w.j [] rfl rfl hs
  simp only [List.append_nil] at h0
  change Runs program _ _ _ _ (Function.update (arithmeticData w [] [] []) (arithmetic .left) w.j) at h0
  rw [arithmeticData_left_update] at h0
  have h1:=copy_call .dRight (.local .dRight) (.local .firstSub) rfl
    (arithmeticData w w.j [] []) w.displacement [] rfl rfl hs
  simp only [List.append_nil] at h1
  change Runs program _ _ _ _ (Function.update (arithmeticData w w.j [] []) (arithmetic .right) w.displacement) at h1
  rw [arithmeticData_right_update] at h1
  have h2:=sub_call (.local .firstSub) (.local .firstBorrow) rfl (fun _=>[]) (words w) w.j w.displacement
  have h3:=pop_run (.local .firstBorrow) (.local .abort) (.local (.sign false)) (.local (.sign true))
    (arithmetic .output) (arithmeticData w [] [] ((subBits w.j w.displacement false).borrow::(subBits w.j w.displacement false).result.bits))
    ((subBits w.j w.displacement false).borrow::(subBits w.j w.displacement false).result.bits) rfl rfl
  simp only [List.head?_cons,List.tail_cons,arithmeticData_output_update] at h3
  have h3':Runs program 1 (.local .firstBorrow)
      (arithmeticData w [] [] ((subBits w.j w.displacement false).borrow::(subBits w.j w.displacement false).result.bits))
      (.local (.sign negative)) (arithmeticData w [] [] (subBits w.j w.displacement false).result.bits):=by
    cases negative <;> simpa only [hb,SemiprimeD1StackBytecode.choose] using h3
  have h4:=push_run (.local (.sign negative)) (.local (if negative then .clearWrapped else .deltaCopy))
    (aux .sign) negative (arithmeticData w [] [] (subBits w.j w.displacement false).result.bits) rfl
  change Runs program 1 _ _ _ (Function.update (arithmeticData w [] [] (subBits w.j w.displacement false).result.bits)
    (aux .sign) (negative::w.sign)) at h4
  rw [hz,arithmeticData_aux_update] at h4
  have hh:=join h0 (join h1 (join h2 (join h3' h4)))
  simpa only [firstTime,arithmeticData_empty,SemiprimeD1StackKernelLinearView.set,Nat.add_assoc] using hh
/-- Own reverse-branch time pays the failed original magnitude and second subtraction. -/
def reverseTime (w:Words) (wrapped:List Bool):Nat:=
  (wrapped.length+3)+(5*w.displacement.length+4)+(5*w.j.length+4)+subTime w.displacement w.j+1
/-- The reverse subtraction is physically executed after a real failed borrow. -/
theorem reverse_trace (w:Words) (hs:w.scratch=[]) (wrapped:List Bool)
    (hb:(subBits w.displacement w.j false).borrow=false):
    Runs program (reverseTime w wrapped) (.local .clearWrapped) (arithmeticData w [] [] wrapped)
      (.local .deltaCopy) (arithmeticData w [] [] (subBits w.displacement w.j false).result.bits):=by
  have h0:=drain_call (.local .clearWrapped) (.local .dLeft) (arithmetic .output)
    (arithmeticData w [] [] wrapped) wrapped rfl rfl
  rw [arithmeticData_output_update] at h0
  have h1:=copy_call .dLeft (.local .dLeft) (.local .jRight) rfl
    (arithmeticData w [] [] []) w.displacement [] rfl rfl hs
  simp only [List.append_nil] at h1
  change Runs program _ _ _ _ (Function.update (arithmeticData w [] [] []) (arithmetic .left) w.displacement) at h1
  rw [arithmeticData_left_update] at h1
  have h2:=copy_call .jRight (.local .jRight) (.local .secondSub) rfl
    (arithmeticData w w.displacement [] []) w.j [] rfl rfl hs
  simp only [List.append_nil] at h2
  change Runs program _ _ _ _ (Function.update (arithmeticData w w.displacement [] []) (arithmetic .right) w.j) at h2
  rw [arithmeticData_right_update] at h2
  have h3:=sub_call (.local .secondSub) (.local .secondBorrow) rfl (fun _=>[]) (words w) w.displacement w.j
  rw [hb] at h3
  have h4:=pop_run (.local .secondBorrow) (.local .abort) (.local .deltaCopy) (.local .abort)
    (arithmetic .output) (arithmeticData w [] [] (false::(subBits w.displacement w.j false).result.bits))
    (false::(subBits w.displacement w.j false).result.bits) rfl rfl
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose,arithmeticData_output_update] at h4
  simpa only [reverseTime,Nat.add_assoc] using join h0 (join h1 (join h2 (join h3 h4)))
/-- The original failed borrow makes the physically reversed subtraction safe. -/
theorem reverse_borrow (j d:List Bool) (h:(subBits j d false).borrow=true):
    (subBits d j false).borrow=false:=by
  have ht:bitValue j<bitValue d:=by
    simpa only [bitNat,Bool.false_eq_true,ite_false,Nat.add_zero] using (subBits_borrow_iff j d false).mp h
  cases hb:(subBits d j false).borrow with
  | false=>rfl
  | true=>
    have hh:bitValue d<bitValue j:=by
      simpa only [bitNat,Bool.false_eq_true,ite_false,Nat.add_zero] using (subBits_borrow_iff d j false).mp hb
    omega
/-- Own complete signed-subtraction clock uses only actually executed fragments. -/
def timeBound (w:Words):Nat:=firstTime w+
  if SemiprimeD1StackKernelLinearSpec.negative w.j w.displacement then
    reverseTime {w with sign:=[true]} (subBits w.j w.displacement false).result.bits else 0
/-- Exact original signed magnitude bytes, including negative/zero/padded branches. -/
theorem source_trace (w:Words) (hs:w.scratch=[]) (hz:w.sign=[]):
    Runs program (timeBound w) (.local .normalize) (data w) (.local .deltaCopy)
      (arithmeticData {w with sign:=[SemiprimeD1StackKernelLinearSpec.negative w.j w.displacement]} [] []
        (SemiprimeD1StackKernelLinearSpec.magnitude w.j w.displacement)):=by
  cases hb:(subBits w.j w.displacement false).borrow with
  | false=>
    have h:=first_trace w hs hz false hb
    simpa only [timeBound,SemiprimeD1StackKernelLinearSpec.negative,SemiprimeD1StackKernelLinearSpec.magnitude,
      hb,Bool.false_eq_true,ite_false,Nat.add_zero] using h
  | true=>
    have h0:=first_trace w hs hz true hb
    have h1:=reverse_trace {w with sign:=[true]} hs (subBits w.j w.displacement false).result.bits
      (reverse_borrow w.j w.displacement hb)
    simpa only [timeBound,SemiprimeD1StackKernelLinearSpec.negative,SemiprimeD1StackKernelLinearSpec.magnitude,
      hb,ite_true] using join h0 h1
end RiemannGaussian.SemiprimeD1StackKernelLinearSigned
