/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinearView
import RiemannGaussian.SemiprimeD1StackKernelLinearSpec
/-! # Paid binary center and original-width acquisition from the actual a word -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearPower
open SemiprimeD1StackKernelLinear SemiprimeD1StackKernelLinearPrimitives
open SemiprimeD1StackKernelLinearView SemiprimeD1StackProcedureTrace
/-- Commuting identical literal false bits is a byte equality, not a numeric transport. -/
theorem zeros_commute (n:Nat) (xs:List Bool):
    List.replicate n false++false::xs=false::(List.replicate n false++xs):=by
  induction n with
  | zero=>rfl
  | succ n ih=>simpa only [List.replicate_succ,List.cons_append] using congrArg (List.cons false) ih
/-- Actual metadata-counter loop writes binary powers without numeric unary expansion. -/
theorem power_loop (w:Words) (todo value:List Bool):
    Runs program (2*todo.length+1) (.local .power) (data {w with remaining:=todo,center:=value})
      (.local .copyK) (data {w with remaining:=[],center:=List.replicate todo.length false++value}):=by
  induction todo generalizing value with
  | nil=>
    have h:=pop_run (.local .power) (.local .copyK) (.local .shift) (.local .shift) (aux .remaining)
      (data {w with remaining:=[],center:=value}) [] rfl rfl
    simpa only [List.head?_nil,List.tail_nil,SemiprimeD1StackBytecode.choose,data,bank_aux_update,SemiprimeD1StackKernelLinearView.set,List.length_nil,Nat.mul_zero,Nat.zero_add,List.replicate_zero,List.nil_append] using h
  | cons b todo ih=>
    have h0:=pop_run (.local .power) (.local .copyK) (.local .shift) (.local .shift) (aux .remaining)
      (data {w with remaining:=b::todo,center:=value}) (b::todo) rfl rfl
    simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose,data,bank_aux_update,SemiprimeD1StackKernelLinearView.set] at h0
    have h0':Runs program 1 (.local .power) (data {w with remaining:=b::todo,center:=value})
        (.local .shift) (data {w with remaining:=todo,center:=value}):=by cases b <;> exact h0
    have h1:=push_run (.local .shift) (.local .power) (aux .center) false
      (data {w with remaining:=todo,center:=value}) rfl
    change Runs program 1 _ _ _ (Function.update (data {w with remaining:=todo,center:=value}) (aux .center) (false::value)) at h1
    simp only [data,bank_aux_update,SemiprimeD1StackKernelLinearView.set] at h1
    have h2:=ih (false::value)
    rw [zeros_commute] at h2
    simpa only [List.length_cons,List.replicate_succ,List.cons_append,
      show 2*(todo.length+1)+1=(1+1)+(2*todo.length+1) by omega] using join (join h0' h1) h2
/-- Complete physically acquired center/width words at the arithmetic front door. -/
def result (a t x y:List Bool):Words:=
  {sourceWords a t x y with center:=SemiprimeD1StackKernelLinearSpec.power a.length,k:=true::a}
/-- Every real source copy, binary zero push and counter EOF is included. -/
theorem source_trace (a t x y:List Bool):
    Runs program (12*a.length+11) (.local .start) (data (sourceWords a t x y))
      (.local .centerAdd) (data (result a t x y)):=by
  let w:=sourceWords a t x y
  have h0:=copy_call .aCounter (.local .start) (.local .seed) rfl (data w) a [] rfl rfl rfl
  simp only [copyStack,copyTarget,List.append_nil] at h0
  change Runs program _ _ _ _ (Function.update (data w) (aux .remaining) a) at h0
  simp only [data,bank_aux_update,SemiprimeD1StackKernelLinearView.set] at h0
  have h1:=push_run (.local .seed) (.local .power) (aux .center) true (data {w with remaining:=a}) rfl
  change Runs program 1 _ _ _ (Function.update (data {w with remaining:=a}) (aux .center) [true]) at h1
  simp only [data,bank_aux_update,SemiprimeD1StackKernelLinearView.set] at h1
  have h2:=power_loop w a [true]
  have h3:=copy_call .aK (.local .copyK) (.local .addK) rfl
    (data {w with remaining:=[],center:=SemiprimeD1StackKernelLinearSpec.power a.length}) a [] rfl rfl rfl
  simp only [copyStack,copyTarget,List.append_nil] at h3
  change Runs program _ _ _ _ (Function.update (data {w with remaining:=[],center:=SemiprimeD1StackKernelLinearSpec.power a.length}) (aux .k) a) at h3
  simp only [data,bank_aux_update,SemiprimeD1StackKernelLinearView.set] at h3
  have h4:=push_run (.local .addK) (.local .centerAdd) (aux .k) true
    (data {w with remaining:=[],center:=SemiprimeD1StackKernelLinearSpec.power a.length,k:=a}) rfl
  change Runs program 1 _ _ _ (Function.update (data {w with remaining:=[],center:=SemiprimeD1StackKernelLinearSpec.power a.length,k:=a}) (aux .k) (true::a)) at h4
  simp only [data,bank_aux_update,SemiprimeD1StackKernelLinearView.set] at h4
  have hh:=join h0 (join h1 (join h2 (join h3 h4)))
  simpa only [data,result,w,sourceWords,SemiprimeD1StackKernelLinearSpec.power,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,
    show 12*a.length+11=(5*a.length+4)+1+(2*a.length+1)+(5*a.length+4)+1 by omega] using hh
end RiemannGaussian.SemiprimeD1StackKernelLinearPower
