/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinearPrimitives
/-! # Real low-zero stripping, retaining exact padded positive suffixes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearStrip
open SemiprimeD1StackKernelLinear SemiprimeD1StackKernelLinearPrimitives
open SemiprimeD1StackProcedureTrace
/-- Proof view of the two actual fields touched by the physical strip loop. -/
def data (before:Stack→List Bool) (scan content:List Bool):Stack→List Bool:=
  Function.update (Function.update before (aux .scan) scan) (aux .content) content
/-- The actual source word of the strip loop. -/
theorem data_scan (before:Stack→List Bool) (scan content:List Bool):data before scan content (aux .scan)=scan:=by simp [data,aux]
/-- The actual binary shifted-one construction field. -/
theorem data_content (before:Stack→List Bool) (scan content:List Bool):data before scan content (aux .content)=content:=by simp [data]
/-- A physical source pop changes only the actual scan field. -/
theorem data_scan_update (before:Stack→List Bool) (scan content tail:List Bool):
    Function.update (data before scan content) (aux .scan) tail=data before tail content:=by
  funext r
  by_cases hs:r=aux .scan
  · subst r;simp [data,aux]
  · by_cases hc:r=aux .content
    · subst r;simp [data,aux]
    · simp [data,Function.update_of_ne hs,Function.update_of_ne hc]
/-- A physical zero push changes only the constructed content. -/
theorem data_content_update (before:Stack→List Bool) (scan content tail:List Bool):
    Function.update (data before scan content) (aux .content) tail=data before scan tail:=by
  simp only [data,Function.update_idem]
/-- Actual two-step false stripping, including the paid shifted-one extension. -/
theorem false_step (before:Stack→List Bool) (scan content:List Bool):
    Runs program 2 (.local .strip) (data before (false::scan) content) (.local .strip)
      (data before scan (false::content)):=by
  have h0:=pop_run (.local .strip) (.local .zeroContent) (.local .shiftContent) (.local .restoreOne)
    (aux .scan) (data before (false::scan) content) (false::scan) rfl (data_scan _ _ _)
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
  rw [data_scan_update] at h0
  have h1:=push_run (.local .shiftContent) (.local .strip) (aux .content) false (data before scan content) rfl
  rw [data_content,data_content_update] at h1
  exact join h0 h1
/-- Every physical low-zero prefix is visited; neither its length nor valuation is supplied to runtime. -/
theorem prefix_run (n:Nat) (before:Stack→List Bool) (scan content:List Bool):
    Runs program (2*n) (.local .strip) (data before (List.replicate n false++scan) content)
      (.local .strip) (data before scan (List.replicate n false++content)):=by
  induction n generalizing content with
  | zero=>exact runs_refl program _ _
  | succ n ih=>
    have h0:=false_step before (List.replicate n false++scan) content
    have h1:=ih (false::content)
    have he:List.replicate n false++false::content=false::(List.replicate n false++content):=by
      calc
        List.replicate n false++false::content=(List.replicate n false++[false])++content:=by simp only [List.append_assoc,List.singleton_append]
        _=List.replicate (n+1) false++content:=by rw [←List.replicate_one (a:=false),←List.replicate_add]
        _=false::(List.replicate n false++content):=rfl
    rw [he] at h1
    simpa only [List.replicate_succ,List.cons_append,show 2*(n+1)=2+2*n by omega] using join h0 h1
/-- The first real one is popped and physically restored, preserving ALL high padding. -/
theorem one_run (before:Stack→List Bool) (scan content:List Bool):
    Runs program 2 (.local .strip) (data before (true::scan) content) (.local .constantCopy)
      (data before (true::scan) content):=by
  have h0:=pop_run (.local .strip) (.local .zeroContent) (.local .shiftContent) (.local .restoreOne)
    (aux .scan) (data before (true::scan) content) (true::scan) rfl (data_scan _ _ _)
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
  rw [data_scan_update] at h0
  have h1:=push_run (.local .restoreOne) (.local .constantCopy) (aux .scan) true (data before scan content) rfl
  rw [data_scan,data_scan_update] at h1
  exact join h0 h1
/-- The all-zero padded branch is selected by the ACTUAL final EOF pop. -/
theorem empty_run (before:Stack→List Bool) (content:List Bool):
    Runs program 1 (.local .strip) (data before [] content) (.local .zeroContent) (data before [] content):=by
  have h:=pop_run (.local .strip) (.local .zeroContent) (.local .shiftContent) (.local .restoreOne)
    (aux .scan) (data before [] content) [] rfl (data_scan _ _ _)
  simpa only [List.head?_nil,List.tail_nil,SemiprimeD1StackBytecode.choose,data_scan_update] using h
end RiemannGaussian.SemiprimeD1StackKernelLinearStrip
