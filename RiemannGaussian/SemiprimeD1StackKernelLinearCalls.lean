/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinearPrimitives
/-! # Actual five-field fitting and eleven-field restoring-division calls -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearCalls
open SemiprimeD1StackKernelLinear SemiprimeD1StackKernelLinearPrimitives
open SemiprimeD1StackProcedureTrace
/-- Exact real fit clock includes its actual caller return. -/
def fitTime (word template:List Bool):Nat:=SemiprimeD1StackWordFitExecution.totalTime word template+1
/-- A complete actual fit changes only its consumed operand and fresh result. -/
theorem fit_call (second:Bool) (pc next:Label) (hc:program pc=.call (.fit second .start) next)
    (before:Stack→List Bool) (word template:List Bool)
    (hi:∀r,before (fitStack second r)=SemiprimeD1StackWordFit.store word template [] [] [] r):
    Runs program (fitTime word template) pc before next
      (Function.update (Function.update before (fitStack second 0) []) (fitStack second 4)
        (SemiprimeD1StackWordFitExecution.result word template)):=by
  let source:=SemiprimeD1StackWordFit.initial word template
  let stop:=SemiprimeD1StackWordFitExecution.done word template
  have hin:Link.DataRel (fitStack second) before source.data before:=⟨hi,fun _ _=>rfl⟩
  have h0:=Link.data_update (fitStack second) (fit_injective second) before source.data before hin (0:Fin 5) []
  have h1:=Link.data_update (fitStack second) (fit_injective second) before
    (Function.update source.data 0 []) (Function.update before (fitStack second 0) []) h0 (4:Fin 5)
    (SemiprimeD1StackWordFitExecution.result word template)
  have he:Function.update (Function.update source.data 0 []) 4 (SemiprimeD1StackWordFitExecution.result word template)=stop.data:=by
    funext r;fin_cases r <;> rfl
  rw [he] at h1
  exact SemiprimeD1StackProcedureCallsTrace.included_call program (fitStack second) (Label.fit second)
    (fit_injective second) F.program .start (fun _=>rfl) pc next hc _ source stop before _ rfl rfl rfl rfl
    (SemiprimeD1StackWordFitExecution.source_run word template) hin h1
/-- Division entry consumes copied operands, preserving every eighteen-role source/cache word. -/
theorem divide_call (pc next:Label) (hc:program pc=.call (.divide (.control .start)) next)
    (u:Aux→List Bool) (xs ys:List Bool):
    Runs program (SemiprimeD1StackDividerExecution.executionTime xs ys+1) pc
      (Sum.elim (SemiprimeD1StackDivider.payload xs ys [] [] [] [] [] [] [] [] []) u) next
      (Sum.elim (SemiprimeD1StackDivider.payload [] [] [] [] [] [] []
        (SemiprimeBitDivision.divideLoop xs ys).remainder (SemiprimeBitDivision.divideLoop xs ys).quotient [] []) u):=by
  let source:=SemiprimeD1StackDivider.state (some (.control .start)) none none xs ys [] [] [] [] [] [] [] [] []
  let stop:=SemiprimeD1StackDivider.state none none none [] [] [] [] [] [] []
    (SemiprimeBitDivision.divideLoop xs ys).remainder (SemiprimeBitDivision.divideLoop xs ys).quotient [] []
  have hi:Link.DataRel divider (Sum.elim source.data u) source.data (Sum.elim source.data u):=⟨fun _=>rfl,fun _ _=>rfl⟩
  have ho:Link.DataRel divider (Sum.elim source.data u) stop.data (Sum.elim stop.data u):=by
    constructor
    · intro r;rfl
    · intro r hr
      rcases r with r|r
      · exact False.elim (hr r rfl)
      · rfl
  exact SemiprimeD1StackProcedureCallsTrace.included_call program divider Label.divide Sum.inl_injective
    D.code (.control .start) (fun _=>rfl) pc next hc _ source stop _ _ rfl rfl rfl rfl
    (SemiprimeD1StackDividerExecution.source_run xs ys) hi ho
end RiemannGaussian.SemiprimeD1StackKernelLinearCalls
