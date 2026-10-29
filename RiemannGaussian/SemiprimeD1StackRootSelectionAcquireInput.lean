/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootSelectionAcquirePrimitives
/-! # Four paid copies from the sole binary input and actual stopped producers -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootSelectionAcquireInput
open SemiprimeD1StackRootSelectionAcquire SemiprimeD1StackRootSelectionAcquireView
open SemiprimeD1StackRootSelectionAcquirePrimitives SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- The actual parameter source initially has only its original binary input populated. -/
theorem parameter_input (bits:List Bool) (k:P.Stack) :
    (P.initial bits).data k=(if k=P.originalInput then bits else []) :=by
  have hi:=SemiprimeD1StackCalls.initial_correct P.originalInput
    SemiprimeD1StackRootParameters.leaf (.inl .start) P.program bits
  have he:=hi.trans (SemiprimeD1StackRootParametersBounds.initial_eq bits)
  exact (congrArg (fun cfg:SemiprimeD1StackRootParameters.machine.Cfg=>cfg.stk (some k)) he).symm
/-- The sole binary-N handoff is an actual preserving copy before both producers run. -/
theorem number_input_run (bits:List Bool) :
    Runs program (5*bits.length+4) (ctl (.copy .number)) (input bits) (ctl .parameters)
      (data (R.initial bits).data (P.initial bits).data (fun _=>[])) :=by
  have hx:(R.initial bits).data R.originalInput=bits:=by
    change R.input bits R.originalInput=bits
    rw [SemiprimeD1StackRootNetworkRowsResources.input_single]
    simp only [ite_true]
  have h:=copy_call .number (data (R.initial bits).data (fun _=>[]) (fun _=>[])) bits [] hx rfl rfl
  simp only [List.append_nil] at h
  change Runs program _ _ _ (ctl .parameters)
    (Function.update (data (R.initial bits).data (fun _=>[]) (fun _=>[])) (parameterStack P.originalInput) bits) at h
  rw [data_parameters] at h
  have he:Function.update (fun _=>[]) P.originalInput bits=(P.initial bits).data:=by
    funext k
    rw [parameter_input]
    simp only [Function.update_apply]
  rw [he] at h
  exact h
/-- Exactly three physical selection-source inputs after the actual producer handoffs. -/
def acquisitionReady (root:R.Stack→List Bool) (parameters:P.Stack→List Bool) :Q.Stack→List Bool :=
  Function.update (Function.update (Function.update (fun _=>[])
    (Q.occurrenceStack .rows) (root R.output))
    (Q.occurrenceStack .number) (root R.leftCount))
    (Q.alphabetStack (SemiprimeD1StackSourceAlphabet64.aux .source)) (parameters P.exponent)
/-- The three actual writes give exactly the honest physical three-input source bank. -/
theorem acquisitionReady_input (root:R.Stack→List Bool) (parameters:P.Stack→List Bool) :
    acquisitionReady root parameters=
      (Q.initial (root R.output) (root R.leftCount) (parameters P.exponent)).data :=by
  funext k
  rcases k with k|k
  · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · rfl
      · cases k <;> rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k <;> rfl
/-- Every actual producer byte pays its real preserving-copy and return cost. -/
def acquisitionCopyTime (root:R.Stack→List Bool) (parameters:P.Stack→List Bool) :Nat :=
  5*((root R.output).length+(root R.leftCount).length+(parameters P.exponent).length)+12
/-- All three stopped-producer handoffs execute physically, preserving both complete producer banks. -/
theorem acquisition_input_run (root:R.Stack→List Bool) (parameters:P.Stack→List Bool) :
    Runs program (acquisitionCopyTime root parameters) (ctl (.copy .rows))
      (data root parameters (fun _=>[])) (ctl .acquire) (data root parameters (acquisitionReady root parameters)) :=by
  let s0:Q.Stack→List Bool:=fun _=>[]
  let s1:=Function.update s0 (Q.occurrenceStack .rows) (root R.output)
  let s2:=Function.update s1 (Q.occurrenceStack .number) (root R.leftCount)
  let s3:=Function.update s2 (Q.alphabetStack (SemiprimeD1StackSourceAlphabet64.aux .source)) (parameters P.exponent)
  have h0:=copy_call .rows (data root parameters s0) (root R.output) [] rfl rfl rfl
  simp only [List.append_nil] at h0
  change Runs program _ _ _ _
    (Function.update (data root parameters s0) (acquisitionStack (Q.occurrenceStack .rows)) (root R.output)) at h0
  rw [data_acquisition] at h0
  have h1:=copy_call .owners (data root parameters s1) (root R.leftCount) [] rfl rfl rfl
  simp only [List.append_nil] at h1
  change Runs program _ _ _ _
    (Function.update (data root parameters s1) (acquisitionStack (Q.occurrenceStack .number)) (root R.leftCount)) at h1
  rw [data_acquisition] at h1
  have h2:=copy_call .dimension (data root parameters s2) (parameters P.exponent) [] rfl rfl rfl
  simp only [List.append_nil] at h2
  change Runs program _ _ _ _
    (Function.update (data root parameters s2)
      (acquisitionStack (Q.alphabetStack (SemiprimeD1StackSourceAlphabet64.aux .source))) (parameters P.exponent)) at h2
  rw [data_acquisition] at h2
  have h:=join (join h0 h1) h2
  change Runs program _ _ _ (ctl .acquire) _ at h
  change Runs program _ _ _ _ (data root parameters s3)
  convert h using 1
  unfold acquisitionCopyTime
  omega
end RiemannGaussian.SemiprimeD1StackRootSelectionAcquireInput
