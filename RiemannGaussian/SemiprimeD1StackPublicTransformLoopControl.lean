/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformQueryClosure
/-! # Physical countdown and terminal cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformLoopControl
open SemiprimeD1StackPublicTransform SemiprimeD1StackPublicTransformState
open SemiprimeD1StackPublicTransformLoopState SemiprimeD1StackPublicTransformPrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeD1StackUnaryDivmod (unary)
/-- Actual pop, drain and restoring copy prepare a descending output query. -/
theorem prepare (bits raw : List Bool) (second inverse : Bool) (n f : ℕ) :
    Runs program (1+(f+1)+(5*n+4)) .loop (data (steady bits raw second inverse (n+1) f))
      .evaluate (data (steady bits raw second inverse n n)) := by
  have h0:=pop .loop .accept .clearFrequency .clearFrequency (.aux .remaining) rfl
    (data (steady bits raw second inverse (n+1) f))
  rw [remaining_value] at h0
  simp only [unary,List.replicate_succ,List.head?_cons,List.tail_cons,
    SemiprimeD1StackBytecode.choose] at h0
  change Runs program 1 .loop _ .clearFrequency
    (Function.update (data (steady bits raw second inverse (n+1) f)) (.aux .remaining) (unary n)) at h0
  rw [remaining_update] at h0
  have h1:=drain .clearFrequency .copyFrequency (.dot (.inl .frequency)) rfl
    (data (steady bits raw second inverse n f))
  rw [frequency_value] at h1
  change Runs program ((unary f).length+1) .clearFrequency _ .copyFrequency
    (Function.update (data (steady bits raw second inverse n f)) (.dot (.inl .frequency)) (unary 0)) at h1
  rw [frequency_update] at h1
  have h2:=copy_call .frequency .copyFrequency .evaluate rfl
    (data (steady bits raw second inverse n 0)) (frequency_value bits raw second inverse n 0)
    (steady_scratch bits raw second inverse n 0)
  change Runs program (5*(data (steady bits raw second inverse n 0) (.aux .remaining)).length+4)
    .copyFrequency _ .evaluate
    (Function.update (data (steady bits raw second inverse n 0)) (.dot (.inl .frequency))
      (data (steady bits raw second inverse n 0) (.aux .remaining))) at h2
  rw [remaining_value,frequency_update] at h2
  simpa only [unary,List.length_replicate] using
    runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
/-- Actual EOF selects acceptance. -/
theorem empty (bits raw : List Bool) (second inverse : Bool) (f : ℕ) :
    Runs program 1 .loop (data (steady bits raw second inverse 0 f)) .accept
      (data (steady bits raw second inverse 0 f)) := by
  have h:=pop .loop .accept .clearFrequency .clearFrequency (.aux .remaining) rfl
    (data (steady bits raw second inverse 0 f))
  rw [remaining_value] at h
  simp only [unary,List.replicate_zero,List.head?_nil,List.tail_nil,
    SemiprimeD1StackBytecode.choose] at h
  have he : data (steady bits raw second inverse 0 f) (.aux .remaining)=[] := remaining_value bits raw second inverse 0 f
  rw [←he,Function.update_eq_self] at h
  exact h
/-- Literal final output and marker cleanup. -/
def finished (p : Parts) (answer : Bool) : Parts :=
  set (set (set p (.aux .output) [answer]) (.aux .remaining) []) (.dot (.inl .frequency)) []
/-- Every remaining cell is physically popped before halt. -/
theorem finish (p : Parts) (answer : Bool) (ho : data p (.aux .output)=[]) :
    Runs program (1+((data p (.aux .remaining)).length+1)+((data p (.dot (.inl .frequency))).length+1))
      (if answer then .accept else .reject) (data p) .done (data (finished p answer)) := by
  have h0 : Runs program 1 (if answer then .accept else .reject) (data p) .clearRemaining
      (Function.update (data p) (.aux .output) [answer]) := by
    cases answer
    · simpa only [Bool.false_eq_true,ite_false,ho] using
        push .reject .clearRemaining (.aux .output) false rfl (data p)
    · simpa only [ite_true,ho] using
        push .accept .clearRemaining (.aux .output) true rfl (data p)
  have h1:=drain .clearRemaining .clearFinalFrequency (.aux .remaining) rfl
    (Function.update (data p) (.aux .output) [answer])
  have h2:=drain .clearFinalFrequency .done (.dot (.inl .frequency)) rfl
    (Function.update (Function.update (data p) (.aux .output) [answer]) (.aux .remaining) [])
  have h:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
  simpa only [finished,data_set,Function.update_of_ne (by decide : Stack.aux .remaining≠.aux .output),
    Function.update_of_ne (by decide : Stack.dot (.inl .frequency)≠.aux .remaining),
    Function.update_of_ne (by decide : Stack.dot (.inl .frequency)≠.aux .output)] using h
/-- Terminal data is independent of the last physical countdown values. -/
theorem finished_steady (bits raw : List Bool) (second inverse answer : Bool) (n f : ℕ) :
    data (finished (steady bits raw second inverse n f) answer)=
      data (finished (steady bits raw second inverse 0 0) answer) := by
  simp only [finished,data_set,steady_data]
  funext k
  by_cases h0 : k=Stack.dot (.inl .frequency)
  · subst k; simp only [Function.update_same]
  by_cases h1 : k=Stack.aux .remaining
  · subst k; simp only [Function.update_of_ne (by decide : Stack.aux .remaining≠.dot (.inl .frequency)),Function.update_same]
  by_cases h2 : k=Stack.aux .output
  · subst k; simp only [Function.update_of_ne (by decide : Stack.aux .output≠.dot (.inl .frequency)),
      Function.update_of_ne (by decide : Stack.aux .output≠.aux .remaining),Function.update_same]
  simp only [Function.update_of_ne h0,Function.update_of_ne h1,Function.update_of_ne h2]
end RiemannGaussian.SemiprimeD1StackPublicTransformLoopControl
