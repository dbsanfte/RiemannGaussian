/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformOriginal
/-! # Closed original-input transform execution
The executing program takes only binary N, raw assignment bytes and two finite
stage/direction flags. Every source, vector, guard and query is actually run.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformTraceBudget
open SemiprimeD1StackPublicTransform SemiprimeD1StackPublicTransformState
open SemiprimeD1StackPublicTransformSetup SemiprimeD1StackPublicTransformWords
open SemiprimeD1StackPublicTransformGuards SemiprimeD1StackPublicTransformMetadata
open SemiprimeD1StackPublicTransformLoopState SemiprimeD1StackPublicTransformLoopControl
open SemiprimeD1StackProcedureTrace SemiprimeBitArithmetic
open SemiprimeD1StackPublicTransformExecution
/-- Sum of retained source/vector/guard/query budgets, not an assumed clock. -/
def timeBound (bits raw : List Bool) (second inverse : Bool) : ℕ :=
  SemiprimeD1StackRootSourceBounds.timeBound bits+1+2+
    metadataBudget (rootData bits) second inverse+normalizationBudget (rootData bits) second inverse+
    wordsBudget (rootData bits) raw second+frontBudget (rootData bits) raw second+
    (if acceptedInputs bits raw second then
      SemiprimeD1StackPublicTransformLoop.budget bits raw second inverse (size bits second) 0 else 0)+3
/-- Whole real source trace with no supplied words, canonicality, root,
normalizer, evaluator, count, equality verdict or component clock. -/
theorem source_run_bounded (bits raw : List Bool) (second inverse : Bool)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    ∃t≤timeBound bits raw second inverse,Runs program t .start (initial bits raw second inverse).data .done
      (data (finalParts bits raw second inverse)) := by
  have hb : bits≠[] := by intro h;subst bits;exact (Nat.lt_irrefl 0 hN)
  obtain ⟨t,ht,h0⟩:=acquire_run bits raw second inverse hb
  obtain ⟨u,hu,h1⟩:=words_run (rootData bits) raw second inverse
  obtain ⟨v,hv,h2⟩:=front_run (rootData bits) raw second inverse
  have front:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
  cases hi : inputFlag (rootData bits) raw second with
  | false=>
    simp only [hi,Bool.false_and] at front
    have hfinish:=finish (frontResult (rootData bits) raw second inverse) false (by
      simp only [frontResult,hi,Bool.false_eq_true,ite_false]
      rfl)
    have hr : data (frontResult (rootData bits) raw second inverse) (.aux .remaining)=[] := by
      simp only [frontResult,hi,Bool.false_eq_true,ite_false];rfl
    have hf : data (frontResult (rootData bits) raw second inverse) (.dot (.inl .frequency))=[] := by
      simp only [frontResult,hi,Bool.false_eq_true,ite_false];rfl
    rw [hr,hf] at hfinish
    norm_num only [List.length_nil] at hfinish
    have h:=runs_trans program _ _ _ _ _ _ _ _ front hfinish
    exact ⟨t+u+v+3,by unfold timeBound; simp only [acceptedInputs,hi,Bool.false_and,Bool.false_eq_true,ite_false];omega,by simpa only [finalParts,acceptedInputs,hi,Bool.false_and,Bool.false_eq_true,ite_false] using h⟩
  | true=>
    cases ho : outputFlag (rootData bits) raw second with
    | false=>
      simp only [hi,ho,Bool.true_and] at front
      have hfinish:=finish (frontResult (rootData bits) raw second inverse) false (by
        simp only [frontResult,hi,ho,ite_true,Bool.false_eq_true,ite_false]
        rfl)
      have hr : data (frontResult (rootData bits) raw second inverse) (.aux .remaining)=[] := by
        simp only [frontResult,hi,ho,ite_true,Bool.false_eq_true,ite_false];rfl
      have hf : data (frontResult (rootData bits) raw second inverse) (.dot (.inl .frequency))=[] := by
        simp only [frontResult,hi,ho,ite_true,Bool.false_eq_true,ite_false];rfl
      rw [hr,hf] at hfinish
      norm_num only [List.length_nil] at hfinish
      have h:=runs_trans program _ _ _ _ _ _ _ _ front hfinish
      exact ⟨t+u+v+3,by unfold timeBound; simp only [acceptedInputs,hi,ho,Bool.true_and,Bool.false_eq_true,ite_false];omega,by simpa only [finalParts,acceptedInputs,hi,ho,Bool.true_and,Bool.false_eq_true,ite_false] using h⟩
    | true=>
      simp only [hi,ho,Bool.true_and,ite_true,frontResult] at front
      obtain ⟨w,hw,hloop⟩:=SemiprimeD1StackPublicTransformLoop.loop_run bits raw second inverse hc hN hi (size bits second) 0
      rw [loop_initial] at hloop
      have h:=runs_trans program _ _ _ _ _ _ _ _ front hloop
      exact ⟨t+u+v+w,by unfold timeBound; simp only [acceptedInputs,hi,ho,Bool.true_and,ite_true];omega,by simpa only [finalParts,acceptedInputs,hi,ho,Bool.true_and,ite_true] using h⟩
end RiemannGaussian.SemiprimeD1StackPublicTransformTraceBudget
