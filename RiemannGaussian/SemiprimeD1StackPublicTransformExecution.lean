/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformLoop
/-! # Closed original-input transform execution
The executing program takes only binary N, raw assignment bytes and two finite
stage/direction flags. Every source, vector, guard and query is actually run.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformExecution
open SemiprimeD1StackPublicTransform SemiprimeD1StackPublicTransformState
open SemiprimeD1StackPublicTransformSetup SemiprimeD1StackPublicTransformWords
open SemiprimeD1StackPublicTransformGuards SemiprimeD1StackPublicTransformMetadata
open SemiprimeD1StackPublicTransformLoopState SemiprimeD1StackPublicTransformLoopControl
open SemiprimeD1StackProcedureTrace SemiprimeBitArithmetic
/-- Actual short-circuit frontend verdict. -/
def acceptedInputs (bits raw : List Bool) (second : Bool) : Bool :=
  inputFlag (rootData bits) raw second && outputFlag (rootData bits) raw second
/-- Specification of the final physical data, including retained actual caches. -/
def finalParts (bits raw : List Bool) (second inverse : Bool) : Parts :=
  if acceptedInputs bits raw second then
    finished (steady bits raw second inverse 0 0)
      (SemiprimeD1StackPublicTransformLoop.answer bits raw second inverse (size bits second))
  else finished (frontResult (rootData bits) raw second inverse) false
/-- Whole real source trace with no supplied words, canonicality, root,
normalizer, evaluator, count, equality verdict or component clock. -/
theorem source_run (bits raw : List Bool) (second inverse : Bool)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    ∃t,Runs program t .start (initial bits raw second inverse).data .done
      (data (finalParts bits raw second inverse)) := by
  have hb : bits≠[] := by intro h;subst bits;exact (Nat.lt_irrefl 0 hN)
  obtain ⟨t,_,h0⟩:=acquire_run bits raw second inverse hb
  obtain ⟨u,_,h1⟩:=words_run (rootData bits) raw second inverse
  obtain ⟨v,_,h2⟩:=front_run (rootData bits) raw second inverse
  have front:=runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
  cases hi : inputFlag (rootData bits) raw second with
  | false=>
    simp only [hi,Bool.false_and] at front
    have hfinish:=finish (frontResult (rootData bits) raw second inverse) false (by
      simp only [frontResult,hi,Bool.false_eq_true,ite_false]
      rfl)
    have h:=runs_trans program _ _ _ _ _ _ _ _ front hfinish
    exact ⟨_,by simpa only [finalParts,acceptedInputs,hi,Bool.false_and,Bool.false_eq_true,ite_false] using h⟩
  | true=>
    cases ho : outputFlag (rootData bits) raw second with
    | false=>
      simp only [hi,ho,Bool.true_and] at front
      have hfinish:=finish (frontResult (rootData bits) raw second inverse) false (by
        simp only [frontResult,hi,ho,ite_true,Bool.false_eq_true,ite_false]
        rfl)
      have h:=runs_trans program _ _ _ _ _ _ _ _ front hfinish
      exact ⟨_,by simpa only [finalParts,acceptedInputs,hi,ho,Bool.true_and,Bool.false_eq_true,ite_false] using h⟩
    | true=>
      simp only [hi,ho,Bool.true_and,ite_true,frontResult] at front
      obtain ⟨w,_,hloop⟩:=SemiprimeD1StackPublicTransformLoop.loop_run bits raw second inverse hc hN hi (size bits second) 0
      rw [loop_initial] at hloop
      have h:=runs_trans program _ _ _ _ _ _ _ _ front hloop
      exact ⟨_,by simpa only [finalParts,acceptedInputs,hi,ho,Bool.true_and,ite_true] using h⟩
end RiemannGaussian.SemiprimeD1StackPublicTransformExecution
