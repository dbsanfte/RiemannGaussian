/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackScheduleSuccessorBounds

/-! # Exact original schedule successor and uniform prepared-metadata cost
These are the actual dyadic levels and cumulative exponents of the original
recursive counter, at every parameter and depth. Their initial acquisition
from binary N and their recursive caller remain separate obligations.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackScheduleSuccessorOriginal
open SemiprimeD1StackScheduleSuccessor SemiprimeD1StackScheduleSuccessorExecution
open SemiprimeD1StackScheduleSuccessorBounds
namespace S
export SemiprimeD1Schedule (levels exponent previous)
end S
/-- Prepared physical parent schedule words, with no numerical internal state. -/
def parent (lam depth:Nat) : C.State Stack Label :=
  initial (List.replicate (S.exponent lam depth) true) (List.replicate (S.levels lam depth) true)
/-- Exact parent and child metadata after one schedule update. -/
def child (lam depth:Nat) : Stack→List Bool :=
  data (List.replicate (S.exponent lam depth) true) (List.replicate (S.levels lam depth) true)
    [] [] (List.replicate (S.levels lam (depth+1)) true)
    (List.replicate (S.exponent lam (depth+1)) true)
/-- Pairwise physical halving is exactly the original floor-dyadic recurrence. -/
theorem halfWord_original (lam depth:Nat) :
    halfWord (List.replicate (S.levels lam depth) true)=
      List.replicate (S.levels lam (depth+1)) true := by
  simp only [halfWord,List.length_replicate,SemiprimeD1Schedule.levels_succ]
/-- The executed copies add precisely the child taper to the inherited exponent. -/
theorem exponentWord_original (lam depth:Nat) :
    List.replicate (S.levels lam (depth+1)) true++
      List.replicate (S.levels lam (depth+1)) true++List.replicate (S.exponent lam depth) true=
        List.replicate (S.exponent lam (depth+1)) true := by
  rw [←List.replicate_add,←List.replicate_add]
  congr 1
  change S.levels lam (depth+1)+S.levels lam (depth+1)+S.exponent lam depth=
    S.previous lam (depth+1)+2*S.levels lam (depth+1)
  rw [SemiprimeD1Schedule.previous_succ]
  omega
/-- All six physical roles agree with the exact original parent/child schedule. -/
theorem result_original (lam depth:Nat) :
    result (List.replicate (S.exponent lam depth) true) (List.replicate (S.levels lam depth) true)=
      child lam depth := by
  unfold result child
  rw [halfWord_original,exponentWord_original]
/-- Actual original schedule update for every parameter and every depth. -/
theorem source_original (lam depth:Nat) :
    SemiprimeD1StackCalls.run program
      (runTime (List.replicate (S.exponent lam depth) true) (List.replicate (S.levels lam depth) true))
      (parent lam depth)=some (⟨none,none,none,child lam depth,[]⟩:C.State Stack Label) := by
  simpa only [parent,done,result_original] using source_run
    (List.replicate (S.exponent lam depth) true) (List.replicate (S.levels lam depth) true)
/-- Uniform linear prepared-metadata time, independent of recursion depth. -/
theorem original_time (lam depth:Nat) :
    runTime (List.replicate (S.exponent lam depth) true) (List.replicate (S.levels lam depth) true) ≤
      120*(lam+1) := by
  have ht:=runTime_le (List.replicate (S.exponent lam depth) true)
    (List.replicate (S.levels lam depth) true)
  simp only [List.length_replicate] at ht
  have ha:=SemiprimeD1Schedule.exponent_le_lam lam depth
  have hu:=SemiprimeD1Schedule.levels_le lam depth
  omega
/-- The same literal finite machine updates the original schedule within that clock. -/
def originalInTime (lam depth:Nat) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (parent lam depth))
      (some (SemiprimeD1StackCalls.configuration
        (⟨none,none,none,child lam depth,[]⟩:C.State Stack Label))) (120*(lam+1)) := by
  apply SemiprimeD1StackCalls.evalsCorrect Stack.levels Stack.nextExponent (.inl .start) program
  exact ⟨⟨_,source_original lam depth⟩,original_time lam depth⟩
/-- All original-schedule data and return cells remain uniformly linear. -/
theorem original_prefix_cells (lam depth fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (parent lam depth)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 1000*(lam+1) := by
  have h:=machine_prefix_cells (List.replicate (S.exponent lam depth) true)
    (List.replicate (S.levels lam depth) true) fuel cfg hr
  simp only [List.length_replicate] at h
  have ha:=SemiprimeD1Schedule.exponent_le_lam lam depth
  have hu:=SemiprimeD1Schedule.levels_le lam depth
  omega
end RiemannGaussian.SemiprimeD1StackScheduleSuccessorOriginal
