/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecursiveScheduleBounds
import RiemannGaussian.SemiprimeD1RecursiveCounter

/-! # Whole-family original recursive schedule front end
The actual guard verdict equals the native recursive counter's branch; on
active calls the actual child schedule equals its exact dyadic recurrence.
This is a prepared-metadata controller fragment, not the full recursive counter.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackRecursiveScheduleOriginal
open SemiprimeD1StackRecursiveSchedule SemiprimeD1StackRecursiveScheduleExecution
open SemiprimeD1StackRecursiveScheduleBounds
namespace AO
export SemiprimeD1StackScheduleActiveOriginal (values answer_original volume_original)
end AO
namespace SO
export SemiprimeD1StackScheduleSuccessorOriginal (child result_original)
end SO
namespace P
export SemiprimeD1Schedule (levels exponent)
end P
/-- Exact original cumulative exponent word; bounded metadata is explicitly paid. -/
def exponentWord (lam depth:Nat) : List Bool := List.replicate (P.exponent lam depth) true
/-- Actual physical verdict equals the original recursive controller's Boolean branch. -/
theorem answer_native (s lam depth M:Nat) : A.answer (AO.values s lam depth M)=
    SemiprimeD1RecursiveCounter.activeTest s lam depth M := by
  apply Bool.eq_iff_iff.mpr
  rw [AO.answer_original,decide_eq_true_eq,SemiprimeD1RecursiveCounter.activeTest_correct]
/-- Exact original conditional physical payload, including all retained guard words. -/
def originalResult (s lam depth M:Nat) : Stack→List Bool :=
  if SemiprimeD1RecursiveCounter.activeTest s lam depth M then
    payload (A.done (AO.values s lam depth M)).data (SO.child lam depth)
  else ready (exponentWord lam depth) (AO.values s lam depth M)
/-- Active calls acquire exactly the original child level and exponent words. -/
theorem successor_original (s lam depth M:Nat) :
    afterSuccessor (exponentWord lam depth) (AO.values s lam depth M)=
      payload (A.done (AO.values s lam depth M)).data (SO.child lam depth) := by
  unfold afterSuccessor
  change payload (A.done (AO.values s lam depth M)).data
    (S.result (List.replicate (P.exponent lam depth) true) (List.replicate (P.levels lam depth) true))=_
  rw [SO.result_original]
/-- The same-program result covers both original branches for every size and depth. -/
theorem result_original (s lam depth M:Nat) :
    result (exponentWord lam depth) (AO.values s lam depth M)=originalResult s lam depth M := by
  unfold result originalResult
  rw [answer_native,successor_original]
/-- Same actual complete clock, uniformly linear in all original bounded metadata. -/
theorem original_time (s lam depth M:Nat) :
    runBound (exponentWord lam depth) (AO.values s lam depth M) ≤ 10000*(s+lam+M+1) := by
  have hv:=AO.volume_original s lam depth M
  have ha:=SemiprimeD1Schedule.exponent_le_lam lam depth
  simp only [runBound,exponentWord,List.length_replicate]
  omega
/-- Complete actual front-end trace, including conditional acquisition and final halt. -/
theorem source_original (s lam depth M:Nat) :
    ∃t≤10000*(s+lam+M+1),SemiprimeD1StackCalls.run program t
      (initial (exponentWord lam depth) (AO.values s lam depth M))=
      some (⟨none,none,none,originalResult s lam depth M,[]⟩:C.State Stack Label) := by
  obtain ⟨t,ht,hr⟩:=source_run (exponentWord lam depth) (AO.values s lam depth M)
  refine ⟨t,ht.trans (original_time s lam depth M),?_⟩
  simpa only [done,result_original] using hr
/-- The useful Boolean output is the original recursive controller's actual guard. -/
theorem verdict_original (s lam depth M:Nat) :
    (done (exponentWord lam depth) (AO.values s lam depth M)).data (guardStack .output)=
      [SemiprimeD1RecursiveCounter.activeTest s lam depth M] := by
  change result (exponentWord lam depth) (AO.values s lam depth M) (guardStack .output)=_
  unfold result
  split <;> simp only [afterSuccessor,ready,guardStack,payload,
    SemiprimeD1StackScheduleActiveExecution.done,SemiprimeD1StackScheduleActive.data,answer_native]
/-- Inactive calls leave the child level output empty; active calls compute its exact word. -/
theorem child_levels_original (s lam depth M:Nat) :
    (done (exponentWord lam depth) (AO.values s lam depth M)).data (successorStack .nextLevels)=
      if SemiprimeD1RecursiveCounter.activeTest s lam depth M then
        List.replicate (P.levels lam (depth+1)) true else [] := by
  change result (exponentWord lam depth) (AO.values s lam depth M) (successorStack .nextLevels)=_
  rw [result_original]
  unfold originalResult
  split <;> rfl
/-- The conditional child exponent is computed exactly, without a cumulative-sum oracle. -/
theorem child_exponent_original (s lam depth M:Nat) :
    (done (exponentWord lam depth) (AO.values s lam depth M)).data (successorStack .nextExponent)=
      if SemiprimeD1RecursiveCounter.activeTest s lam depth M then
        List.replicate (P.exponent lam (depth+1)) true else [] := by
  change result (exponentWord lam depth) (AO.values s lam depth M) (successorStack .nextExponent)=_
  rw [result_original]
  unfold originalResult
  split <;> rfl
/-- Genuine finite-machine certificate with this same complete own clock. -/
noncomputable def originalInTime (s lam depth M:Nat) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (exponentWord lam depth) (AO.values s lam depth M)))
      (some (SemiprimeD1StackCalls.configuration
        (⟨none,none,none,originalResult s lam depth M,[]⟩:C.State Stack Label)))
      (10000*(s+lam+M+1)) := by
  apply SemiprimeD1StackCalls.evalsCorrect (guardStack .leaf) (guardStack .output) (.inl .start) program
  let h:=source_original s lam depth M
  let t:=Classical.choose h
  have ht:=Classical.choose_spec h
  exact ⟨⟨t,ht.2⟩,ht.1⟩
/-- All sixteen data roles, the shared-level shadow and every real return cell are paid. -/
theorem original_prefix_cells (s lam depth M fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (initial (exponentWord lam depth) (AO.values s lam depth M))))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 1000000*(s+lam+M+1) := by
  have h:=machine_prefix_cells (exponentWord lam depth) (AO.values s lam depth M) fuel cfg hr
  have hv:=AO.volume_original s lam depth M
  have ha:=SemiprimeD1Schedule.exponent_le_lam lam depth
  have ht:=original_time s lam depth M
  simp only [exponentWord,List.length_replicate] at h ht
  omega
end RiemannGaussian.SemiprimeD1StackRecursiveScheduleOriginal
