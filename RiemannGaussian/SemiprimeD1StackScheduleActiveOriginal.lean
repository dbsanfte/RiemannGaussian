/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackScheduleActiveBounds

/-! # Exact original active predicate and its own metadata-linear machine clock
Every original parameter, depth and edge count is covered. Preparing these
metadata words from an actual child network remains separate caller work.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackScheduleActiveOriginal
open SemiprimeD1StackScheduleActive SemiprimeD1StackScheduleActiveExecution
open SemiprimeD1StackScheduleActiveBounds
namespace S
export SemiprimeD1Schedule (leafSize levels Active)
export SemiprimeD1PrecisionEnvelope (minimumLevels)
end S
/-- Proof-side decidability of the original guard; no predicate opcode is executed. -/
instance (s lam depth M:Nat) : Decidable (S.Active s lam depth M) :=
  inferInstanceAs (Decidable (S.leafSize s lam<M ∧ S.minimumLevels lam≤S.levels lam depth ∧
    S.levels lam depth≤M))
/-- Actual four original guard counters, encoded only as data by `start`. -/
def values (s lam depth M:Nat) : Param→Nat
  | .leaf=>S.leafSize s lam | .minimum=>S.minimumLevels lam
  | .levels=>S.levels lam depth | .edges=>M
/-- The physically acquired Boolean is precisely the original three-way guard. -/
theorem answer_original (s lam depth M:Nat) :
    answer (values s lam depth M)=decide (S.Active s lam depth M) := rfl
/-- Preparing those exact metadata words agrees with the concrete four-operand API. -/
theorem start_original (s lam depth M:Nat) :
    start (values s lam depth M)=initial (S.leafSize s lam) (S.minimumLevels lam) (S.levels lam depth) M := rfl
/-- No logarithmic metadata is treated as free or as a numerical control register. -/
theorem minimum_le (lam:Nat) : S.minimumLevels lam ≤ 4*lam+12 := by
  have h:Nat.clog 2 (lam+1) ≤ lam+1 := Nat.clog_le_of_le_pow (lam+1).lt_two_pow_self.le
  unfold SemiprimeD1PrecisionEnvelope.minimumLevels
  omega
/-- Uniform inventory in original root scale, logarithmic parameter and current edges. -/
theorem volume_original (s lam depth M:Nat) : volume (values s lam depth M) ≤ s+5*lam+M+13 := by
  have hl:S.leafSize s lam ≤ s+1 := Nat.add_le_add_right (Nat.div_le_self s (Nat.sqrt lam+1)) 1
  have hm:=minimum_le lam
  have hu:=SemiprimeD1Schedule.levels_le lam depth
  change S.leafSize s lam+S.minimumLevels lam+S.levels lam depth+M ≤ _
  omega
/-- Same actual complete guard clock, uniformly linear in original bounded metadata. -/
theorem original_time (s lam depth M:Nat) : runBound (values s lam depth M) ≤ 10000*(s+lam+M+1) := by
  have h:=volume_original s lam depth M
  unfold runBound
  omega
/-- Complete physical guard execution for the whole original schedule family. -/
theorem source_original (s lam depth M:Nat) :
    ∃t≤10000*(s+lam+M+1),SemiprimeD1StackCalls.run program t
      (initial (S.leafSize s lam) (S.minimumLevels lam) (S.levels lam depth) M)=
      some (⟨none,none,none,data (unaryWords (values s lam depth M)) [] [] []
        [decide (S.Active s lam depth M)],[]⟩:C.State Stack Label) := by
  obtain ⟨t,ht,hr⟩:=source_run (values s lam depth M)
  refine ⟨t,ht.trans (original_time s lam depth M),?_⟩
  simpa only [start_original,done,answer_original] using hr
/-- Genuine finite-machine result, with the same own acquired-input clock. -/
noncomputable def originalInTime (s lam depth M:Nat) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (initial (S.leafSize s lam) (S.minimumLevels lam) (S.levels lam depth) M))
      (some (SemiprimeD1StackCalls.configuration
        (⟨none,none,none,data (unaryWords (values s lam depth M)) [] [] []
          [decide (S.Active s lam depth M)],[]⟩:C.State Stack Label))) (10000*(s+lam+M+1)) := by
  apply SemiprimeD1StackCalls.evalsCorrect Stack.leaf Stack.output (.inl (.left .leaf)) program
  let h:=source_original s lam depth M
  let t:=Classical.choose h
  have ht:=Classical.choose_spec h
  exact ⟨⟨t,ht.2⟩,ht.1⟩
/-- Every original-metadata data role and every real return cell is included. -/
theorem original_prefix_cells (s lam depth M fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (initial (S.leafSize s lam) (S.minimumLevels lam) (S.levels lam depth) M)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 1000000*(s+lam+M+1) := by
  have h:=machine_prefix_cells (values s lam depth M) fuel cfg hr
  have hv:=volume_original s lam depth M
  have ht:=original_time s lam depth M
  omega
end RiemannGaussian.SemiprimeD1StackScheduleActiveOriginal
