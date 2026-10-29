/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeHermiteBitsPublicController
import RiemannGaussian.SemiprimeCachedSourceScheduledExecution

/-!
# N-only controller calling the physical Hermite counter

The only runtime input is N. Actual cached-source queries, floor operations,
zero-first recovery, and physical operand reconstruction retain their reports.
The literal schedule/guard and public enumeration construction still require
their separate setup/physical-bit refinements; no complete bit clock is inferred
from the selected scalar/list/branch ledger below.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeHermiteBitsScheduledController
open SemiprimeHermiteBitsPublicController SemiprimePublicAcquiredExecution
open SemiprimeScheduledFactorExecution

/-- Additional actual branch/report control leaves the acquired result unchanged. -/
def bump (r : FactorRun) (n : ℕ) : FactorRun := ⟨r.value,r.queries,r.work+n⟩

/-- Execute the actual finite trial interval, with every tested remainder retained. -/
def trialList (N : ℕ) : List ℕ → FactorRun
  | [] => ⟨none,0,1⟩
  | p::ps => if 2≤ p ∧ N%p=0 then ⟨some p,0,5⟩ else
    let tail := trialList N ps
    ⟨tail.value,0,tail.work+5⟩

/-- Literal finite fallback has the same chosen first divisor as the old algorithm. -/
theorem trialList_value (N : ℕ) (xs : List ℕ) :
    (trialList N xs).value=xs.find? (fun p => decide (2≤ p ∧ N%p=0)) := by
  induction xs with
  | nil => rfl
  | cons p ps ih => by_cases h : 2≤ p ∧ N%p=0 <;> simp [trialList,h,ih]

/-- Every actual finite trial step contributes to the selected-operation report. -/
theorem trialList_work (N : ℕ) (xs : List ℕ) : (trialList N xs).work≤5*xs.length+1 := by
  induction xs with
  | nil => simp [trialList]
  | cons p ps ih => by_cases h : 2≤ p ∧ N%p=0 <;>
      simp [trialList,h,List.length_cons] <;> omega

/-- Explicit ascending finite interval construction, retaining list/loop work. -/
def rangeFrom : ℕ → ℕ → SemiprimePaidPrefixController.Run (List ℕ)
  | 0, _ => ⟨[],1⟩
  | n+1, start => let tail := rangeFrom n (start+1); ⟨start::tail.value,tail.work+3⟩

/-- The acquired interval is the literal original ascending range. -/
theorem rangeFrom_value (n start : ℕ) : (rangeFrom n start).value=List.range' start n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp only [rangeFrom,ih,List.range'_succ,Nat.add_one]

/-- Each interval cell, successor and recursive step is accounted for. -/
theorem rangeFrom_work (n start : ℕ) : (rangeFrom n start).work=3*n+1 := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp only [rangeFrom,ih]; omega

/-- Acquire the actual finite range and retain its full trial scan. -/
def trial (N : ℕ) : FactorRun :=
  let candidates := rangeFrom N 0
  let result := trialList N candidates.value
  bump result (candidates.work+1)

/-- Trial range allocation and each tested scalar remainder are included. -/
theorem trial_work (N : ℕ) : (trial N).work≤8*N+3 := by
  have h := trialList_work N (List.range N)
  simp only [List.length_range] at h
  simp only [trial,bump,rangeFrom_work,rangeFrom_value,← List.range_eq_range']
  omega

/-- Exact old fallback output, without a divisor answer input. -/
theorem trial_value (N : ℕ) : (trial N).value=trialFactor N :=
  by simpa only [trial,bump,rangeFrom_value,← List.range_eq_range',trialFactor] using trialList_value N (List.range N)

/-- Entire deterministic factor algorithm. Counter values and all their reports
are acquired internally, never supplied through a public count callback. -/
def run (N : ℕ) : FactorRun :=
  if hN : 0< N then
    if hr : 0< groups N then
      letI : NeZero (groups N) := ⟨Nat.ne_of_gt hr⟩
      if fastGuard N then
        bump (SemiprimeHermiteBitsPublicController.factor N hN (groups N) (points N)
          (epsilon N) (degree N) (precision N)) 3
      else bump (trial N) 3
    else bump (trial N) 2
  else ⟨none,0,1⟩

/-- EVERY-N exact value equivalence; work reports are NOT identified or discarded. -/
theorem run_value (N : ℕ) : (run N).value=SemiprimeCachedSourceScheduledExecution.run N := by
  by_cases hN : 0< N
  · by_cases hr : 0< groups N
    · let _ : NeZero (groups N) := ⟨Nat.ne_of_gt hr⟩
      by_cases hg : fastGuard N
      · have hQ : 1≤ points N := Nat.le_trans (by decide : 1≤2) hg.2.2.2.1
        have hAQ := guard_interval N hg
        have hp := precision_valid N hN (guard_points_pos N hg)
        simpa only [run,SemiprimeCachedSourceScheduledExecution.run,dite_eq_left hN,
          dite_eq_left hr,ite_eq_left hg,bump] using
          SemiprimeHermiteBitsPublicController.factor_value N hN (groups N) (points N)
            (epsilon N) (degree N) (precision N) hQ hAQ hp.1 hp.2
      · simpa only [run,SemiprimeCachedSourceScheduledExecution.run,dite_eq_left hN,
          dite_eq_left hr,ite_eq_right hg,bump] using trial_value N
    · simpa only [run,SemiprimeCachedSourceScheduledExecution.run,dite_eq_left hN,dite_eq_right hr,bump] using trial_value N
  · simp only [run,SemiprimeCachedSourceScheduledExecution.run,dite_eq_right hN]

/-- Every actual returned value is a proper integer factor. -/
theorem run_sound (N p : ℕ) (h : (run N).value=some p) : 2≤ p ∧ p< N ∧ p∣N :=
  SemiprimeCachedSourceScheduledExecution.run_sound N p ((run_value N).symm.trans h)

/-- All-input completeness, including zero, one, primes and perfect squares. -/
theorem run_none_iff (N : ℕ) :
    (run N).value=none ↔ ¬Nonempty (SemiprimePublicFactorCount.OrdinaryFactors N) := by
  rw [run_value]
  exact SemiprimeCachedSourceScheduledExecution.run_none_iff N

open Filter in
/-- The eventual fast branch actually invokes the word-packet controller. -/
theorem eventually_run_nativeBits : ∀ᶠ N : ℕ in atTop,
    ∃ hN : 0< N, ∃ hg : fastGuard N,
      letI : NeZero (groups N) := ⟨Nat.ne_of_gt (guard_groups_pos N hg)⟩
      run N=bump (SemiprimeHermiteBitsPublicController.factor N hN (groups N) (points N)
        (epsilon N) (degree N) (precision N)) 3 := by
  filter_upwards [eventually_fastGuard,eventually_gt_atTop 0] with N hg hN
  exact ⟨hN,hg,by simp only [run,dite_eq_left hN,dite_eq_left (guard_groups_pos N hg),ite_eq_left hg]⟩

/-- Fast-branch aggregate bound: countBudget is a bound on the ACTUAL internal
counter report, while all additional prefix/recovery/decoder work is explicit. -/
theorem run_fast_work (N : ℕ) (hN : 0< N) (hg : fastGuard N) [NeZero (groups N)] (B : ℕ)
    (hb : ∀ fixed, fixed.length≤ wireCount N →
      (SemiprimeHermiteBitsPublicController.counter N hN (groups N) (points N)
        (epsilon N) (degree N) (precision N) fixed).work≤ B) :
    (run N).work≤(wireCount N+1)*
      (B+wireCount N+3*(wireCount N+1)^2+SemiprimePaidFactorDecoder.budget N (wireCount N)+19) := by
  have hf := SemiprimeHermiteBitsPublicController.factor_work N hN (groups N) (points N)
    (epsilon N) (degree N) (precision N) B hb
  simp only [run,dite_eq_left hN,dite_eq_left (guard_groups_pos N hg),ite_eq_left hg,bump]
  nlinarith

end RiemannGaussian.SemiprimeHermiteBitsScheduledController
