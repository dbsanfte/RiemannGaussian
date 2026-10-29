/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCachedSourcePublicExecution
import RiemannGaussian.SemiprimeScheduledFactorExecution

/-!
# Natural-input materialized factoring execution

The only runtime input is N. The original computed schedule and literal decidable
guard select the new materialized public count/search; the same complete finite
trial fallback handles the complementary branch. No source array, design,
coefficient, local table, count answer or externally chosen parameter is supplied.
This is a semantic execution join, not a new whole primitive-bit clock theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeCachedSourceScheduledExecution
open scoped BigOperators
open Filter SemiprimePublicAcquiredExecution
open SemiprimeScheduledFactorExecution

/-- Entire deterministic N-only algorithm, with the new materialized counter on
its automatically chosen fast branch and the old finite complete fallback. -/
def run (N : ℕ) : Option ℕ :=
  if hN : 0<N then
    if hr : 0<groups N then
      letI : NeZero (groups N) := ⟨Nat.ne_of_gt hr⟩
      if fastGuard N then
        SemiprimeCachedSourcePublicExecution.factor N hN (groups N) (points N)
          (epsilon N) (degree N) (precision N)
      else trialFactor N
    else trialFactor N
  else none

/-- Exact output equivalence on EVERY natural input, not only promised semiprimes.
The two algorithms can have different operation traces and work reports. -/
theorem run_eq_old (N : ℕ) : run N=SemiprimeScheduledFactorExecution.run N := by
  by_cases hN : 0<N
  · by_cases hr : 0<groups N
    · let _ : NeZero (groups N) := ⟨Nat.ne_of_gt hr⟩
      by_cases hg : fastGuard N
      · have hQ : 1≤points N := Nat.le_trans (by decide : 1≤2) hg.2.2.2.1
        have hAQ := guard_interval N hg
        have hp := precision_valid N hN (guard_points_pos N hg)
        have he := SemiprimeCachedSourcePublicExecution.factor_eq_old N hN (groups N) (points N)
          (epsilon N) (degree N) (precision N) hQ hAQ hp.1 hp.2
        simpa only [run,SemiprimeScheduledFactorExecution.run,dite_eq_left hN,
          dite_eq_left hr,ite_eq_left hg] using he
      · simp only [run,SemiprimeScheduledFactorExecution.run,dite_eq_left hN,
          dite_eq_left hr,ite_eq_right hg]
    · simp only [run,SemiprimeScheduledFactorExecution.run,dite_eq_left hN,dite_eq_right hr]
  · simp only [run,SemiprimeScheduledFactorExecution.run,dite_eq_right hN]

/-- Every actual returned integer is a proper divisor of the original input. -/
theorem run_sound (N p : ℕ) (h : run N=some p) : 2≤p ∧ p<N ∧ p∣N :=
  SemiprimeScheduledFactorExecution.run_sound N p ((run_eq_old N).symm.trans h)

/-- Complete failure characterization for all naturals, including zero, one,
primes, and perfect squares. -/
theorem run_none_iff (N : ℕ) :
    run N=none ↔ ¬Nonempty (SemiprimePublicFactorCount.OrdinaryFactors N) := by
  rw [run_eq_old]
  exact SemiprimeScheduledFactorExecution.run_none_iff N

/-- The literal guard eventually passes, so the runtime actually uses the new
paid cached-source counter rather than the finite fallback. -/
theorem eventually_run_materialized : ∀ᶠ N : ℕ in atTop,
    ∃ hN : 0<N, ∃ hg : fastGuard N,
      letI : NeZero (groups N) := ⟨Nat.ne_of_gt (guard_groups_pos N hg)⟩
      run N=SemiprimeCachedSourcePublicExecution.factor N hN (groups N) (points N)
        (epsilon N) (degree N) (precision N) := by
  filter_upwards [eventually_fastGuard,eventually_gt_atTop 0] with N hg hN
  exact ⟨hN,hg,by simp only [run,dite_eq_left hN,dite_eq_left (guard_groups_pos N hg),ite_eq_left hg]⟩

end RiemannGaussian.SemiprimeCachedSourceScheduledExecution
