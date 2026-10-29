/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeFullCounterBudget
import RiemannGaussian.SemiprimePublicBudgetDimensions
import RiemannGaussian.SemiprimeFullSetupScheduledController

/-! # Uniform acquired-counter and public-controller budgets
The counter bound is derived from the original indexed graph and scheduled
packing guards. No counter-report, head, rank, or summary budget is assumed.
The result closes the mixed retained-report premise, not a primitive-bit model.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace RiemannGaussian.SemiprimePublicCounterBudget
open scoped BigOperators
open SemiprimePublicAcquiredExecution SemiprimeScheduledFactorExecution
open SemiprimeMacroParameters SemiprimeIndexedDesignResources

/-- Balanced actual-head upper bound used only where native execution needs it. -/
def headBound (N : ℕ) : ℕ := ⌈3*(wireCount N : ℚ)/(2*(groups N : ℚ))⌉₊

/-- Parameter-only complete summary box, using the acquired total-rank budget. -/
def summaryBound (N : ℕ) : ℕ :=
  (2*wireCount N*SemiprimeAcquiredSourceCounter.measurementBound 2 (points N) (degree N)+1)^
    (4*wireCount N/(groups N*lambda N))

/-- One original-input numerical envelope for every reachable prefix counter. -/
def counterBudget (N : ℕ) : ℕ :=
  SemiprimeFullCounterBudget.budget (wireCount N) (factorCount N) (2*wireCount N)
    (groups N) (points N) (degree N) 2 (precision N)
    (SemiprimePublicBudgetDimensions.entryEnvelope (wireCount N))
    (scopeBound (bitLength N)) (headBound N) (4*wireCount N) (summaryBound N)

/-- The ACTUAL executed counter has one derived uniform bound over every
reachable prefix; no counter-work or selected-resource premise remains. -/
theorem counter_work (N : ℕ) (hN : 0<N) (hg : fastGuard N) [NeZero (groups N)]
    (fixed : List (Fin (wireCount N) × Bool)) (hf : fixed.length ≤ wireCount N) :
    (SemiprimeFullSetupPublicController.counter N hN (groups N) (points N)
      (epsilon N) (degree N) (precision N) fixed).work ≤ counterBudget N := by
  let _ : NeZero (SemiprimeCounterRate.scheduledGroupCount (Nat.clog 2 (wireCount N))) :=
    ⟨by change groups N ≠ 0; exact NeZero.ne (groups N)⟩
  have hsource := fastGuard_source N hg
  have hh := scheduled_head_bound (indexedArity N) (indexedCoordinate N hN)
    (scopeBound (bitLength N)) hsource (indexed_occurrences N hN)
    (indexedArity_le N) (indexed_incidence_count N hN)
  have hm := scheduled_measurement_le (indexedArity N) (indexedCoordinate N hN)
    (scopeBound (bitLength N)) hsource (indexed_occurrences N hN)
    (indexedArity_le N) (indexed_incidence_count N hN)
  have hy := scheduled_summary_bound (indexedArity N) (indexedCoordinate N hN)
    (scopeBound (bitLength N)) hsource (indexed_occurrences N hN)
    (indexedArity_le N) (indexed_incidence_count N hN)
  have hT (e : Fin (factorCount N)) (eta : Fin (indexedArity N e) → Bool) :
      (SemiprimeAcquiredPrefixSearch.entry (indexedArity N) (indexedCoordinate N hN)
        (indexedEntry N hN) fixed e eta).arithmetic ≤
          SemiprimePublicBudgetDimensions.entryEnvelope (wireCount N) ∧
      (SemiprimeAcquiredPrefixSearch.entry (indexedArity N) (indexedCoordinate N hN)
        (indexedEntry N hN) fixed e eta).reads ≤
          SemiprimePublicBudgetDimensions.entryEnvelope (wireCount N) := by
    have ht := SemiprimeFullSetupPublicController.entry_work_le N hN fixed hf e eta
    have hb := SemiprimePublicBudgetDimensions.entryBudget_le N hN
    exact ⟨ht.1.trans hb,ht.2.trans hb⟩
  have h := SemiprimeFullCounterBudget.count_work (r:=groups N) (Q:=points N)
    (indexedArity N) (indexedCoordinate N hN) (epsilon N) (degree N) 2 (precision N)
    (SemiprimePublicBudgetDimensions.entryEnvelope (wireCount N))
    (scopeBound (bitLength N)) (headBound N) (4*wireCount N) (summaryBound N)
    (SemiprimeAcquiredPrefixSearch.entry (indexedArity N) (indexedCoordinate N hN)
      (indexedEntry N hN) fixed)
    hg.2.2.1 (indexed_occurrences N hN)
    (Nat.le_trans (by decide : 1 ≤ 2) hg.2.2.2.1) (guard_interval N hg)
    hh hm hy (indexedArity_le N) hT
  simpa only [SemiprimeFullSetupPublicController.counter,counterBudget,
    indexed_incidence_count N hN] using h

/-- Complete derived fast-branch report envelope, including repeated setup for
every query and the actual decoder/controller terms. -/
def controllerBudget (N : ℕ) : ℕ :=
  (wireCount N+1)*(counterBudget N+wireCount N+3*(wireCount N+1)^2+
    SemiprimePublicBudgetDimensions.decoderEnvelope (wireCount N)+19)

/-- The public fast controller no longer assumes an unexplained count budget B. -/
theorem run_work (N : ℕ) (hN : 0<N) (hg : fastGuard N) [NeZero (groups N)] :
    (SemiprimeFullSetupScheduledController.run N).work ≤ controllerBudget N := by
  have h := SemiprimeFullSetupScheduledController.run_fast_work N hN hg (counterBudget N)
    (fun fixed hf => counter_work N hN hg fixed hf)
  have hd := SemiprimePublicBudgetDimensions.decoderBudget_le N hN (wireCount N) (le_refl _)
  exact h.trans (by unfold controllerBudget; gcongr)

/-- Every sufficiently large input executes under the derived public envelope.
This is a bound on the retained mixed report, not yet a primitive bit theorem. -/
theorem eventually_run_work :
    ∀ᶠ N : ℕ in Filter.atTop, (SemiprimeFullSetupScheduledController.run N).work ≤ controllerBudget N := by
  filter_upwards [eventually_fastGuard,Filter.eventually_gt_atTop 0] with N hg hN
  let _ : NeZero (groups N) := ⟨Nat.ne_of_gt (guard_groups_pos N hg)⟩
  exact run_work N hN hg

end RiemannGaussian.SemiprimePublicCounterBudget
