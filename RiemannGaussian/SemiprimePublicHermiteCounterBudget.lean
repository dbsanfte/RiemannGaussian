/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeHermiteBitsSetupBudget
import RiemannGaussian.SemiprimePublicBudgetDimensions
import RiemannGaussian.SemiprimeHermiteBitsScheduledController
import RiemannGaussian.SemiprimePublicCounterBudget

/-! # Uniform acquired-counter and public-controller budgets
The counter bound is derived from the original indexed graph and scheduled
packing guards. No counter-report, head, rank, or summary budget is assumed.
The result closes the mixed retained-report premise, not a primitive-bit model.
-/
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace RiemannGaussian.SemiprimePublicHermiteCounterBudget
open scoped BigOperators
open SemiprimePublicAcquiredExecution SemiprimeScheduledFactorExecution
open SemiprimeMacroParameters SemiprimeIndexedDesignResources

/-- Reuse only the proved public numerical head envelope, never an old clock. -/
abbrev headBound := SemiprimePublicCounterBudget.headBound

/-- Reuse only the numerical complete summary box. -/
abbrev summaryBound := SemiprimePublicCounterBudget.summaryBound

/-- Literal physical checker report envelope, including its prefix gate. -/
def entryBound (N : ℕ) := 2*SemiprimePublicBudgetDimensions.entryEnvelope (wireCount N)+4

/-- Actual cached designs coincide with the indexed mathematical design. -/
theorem designs_eq {n F r Q : ℕ} [NeZero r] (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B : ℕ)
    (howner : ∀ v,(Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card ≤ B)
    (hQ : 1 ≤ Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (t : Fin Q) :
    SemiprimeHermiteBitsSetupBudget.designs (r:=r) (Q:=Q) arity coordinate eps R B t =
      indexedDesign (r:=r) (Q:=Q) arity coordinate eps R B t := by
  let f := fun (en : SemiprimeSourceLayout.Enumerations
      ((e : Fin F) × Fin (arity e)) (Fin n) (Fin F) r Q) =>
    (SemiprimePaidRuntimeDesign.build
      (SemiprimePaidRawAcquisition.raw (n:=n) (F:=F)
        (SemiprimePaidRawAcquisition.acquire arity coordinate en eps R B).value t)
      (SemiprimePaidRawAcquisition.reader (n:=n)
        (SemiprimePaidRawAcquisition.acquire arity coordinate en eps R B).value t)
      (SemiprimePaidMeasurementBound.bits B Q R)).value
  have he := congrArg f (SemiprimePaidFiniteEnumerations.indexed_value n F r Q arity)
  have hh : SemiprimeHermiteBitsSetupBudget.designs (r:=r) (Q:=Q) arity coordinate eps R B t =
      f (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value := by
    simp only [SemiprimeHermiteBitsSetupBudget.designs,Array.getElem_ofFn]
    rfl
  exact hh.trans (he.trans (physical_eq (r:=r) (Q:=Q) arity coordinate eps R B howner hQ hAQ t))


/-- One original-input numerical envelope for every reachable prefix counter. -/
def counterBudget (N : ℕ) (hN : 0<N) [NeZero (groups N)] : ℕ :=
  SemiprimeFullSetupBudget.setupBudget (wireCount N) (factorCount N) (2*wireCount N)
    (groups N) (points N) (degree N) 2 ((groups N)^(2*points N)) ((groups N)^(points N))+
  SemiprimeSourceWordAcquisition.encodingBudget (2*wireCount N) (wireCount N)
    (SemiprimeSourceWordAcquisition.sourceBits 2 (points N) (degree N)) (degree N)+1+
  SemiprimeHermiteBitsSetupBudget.nativeBudget (wireCount N) (factorCount N) (2*wireCount N)
    (SemiprimeNativeInputBits.inputBits (wireCount N) 2 (points N) (degree N) (precision N))
    (points N) (precision N) (degree N) (headBound N) (4*wireCount N)
    (scopeBound (bitLength N)) (entryBound N) (indexedArity N)
    (SemiprimeHermiteBitsSetupBudget.designs (r:=groups N) (Q:=points N)
      (indexedArity N) (indexedCoordinate N hN)
      (epsilon N) (degree N) 2)

/-- The literal executed design has the public indexed head, rank and summary bounds. -/
theorem actual_design_resources (N : ℕ) (hN : 0<N) (hg : fastGuard N) [NeZero (groups N)] :
    let ds := SemiprimeHermiteBitsSetupBudget.designs (r:=groups N) (Q:=points N)
      (indexedArity N) (indexedCoordinate N hN) (epsilon N) (degree N) 2
    (∀ a,(ds a).r=groups N) ∧
    (∀ a g,(ds a).h g ≤ headBound N) ∧
    (∀ a g,(ds a).m g ≤ 4*wireCount N) ∧
    (∀ a,SemiprimePacketArrayExecution.summaryCount (ds a).r (ds a).h (ds a).m (ds a).W ≤ summaryBound N) := by
  let _ : NeZero (SemiprimeCounterRate.scheduledGroupCount (Nat.clog 2 (wireCount N))) :=
    ⟨by change groups N ≠ 0; exact NeZero.ne (groups N)⟩
  have hQ : 1 ≤ points N := Nat.le_trans (by decide : 1 ≤ 2) hg.2.2.2.1
  have hAQ := guard_interval N hg
  have he (a : Fin (points N)) := designs_eq (r:=groups N) (Q:=points N)
    (indexedArity N) (indexedCoordinate N hN) (epsilon N) (degree N) 2
    (indexed_occurrences N hN) hQ hAQ a
  refine ⟨?_,?_,?_,?_⟩
  · intro a
    exact (congrArg (fun d => d.r) (he a)).trans rfl
  · intro a
    rw [he a]
    exact scheduled_head_bound (indexedArity N) (indexedCoordinate N hN)
      (scopeBound (bitLength N)) (fastGuard_source N hg) (indexed_occurrences N hN)
      (indexedArity_le N) (indexed_incidence_count N hN) a
  · intro a
    rw [he a]
    exact scheduled_measurement_le (indexedArity N) (indexedCoordinate N hN)
      (scopeBound (bitLength N)) (fastGuard_source N hg) (indexed_occurrences N hN)
      (indexedArity_le N) (indexed_incidence_count N hN) a
  · intro a
    rw [he a]
    exact scheduled_summary_bound (indexedArity N) (indexedCoordinate N hN)
      (scopeBound (bitLength N)) (fastGuard_source N hg) (indexed_occurrences N hN)
      (indexedArity_le N) (indexed_incidence_count N hN) a

/-- The ACTUAL executed counter has one derived uniform bound over every
reachable prefix; no counter-work or selected-resource premise remains. -/
theorem counter_work (N : ℕ) (hN : 0<N) (hg : fastGuard N) [NeZero (groups N)]
    (fixed : List (Fin (wireCount N) × Bool)) (hf : fixed.length ≤ wireCount N) :
    (SemiprimeHermiteBitsPublicController.counter N hN (groups N) (points N)
      (epsilon N) (degree N) (precision N) fixed).work ≤ counterBudget N hN := by
  let _ : NeZero (SemiprimeCounterRate.scheduledGroupCount (Nat.clog 2 (wireCount N))) :=
    ⟨by change groups N ≠ 0; exact NeZero.ne (groups N)⟩
  have hsource := fastGuard_source N hg
  have hh := scheduled_head_bound (indexedArity N) (indexedCoordinate N hN)
    (scopeBound (bitLength N)) hsource (indexed_occurrences N hN)
    (indexedArity_le N) (indexed_incidence_count N hN)
  have hm := scheduled_measurement_le (indexedArity N) (indexedCoordinate N hN)
    (scopeBound (bitLength N)) hsource (indexed_occurrences N hN)
    (indexedArity_le N) (indexed_incidence_count N hN)
  have hQ : 1 ≤ points N := Nat.le_trans (by decide : 1 ≤ 2) hg.2.2.2.1
  have hAQ := guard_interval N hg
  have hh' : ∀ a g,(SemiprimeHermiteBitsSetupBudget.designs (r:=groups N) (Q:=points N)
      (indexedArity N) (indexedCoordinate N hN) (epsilon N) (degree N) 2 a).h g ≤ headBound N := by
    intro a
    rw [designs_eq (r:=groups N) (Q:=points N) (indexedArity N)
      (indexedCoordinate N hN) (epsilon N) (degree N) 2 (indexed_occurrences N hN) hQ hAQ a]
    exact hh a
  have hm' : ∀ a g,(SemiprimeHermiteBitsSetupBudget.designs (r:=groups N) (Q:=points N)
      (indexedArity N) (indexedCoordinate N hN) (epsilon N) (degree N) 2 a).m g ≤ 4*wireCount N := by
    intro a
    rw [designs_eq (r:=groups N) (Q:=points N) (indexedArity N)
      (indexedCoordinate N hN) (epsilon N) (degree N) 2 (indexed_occurrences N hN) hQ hAQ a]
    exact hm a
  have hT (e : Fin (factorCount N)) (eta : Fin (indexedArity N e) → Bool) :
      (SemiprimePrefixEntryWords.entry (indexedArity N) (indexedCoordinate N hN)
        (indexedEntry N hN) fixed e eta).clock ≤ entryBound N := by
    have ht := SemiprimeHermiteBitsPublicController.entry_work_le N hN fixed hf e eta
    have hb := SemiprimePublicBudgetDimensions.entryBudget_le N hN
    have he : SemiprimeHermiteBitsPublicController.entryBudget N ≤ entryBound N := by
      unfold SemiprimeHermiteBitsPublicController.entryBudget entryBound
      unfold SemiprimeFullSetupPublicController.entryBudget at hb
      omega
    exact ht.trans he
  have h := SemiprimeHermiteBitsSetupBudget.count_work (r:=groups N) (Q:=points N)
    (indexedArity N) (indexedCoordinate N hN) (epsilon N) (degree N) 2 (precision N)
    (headBound N) (4*wireCount N) (scopeBound (bitLength N)) (entryBound N)
    (SemiprimePrefixEntryWords.entry (indexedArity N) (indexedCoordinate N hN)
      (indexedEntry N hN) fixed)
    hg.2.2.1 (indexed_occurrences N hN) hQ hAQ hh' hm' (indexedArity_le N) hT
    (fun e eta => le_of_eq (SemiprimePrefixEntryWords.entry_length _ _ _ _ e eta))
  simpa only [SemiprimeHermiteBitsPublicController.counter,counterBudget,
    indexed_incidence_count N hN] using h

/-- Complete derived fast-branch report envelope, including repeated setup for
every query and the actual decoder/controller terms. -/
def controllerBudget (N : ℕ) (hN : 0<N) [NeZero (groups N)] : ℕ :=
  (wireCount N+1)*(counterBudget N hN+wireCount N+3*(wireCount N+1)^2+
    SemiprimePublicBudgetDimensions.decoderEnvelope (wireCount N)+19)

/-- The public fast controller no longer assumes an unexplained count budget B. -/
theorem run_work (N : ℕ) (hN : 0<N) (hg : fastGuard N) [NeZero (groups N)] :
    (SemiprimeHermiteBitsScheduledController.run N).work ≤ controllerBudget N hN := by
  have h := SemiprimeHermiteBitsScheduledController.run_fast_work N hN hg (counterBudget N hN)
    (fun fixed hf => counter_work N hN hg fixed hf)
  have hd := SemiprimePublicBudgetDimensions.decoderBudget_le N hN (wireCount N) (le_refl _)
  exact h.trans (by unfold controllerBudget; gcongr)

end RiemannGaussian.SemiprimePublicHermiteCounterBudget
