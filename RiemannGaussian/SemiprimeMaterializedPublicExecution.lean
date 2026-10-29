/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedAcquiredCounter
import RiemannGaussian.SemiprimePublicAcquiredExecution

/-!
# Materialized count and prefix recovery on the actual public factoring graph

All source coefficients and designs are acquired internally. The runtime entry
callback is the actual paid subdivided arithmetic/equality checker with the
existing every-occurrence prefix gate. Only computed numerical source parameters
are exposed here; the N-only schedule is connected in the companion module.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeMaterializedPublicExecution
open scoped BigOperators
open SemiprimePublicAcquiredExecution
open SemiprimeCountRecovery SemiprimeCounterSearch

/-- Actual public prefix count with the new materialized source counter. -/
def prefixCount (N : ℕ) (hN : 0<N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (fixed : List (Fin (wireCount N) × Bool)) : ℕ :=
  Nat.floor (SemiprimeMaterializedAcquiredCounter.count (r := r) (Q := Q)
    (indexedArity N) (indexedCoordinate N hN) eps R 2 J
    (SemiprimeAcquiredPrefixSearch.entry (indexedArity N) (indexedCoordinate N hN)
      (indexedEntry N hN) fixed)).value

/-- Every new requested count agrees with the old public interpreter, for the
same original network and same every-occurrence restrictions. -/
theorem prefixCount_eq_old (N : ℕ) (hN : 0<N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (hQ : 1≤Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R≤Q)
    (hJ : 0<J) (hprecision : (∑ e, indexedArity N e)*R<Q*J)
    (fixed : List (Fin (wireCount N) × Bool)) :
    prefixCount N hN r Q eps R J fixed =
      SemiprimePublicAcquiredExecution.prefixCount N hN r Q eps R J fixed := by
  exact congrArg Nat.floor (SemiprimeMaterializedAcquiredCounter.count_value_eq_old
    (indexedArity N) (indexedCoordinate N hN) eps R 2 J
    (SemiprimeAcquiredPrefixSearch.entry (indexedArity N) (indexedCoordinate N hN)
      (indexedEntry N hN) fixed) (indexed_occurrences N hN) hQ hAQ hJ hprecision)

/-- Counts are exactly the original restricted accepting counts, not modular approximations. -/
theorem prefixCount_correct (N : ℕ) (hN : 0<N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (hQ : 1≤Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R≤Q)
    (hJ : 0<J) (hprecision : (∑ e, indexedArity N e)*R<Q*J)
    (fixed : List (Fin (wireCount N) × Bool)) :
    prefixCount N hN r Q eps R J fixed =
      acceptedCount (restricted assignmentBit (indexedPredicate N hN) fixed) :=
  (prefixCount_eq_old N hN r Q eps R J hQ hAQ hJ hprecision fixed).trans
    (SemiprimePublicAcquiredExecution.prefixCount_correct N hN r Q eps R J hQ hAQ hJ hprecision fixed)

/-- Actual zero-first bit selection invokes the NEW acquired materialized count. -/
def search (N : ℕ) (hN : 0<N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ) :
    SearchResult (Fin (wireCount N)) :=
  SemiprimeCountRecovery.search (prefixCount N hN r Q eps R J) (List.finRange (wireCount N))

/-- Equality includes all selected bits and the actual prefix-query count. -/
theorem search_eq_old (N : ℕ) (hN : 0<N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (hQ : 1≤Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R≤Q)
    (hJ : 0<J) (hprecision : (∑ e, indexedArity N e)*R<Q*J) :
    search N hN r Q eps R J = SemiprimePublicAcquiredExecution.search N hN r Q eps R J := by
  have hp : prefixCount N hN r Q eps R J =
      SemiprimePublicAcquiredExecution.prefixCount N hN r Q eps R J := by
    funext fixed
    exact prefixCount_eq_old N hN r Q eps R J hQ hAQ hJ hprecision fixed
  exact congrArg (fun f => SemiprimeCountRecovery.search f (List.finRange (wireCount N))) hp

/-- Decode the actual selected physical input bits into an integer factor. -/
def factor (N : ℕ) (hN : 0<N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ) : Option ℕ :=
  (search N hN r Q eps R J).values.map (fun values => decodeOperand N values 0)

/-- The materialized factoring execution preserves the exact public selected output. -/
theorem factor_eq_old (N : ℕ) (hN : 0<N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (hQ : 1≤Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R≤Q)
    (hJ : 0<J) (hprecision : (∑ e, indexedArity N e)*R<Q*J) :
    factor N hN r Q eps R J = SemiprimePublicAcquiredExecution.factor N hN r Q eps R J := by
  unfold factor SemiprimePublicAcquiredExecution.factor
  rw [search_eq_old N hN r Q eps R J hQ hAQ hJ hprecision]

/-- Every returned integer is a genuine proper divisor of N. -/
theorem factor_sound (N : ℕ) (hN : 0<N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (hQ : 1≤Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R≤Q)
    (hJ : 0<J) (hprecision : (∑ e, indexedArity N e)*R<Q*J)
    (p : ℕ) (h : factor N hN r Q eps R J=some p) : 2≤p ∧ p<N ∧ p∣N :=
  SemiprimePublicAcquiredExecution.factor_sound N hN r Q eps R J hQ hAQ hJ hprecision p
    ((factor_eq_old N hN r Q eps R J hQ hAQ hJ hprecision).symm.trans h)

/-- Exact failure characterization, including primes and perfect squares. -/
theorem factor_none_iff (N : ℕ) (hN : 0<N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (hQ : 1≤Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R≤Q)
    (hJ : 0<J) (hprecision : (∑ e, indexedArity N e)*R<Q*J) :
    factor N hN r Q eps R J=none ↔ ¬Nonempty (SemiprimePublicFactorCount.OrdinaryFactors N) := by
  rw [factor_eq_old N hN r Q eps R J hQ hAQ hJ hprecision]
  exact SemiprimePublicAcquiredExecution.factor_none_iff N hN r Q eps R J hQ hAQ hJ hprecision

/-- At most one initial and one conditional query per actual public wire. -/
theorem search_queries (N : ℕ) (hN : 0<N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ) :
    (search N hN r Q eps R J).queries ≤ wireCount N+1 := by
  simpa only [search,List.length_finRange] using SemiprimeCountRecovery.search_queries_le
    (prefixCount N hN r Q eps R J) (List.finRange (wireCount N))

end RiemannGaussian.SemiprimeMaterializedPublicExecution
