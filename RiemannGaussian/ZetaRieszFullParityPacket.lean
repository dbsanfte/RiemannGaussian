/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszParityWindow

/-!
# The literal all-count packet in the interior share box

Every prime count is retained. The exact finite factorial selection is
shared across counts; it is not replaced by its limiting indicator. The
original residual coefficient keeps the old unassigned fraction, Riesz
sign, phase, count cutoff and all core masks. The ledger below is an exact
suballocation only; no estimate for the packet or its rest is asserted.
-/

namespace RiemannGaussian.ZetaRieszParityPacket
noncomputable section
open scoped BigOperators Classical
open ZetaRieszSkewAllocation ZetaRieszPrimeEndpoint ZetaRieszAnnulusJoint
open ZetaRieszJointAllocation

/-- The concrete interior box, with canonical largest and least primes. -/
structure FullParityBox (n : ℕ) : Prop where
  squarefree : Squarefree n
  nontrivial : 1 < n
  count_lower : 3 ≤ n.primeFactors.card
  largest_mem : largestPrime n ∈ n.primeFactors
  largest_lower : (43/80 : ℝ)*Real.log n ≤ Real.log (largestPrime n)
  largest_upper : Real.log (largestPrime n) ≤ (9/16 : ℝ)*Real.log n
  least_lower : (3/250 : ℝ)*Real.log n ≤ Real.log n.minFac
  least_upper : Real.log n.minFac ≤ (7/250 : ℝ)*Real.log n

/-- This is a filter of the current direct core support, including its
literal prime-count bound. The physical prime mask is retained on every leg. -/
def fullParityBand (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (coreBand u N K).filter (fun n => FullParityBox n ∧
    ∀ p ∈ n.primeFactors, p ∈ intermediatePrimes u N)

private theorem fullParityBox_ratios {n : ℕ} (h : FullParityBox n) :
    (0 ≤ 1-Real.log (largestPrime n)/Real.log n ∧
      1-Real.log (largestPrime n)/Real.log n ≤ 1) ∧
    (0 ≤ Real.log n.minFac/(Real.log n-Real.log (largestPrime n)) ∧
      Real.log n.minFac/(Real.log n-Real.log (largestPrime n)) ≤ 1) := by
  have hn : 0 < Real.log n := Real.log_pos (by exact_mod_cast h.nontrivial)
  have hp0 : 0 ≤ Real.log (largestPrime n) := Real.log_natCast_nonneg _
  have hr0 : 0 ≤ Real.log n.minFac := Real.log_natCast_nonneg _
  have hcof : 0 < Real.log n-Real.log (largestPrime n) := by linarith [h.largest_upper]
  have hfrac0 := div_nonneg hp0 hn.le
  have hfrac1 : Real.log (largestPrime n)/Real.log n ≤ 1 :=
    (div_le_one hn).mpr (by linarith [h.largest_upper])
  exact ⟨⟨by linarith, by linarith⟩,
    div_nonneg hr0 hcof.le, (div_le_one hcof).mpr (by linarith [h.least_upper, h.largest_upper])⟩

/-- The same exact correlated order box on the largest prime, least
prime and the aggregate remaining cofactor. No asymptotic mask removal. -/
def fullParitySelection (u : ℝ) (N K n : ℕ) : ℝ :=
  if n ∈ fullParityBand u N K then
    rectangleMass N (1-Real.log (largestPrime n)/Real.log n)
      (Real.log n.minFac/(Real.log n-Real.log (largestPrime n)))
  else 0

theorem fullParitySelection_bounds (u : ℝ) (N K n : ℕ) :
    0 ≤ fullParitySelection u N K n ∧ fullParitySelection u N K n ≤ 1 := by
  unfold fullParitySelection
  split_ifs with hn
  · have hb := (Finset.mem_filter.mp hn).2.1
    obtain ⟨hx, hc⟩ := fullParityBox_ratios hb
    have hm := rectangleMass_bounds N hx.1 hx.2 hc.1 hc.2
    exact ⟨hm.1, hm.2.trans (rectangleMarginal_bounds N hx.1 hx.2).2⟩
  · norm_num

/-- The packet retains the complete complex phase and original allocation. -/
def fullParityPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ coreBand u N K, (fullParitySelection u N K n : ℂ)*
    (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n *
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)

/-- Everything not allocated to the packet remains explicitly unpaid. -/
def fullParityRest (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ coreBand u N K, ((1-fullParitySelection u N K n : ℝ) : ℂ)*
    (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n *
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)

theorem fullParity_direct_ledger (u y : ℝ) (N K : ℕ) :
    coreResponse u y N K = fullParityPacket u y N K+fullParityRest u y N K := by
  unfold coreResponse fullParityPacket fullParityRest
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  push_cast
  ring

/-- There is a finite rigorous count ceiling in this fixed box: no
label with forty or more prime factors can occur. Counts 12 through 39
are still present and have not been discarded on numerical evidence. -/
theorem fullParityBox_count_le {n : ℕ} (h : FullParityBox n) : n.primeFactors.card ≤ 39 := by
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast h.nontrivial)
  have hrprime : n.minFac.Prime := Nat.minFac_prime h.nontrivial.ne'
  have hs : (∑ _q ∈ n.primeFactors.erase (largestPrime n), (3/250 : ℝ)*Real.log n) ≤
      ∑ q ∈ n.primeFactors.erase (largestPrime n), Real.log q := by
    apply Finset.sum_le_sum
    intro q hq
    have hqm := Finset.mem_of_mem_erase hq
    have hqprime := Nat.prime_of_mem_primeFactors hqm
    exact h.least_lower.trans (Real.log_le_log (by exact_mod_cast hrprime.pos)
      (by exact_mod_cast Nat.minFac_le_of_dvd hqprime.two_le (Nat.dvd_of_mem_primeFactors hqm)))
  have he := Finset.sum_erase_add _ (fun q : ℕ => Real.log q) h.largest_mem
  rw [← CoprimeEulerPhase.squarefree_log_eq_prime_sum h.squarefree] at he
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem h.largest_mem,
    Nat.cast_sub (by have := h.count_lower; omega : 1 ≤ n.primeFactors.card), Nat.cast_one] at hs
  by_contra hc
  have hcR : (40 : ℝ) ≤ n.primeFactors.card := by exact_mod_cast (by omega : 40 ≤ n.primeFactors.card)
  nlinarith [h.largest_lower]

theorem fullParitySelection_eq_zero_of_large_count {u : ℝ} {N K n : ℕ}
    (hc : 40 ≤ n.primeFactors.card) : fullParitySelection u N K n = 0 := by
  apply if_neg
  intro hn
  have h := fullParityBox_count_le (Finset.mem_filter.mp hn).2.1
  omega

end
end RiemannGaussian.ZetaRieszParityPacket
