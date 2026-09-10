/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FinitePrimePatternSieve
import RiemannGaussian.ZetaMoebiusFiniteSieve

/-!
# The genuine arithmetic response of the complete prime-pattern sieve

The exact pattern expansion identifies the whole union of products with
at least two selected prime divisors. Every intersection is an eligible
mixed-prime arithmetic sector. The full convergent series, including all
overlaps and logarithmic companions, has an independently proved bound
by the explicit product cost of the selected primes.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The original signed tail on the actual union with at least two
selected prime divisors. Each physical integer is included once. -/
def zetaMoebiusPrimePatternCoefficient (D : ℕ) (S : Finset ℕ) (n : ℕ) : ℂ :=
  if 2 ≤ (S.filter (fun p ↦ p ∣ n)).card then zetaMoebiusLogTailCoefficient D n else 0

/-- The complete union coefficient is its exact signed pattern family,
with repeated intersection indices retained until after the identity. -/
theorem zetaMoebiusPrimePatternCoefficient_eq_patterns (D : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (n : ℕ) :
    zetaMoebiusPrimePatternCoefficient D S n =
      ∑ T ∈ S.powerset.filter (fun T ↦ 2 ≤ T.card), ∑ U ∈ (S \ T).powerset,
        (-1 : ℂ) ^ U.card * zetaMoebiusMultipleCoefficient D (∏ p ∈ T ∪ U, p) n :=
  primePairSieve_eq_signed_patterns S hS (zetaMoebiusLogTailCoefficient D) n

/-- The full original arithmetic series on the prime-pattern union. -/
def zetaMoebiusPrimePatternFilter (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ)
    (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, zetaMoebiusPrimePatternCoefficient D S n * zetaPrimeFilterKernel p N s n

/-- The new exact-pattern expression is the original simultaneous
divisibility sieve over all selected prime pairs, coefficient by coefficient. -/
theorem zetaMoebiusPrimePatternCoefficient_eq_sieve (D : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (n : ℕ) :
    zetaMoebiusPrimePatternCoefficient D S n = zetaMoebiusSieveCoefficient D (primePairFactors S) n := by
  simp only [zetaMoebiusPrimePatternCoefficient, zetaMoebiusSieveCoefficient, primePairSieve_card_iff S hS n]

/-- The complete pattern response agrees exactly with the existing
genuine sieve series; no replacement carrier is introduced. -/
theorem zetaMoebiusPrimePatternFilter_eq_sieve (p : Polynomial ℂ) (D N : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (s : ℂ) :
    zetaMoebiusPrimePatternFilter p D S N s = zetaMoebiusSieveFilter p D (primePairFactors S) N s := by
  unfold zetaMoebiusPrimePatternFilter zetaMoebiusSieveFilter
  simp_rw [zetaMoebiusPrimePatternCoefficient_eq_sieve D S hS]

/-- The literal union series is genuinely summable throughout the
Euler half-plane, with no bound on the selected primes required. -/
theorem summable_zetaMoebiusPrimePatternKernel (p : Polynomial ℂ) (D N : ℕ) (S : Finset ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ zetaMoebiusPrimePatternCoefficient D S n * zetaPrimeFilterKernel p N s n) := by
  have h := (hasSum_zetaMoebiusLogTailFilter_kernel p D N hs).summable.indicator
    {n | 2 ≤ (S.filter (fun p ↦ p ∣ n)).card}
  apply h.congr
  intro n
  by_cases hn : 2 ≤ (S.filter (fun p ↦ p ∣ n)).card <;>
    simp [Set.indicator, zetaMoebiusPrimePatternCoefficient, hn]

/-- Every intersection has its genuine analytic response, and the
complete finite expansion sums to the original union series. -/
theorem hasSum_zetaMoebiusPrimePatternFilter (p : Polynomial ℂ) (D N : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ zetaMoebiusPrimePatternCoefficient D S n * zetaPrimeFilterKernel p N s n)
      (∑ T ∈ S.powerset.filter (fun T ↦ 2 ≤ T.card), ∑ U ∈ (S \ T).powerset,
        (-1 : ℂ) ^ U.card * zetaMoebiusMultipleFilter p D (∏ r ∈ T ∪ U, r) N s) := by
  have h := hasSum_sum (s := S.powerset.filter (fun T ↦ 2 ≤ T.card)) (fun T hT ↦
    hasSum_sum (s := (S \ T).powerset) (fun U hU ↦
      (hasSum_zetaMoebiusMultipleFilter p D N
        (prime_pattern_factor_eligible S hS hT hU).1
        (prime_pattern_factor_eligible S hS hT hU).2.1
        (prime_pattern_factor_eligible S hS hT hU).2.2 hs).mul_left ((-1 : ℂ) ^ U.card)))
  apply h.congr_fun
  intro n
  rw [zetaMoebiusPrimePatternCoefficient_eq_patterns D S hS n]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro U _
  ring

/-- The whole simultaneous deletion has one independent bound with
every overlap paid by the proved selected-prime product cost. -/
theorem exists_zetaMoebiusPrimePatternFilter_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N : ℕ) (S : Finset ℕ),
      (∀ r ∈ S, r.Prime) →
      ‖zetaMoebiusPrimePatternFilter p D S N (3 / 2 + I * y)‖ ≤
        C * Real.sqrt D * (∑ k ∈ p.support, ‖p.coeff k‖) * primePatternSieveCost S := by
  obtain ⟨C, hC, hb⟩ := exists_zetaMoebiusMultipleFilter_lcm_bound y hy
  refine ⟨C, hC, ?_⟩
  intro p D N S hS
  rw [zetaMoebiusPrimePatternFilter, (hasSum_zetaMoebiusPrimePatternFilter p D N S hS (by norm_num)).tsum_eq]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ T ∈ S.powerset.filter (fun T ↦ 2 ≤ T.card), ∑ U ∈ (S \ T).powerset,
        C * Real.sqrt D * (∑ k ∈ p.support, ‖p.coeff k‖) * zetaMoebiusLcmCost (∏ r ∈ T ∪ U, r) := by
      apply Finset.sum_le_sum
      intro T hT
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro U hU
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact (hb p D _ N (prime_pattern_factor_eligible S hS hT hU).1).trans_eq (by ring)
    _ = C * Real.sqrt D * (∑ k ∈ p.support, ‖p.coeff k‖) *
        ∑ T ∈ S.powerset.filter (fun T ↦ 2 ≤ T.card), ∑ U ∈ (S \ T).powerset,
          zetaMoebiusLcmCost (∏ r ∈ T ∪ U, r) := by simp_rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_prime_pattern_lcm_cost_le S hS) (by positivity)

/-- The complete simultaneous deletion has an explicit square-root
prime-cutoff exponential bound, for every finite selected-prime family. -/
theorem exists_zetaMoebiusPrimePatternFilter_cutoff_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N R : ℕ) (S : Finset ℕ),
      (∀ r ∈ S, r.Prime ∧ r ≤ R) →
      ‖zetaMoebiusPrimePatternFilter p D S N (3 / 2 + I * y)‖ ≤
        C * Real.sqrt D * (∑ k ∈ p.support, ‖p.coeff k‖) *
          ((1 + (R : ℝ) ^ 2) * Real.exp (8 * Real.sqrt R)) := by
  obtain ⟨C, hC, hb⟩ := exists_zetaMoebiusPrimePatternFilter_bound y hy
  refine ⟨C, hC, fun p D N R S hS ↦ ?_⟩
  exact (hb p D N S (fun r hr ↦ (hS r hr).1)).trans
    (mul_le_mul_of_nonneg_left (primePatternSieveCost_le_exp_sqrt S R hS) (by positivity))

end
end RiemannGaussian
