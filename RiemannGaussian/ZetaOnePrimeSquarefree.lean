/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeDivisibilityPrefix
import RiemannGaussian.FinitePrimeCountOne

/-!
# Independent control of the final selected-prime contribution

The actual squarefree tail with exactly one selected prime splits into its
complete signed divisor prefix and a finite ordinary-prime correction.
Every overlap in the prefix has a proved product budget. The correction
is retained exactly and bounded independently. Together they control the
whole selected-prime contribution, rather than one fibre at a time.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- On every squarefree integer the original distinct-prime tail is
the negative divisor prefix plus its exact ordinary-prime correction. -/
theorem zetaSquarefreeDistinctCoefficient_eq_prefix_add_prime (D : ℕ) (hD : 1 ≤ D) (n : ℕ) :
    (if Squarefree n then zetaMoebiusDistinctPrimeCoefficient D n else 0) =
      zetaSquarefreeDivisibilityPrefixCoefficient D ∅ n +
        if n.Prime then (Real.log n : ℂ) else 0 := by
  by_cases hn : Squarefree n
  · have hz : zetaMoebiusTailPrimePowerCoefficient D n = 0 := by
      unfold zetaMoebiusTailPrimePowerCoefficient
      split_ifs with hp
      · exact zetaMoebiusLogTailCoefficient_prime D hD
          (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hn, hp⟩)
      · rfl
    have ht := zetaMoebiusLogTailCoefficient_eq_primePower_add_distinct D n
    rw [zetaMoebiusLogTailCoefficient_eq_vonMangoldt_add_prefix, hz, zero_add] at ht
    rw [if_pos hn, zetaSquarefreeDivisibilityPrefixCoefficient, if_pos hn, Finset.prod_empty, ← ht]
    by_cases hp : n.Prime
    · rw [if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
      ring
    · have hpp : ¬IsPrimePow n := fun h ↦ hp (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hn, h⟩)
      simp [hp, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
  · have hp : ¬n.Prime := fun h ↦ hn h.squarefree
    simp [hn, hp, zetaSquarefreeDivisibilityPrefixCoefficient]

/-- At a prime integer, having exactly one selected prime divisor
means precisely that this prime is in the selected family. -/
theorem prime_count_one_iff_mem (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {n : ℕ} (hn : n.Prime) :
    (S.filter (fun p ↦ p ∣ n)).card = 1 ↔ n ∈ S := by
  have he : S.filter (fun p ↦ p ∣ n) = S.filter (fun p ↦ p = n) :=
    Finset.filter_congr (fun p hp ↦ Nat.prime_dvd_prime_iff_eq (hS p hp) hn)
  rw [he, Finset.filter_eq']
  by_cases h : n ∈ S <;> simp [h]

/-- The original squarefree distinct-prime coefficient on the full
pattern having exactly one selected prime divisor. -/
def zetaOnePrimeSquarefreeCoefficient (D : ℕ) (S : Finset ℕ) (n : ℕ) : ℂ :=
  if (S.filter (fun p ↦ p ∣ n)).card = 1 then
    (if Squarefree n then zetaMoebiusDistinctPrimeCoefficient D n else 0) else 0

/-- The actual negative prefix on that same complete physical pattern. -/
def zetaOnePrimeSquarefreePrefixCoefficient (D : ℕ) (S : Finset ℕ) (n : ℕ) : ℂ :=
  if (S.filter (fun p ↦ p ∣ n)).card = 1 then
    zetaSquarefreeDivisibilityPrefixCoefficient D ∅ n else 0

/-- Every term in the prime correction is explicit and finite.
No ordinary-prime leakage is hidden in the prefix bound. -/
theorem zetaOnePrimeSquarefreeCoefficient_eq_prefix_add_primes (D : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (n : ℕ) :
    zetaOnePrimeSquarefreeCoefficient D S n = zetaOnePrimeSquarefreePrefixCoefficient D S n +
      if n ∈ S then (Real.log n : ℂ) else 0 := by
  unfold zetaOnePrimeSquarefreeCoefficient zetaOnePrimeSquarefreePrefixCoefficient
  rw [zetaSquarefreeDistinctCoefficient_eq_prefix_add_prime D hD n]
  by_cases hn : n ∈ S
  · have hp := hS n hn
    have hc := (prime_count_one_iff_mem S hS hp).mpr hn
    simp [hn, hp, hc]
  · by_cases hp : n.Prime
    · have hc : (S.filter (fun p ↦ p ∣ n)).card ≠ 1 :=
        fun h ↦ hn ((prime_count_one_iff_mem S hS hp).mp h)
      simp [hn, hc]
    · simp [hn, hp]

/-- The full one-prime prefix is exactly the signed transform of
the already controlled squarefree intersection responses. -/
theorem zetaOnePrimeSquarefreePrefixCoefficient_eq_transform (D : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (n : ℕ) :
    zetaOnePrimeSquarefreePrefixCoefficient D S n =
      primeCountOneTransform (fun W ↦ zetaSquarefreeDivisibilityPrefixCoefficient D W n) S := by
  have he : (fun W ↦ zetaSquarefreeDivisibilityPrefixCoefficient D W n) =
      (fun W ↦ if (∏ p ∈ W, p) ∣ n then zetaSquarefreeDivisibilityPrefixCoefficient D ∅ n else 0) :=
    funext (fun W ↦ zetaSquarefreeDivisibilityPrefixCoefficient_eq_indicator D W n)
  rw [he, primeCountOneTransform_indicator S hS]
  rfl

/-- The entire signed prefix response, with all physical phases and
the actual polynomial filter retained. -/
def zetaOnePrimeSquarefreePrefixFilter (p : Polynomial ℂ) (D : ℕ)
    (S : Finset ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, zetaOnePrimeSquarefreePrefixCoefficient D S n * zetaPrimeFilterKernel p N s n

/-- The exact finite prime-pattern expansion commutes with all of
the genuinely convergent squarefree prefix series. -/
theorem hasSum_zetaOnePrimeSquarefreePrefixFilter (p : Polynomial ℂ) (D N : ℕ)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ zetaOnePrimeSquarefreePrefixCoefficient D S n * zetaPrimeFilterKernel p N s n)
      (primeCountOneTransform (fun W ↦ zetaSquarefreeDivisibilityPrefixFilter p D W N s) S) := by
  have h := hasSum_primeCountOneTransform
    (fun W n ↦ zetaSquarefreeDivisibilityPrefixCoefficient D W n * zetaPrimeFilterKernel p N s n)
    (fun W ↦ zetaSquarefreeDivisibilityPrefixFilter p D W N s) S
    (fun W hW ↦ (summable_zetaSquarefreeDivisibilityPrefixFilter p D N W
      (fun a ha ↦ hS a (hW ha)) hs).hasSum)
  apply h.congr_fun
  intro n
  rw [primeCountOneTransform_mul_right, zetaOnePrimeSquarefreePrefixCoefficient_eq_transform D S hS n]

/-- The complete prefix has a uniform independent bound for every
finite selected-prime family through the cutoff, including all overlaps. -/
theorem exists_zetaOnePrimeSquarefreePrefixFilter_bound (y : ℝ) (hy : 1 < |y|)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N R : ℕ) (S : Finset ℕ),
      (∀ a ∈ S, a.Prime ∧ a ≤ R) →
      ‖zetaOnePrimeSquarefreePrefixFilter p D S N (3 / 2 + I * y)‖ ≤
        C * D * Real.exp (4 * Real.sqrt R) * r⁻¹ ^ N *
          ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  obtain ⟨C, hC, hb⟩ := exists_zetaSquarefreeDivisibilityPrefixFilter_bound y hy hr hr1
  let τ := zetaSquareSieveExponent r
  refine ⟨3 * C * Real.exp (2 * primeSquareWeightMass τ), by positivity, ?_⟩
  intro p D N R S hS
  rw [zetaOnePrimeSquarefreePrefixFilter,
    (hasSum_zetaOnePrimeSquarefreePrefixFilter p D N S (fun a ha ↦ (hS a ha).1) (by norm_num)).tsum_eq]
  have h := norm_primeCountOneTransform_le
    (fun W ↦ zetaSquarefreeDivisibilityPrefixFilter p D W N (3 / 2 + I * y)) S
    (primeSquareCorrectedWeight τ) (primeSquareCorrectedWeight_nonneg τ)
    (show 0 ≤ C * D * r⁻¹ ^ N * (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) by positivity)
    (fun W hW ↦ hb p D N W (fun a ha ↦ (hS a (hW ha)).1))
  have hp := prod_one_add_primeSquareCorrectedWeight_le S R hS (zetaSquareSieveExponent_gt_half hr1)
  apply h.trans
  exact (mul_le_mul_of_nonneg_left hp (by positivity :
    0 ≤ 3 * (C * D * r⁻¹ ^ N * (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k)))).trans_eq (by ring)

end
end RiemannGaussian
