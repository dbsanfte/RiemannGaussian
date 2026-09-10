/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaOnePrimeSquarefree

/-!
# The actual one-prime squarefree contribution has an independent bound

The complete finite ordinary-prime correction is paid in addition to the
signed prefix. The resulting bound applies to the literal part of the
previous squarefree survivor with a selected prime divisor. Both the exact
coefficient and the full convergent arithmetic sum remain available.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The one-prime contribution restricts exactly the original
squarefree survivor; all other coefficients remain unchanged. -/
theorem zetaOnePrimeSquarefreeCoefficient_eq_sieved (D : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (n : ℕ) :
    zetaOnePrimeSquarefreeCoefficient D S n =
      if ∃ p ∈ S, p ∣ n then zetaSquarefreeCoefficient D S n else 0 := by
  have hp := primePairSieve_card_iff S hS n
  have hz : (S.filter (fun p ↦ p ∣ n)).card = 0 ↔ ¬∃ p ∈ S, p ∣ n := by
    simp [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  by_cases hc : (S.filter (fun p ↦ p ∣ n)).card = 1
  · have he : ∃ p ∈ S, p ∣ n := by
      by_contra h
      have h0 := hz.mpr h
      omega
    have hsieve : ¬∃ P ∈ primePairFactors S, P ∣ n := by
      intro h
      have hge := hp.mpr h
      omega
    simp [zetaOnePrimeSquarefreeCoefficient, zetaSquarefreeCoefficient,
      zetaMoebiusSievedPrimeCoefficient, hc, he, hsieve]
  · by_cases he : ∃ p ∈ S, p ∣ n
    · have h0 : (S.filter (fun p ↦ p ∣ n)).card ≠ 0 := fun h ↦ hz.mp h he
      have hsieve := hp.mp (by omega)
      simp [zetaOnePrimeSquarefreeCoefficient, zetaSquarefreeCoefficient,
        zetaMoebiusSievedPrimeCoefficient, hc, he, hsieve]
    · simp [zetaOnePrimeSquarefreeCoefficient, hc, he]

/-- The genuine full series on the last selected-prime contribution. -/
def zetaOnePrimeSquarefreeFilter (p : Polynomial ℂ) (D : ℕ)
    (S : Finset ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, zetaOnePrimeSquarefreeCoefficient D S n * zetaPrimeFilterKernel p N s n

/-- The actual sum is the controlled prefix plus the complete finite
ordinary-prime correction, with convergence and all signs established. -/
theorem hasSum_zetaOnePrimeSquarefreeFilter (p : Polynomial ℂ) (D N : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ zetaOnePrimeSquarefreeCoefficient D S n * zetaPrimeFilterKernel p N s n)
      (zetaOnePrimeSquarefreePrefixFilter p D S N s +
        ∑ n ∈ S, (Real.log n : ℂ) * zetaPrimeFilterKernel p N s n) := by
  have hf : HasSum
      (fun n ↦ (if n ∈ S then (Real.log n : ℂ) else 0) * zetaPrimeFilterKernel p N s n)
      (∑ n ∈ S, (if n ∈ S then (Real.log n : ℂ) else 0) * zetaPrimeFilterKernel p N s n) :=
    hasSum_sum_of_ne_finset_zero (s := S)
    (f := fun n ↦ (if n ∈ S then (Real.log n : ℂ) else 0) * zetaPrimeFilterKernel p N s n)
    (by intro n hn; simp [hn])
  have he : (∑ n ∈ S, (if n ∈ S then (Real.log n : ℂ) else 0) * zetaPrimeFilterKernel p N s n) =
      ∑ n ∈ S, (Real.log n : ℂ) * zetaPrimeFilterKernel p N s n :=
    Finset.sum_congr rfl (fun n hn ↦ by rw [if_pos hn])
  rw [he] at hf
  have h := (hasSum_zetaOnePrimeSquarefreePrefixFilter p D N S hS hs).summable.hasSum.add hf
  apply h.congr_fun
  intro n
  rw [zetaOnePrimeSquarefreeCoefficient_eq_prefix_add_primes D hD S hS n, add_mul]

/-- All selected ordinary-prime logarithms have an elementary finite
budget uniform over the selected family and every nonnegative real exponent. -/
theorem sum_primeLog_expWeight_le_square (S : Finset ℕ) (R : ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ R) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∑ p ∈ S, Real.log p * zetaPrimeExpWeight σ p) ≤ (R : ℝ) ^ 2 := by
  have hsub : S ⊆ Finset.Icc 1 R := fun p hp ↦ Finset.mem_Icc.mpr ⟨(hS p hp).1.pos, (hS p hp).2⟩
  have hcard : S.card ≤ R := by simpa using Finset.card_le_card hsub
  calc
    _ ≤ ∑ p ∈ S, Real.log p := by
      apply Finset.sum_le_sum
      intro p _
      have hw : zetaPrimeExpWeight σ p ≤ 1 := Real.exp_le_one_iff.mpr
        (by nlinarith [mul_nonneg hσ (Real.log_natCast_nonneg p)])
      simpa using mul_le_mul_of_nonneg_left hw (Real.log_natCast_nonneg p)
    _ ≤ ∑ _p ∈ S, (R : ℝ) := Finset.sum_le_sum (fun p hp ↦
      (Real.log_le_self (Nat.cast_nonneg p)).trans (by exact_mod_cast (hS p hp).2))
    _ ≤ (R : ℝ) ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact (mul_le_mul_of_nonneg_right (show (S.card : ℝ) ≤ R by exact_mod_cast hcard)
        (Nat.cast_nonneg R)).trans_eq (by ring)

/-- The exact finite prime correction has a uniform polynomial
allowance, retaining the full radius-weighted polynomial filter norm. -/
theorem norm_selectedPrimeFilter_le (p : Polynomial ℂ) (N R : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime ∧ a ≤ R) (y : ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ‖∑ n ∈ S, (Real.log n : ℂ) * zetaPrimeFilterKernel p N (3 / 2 + I * y) n‖ ≤
      (R : ℝ) ^ 2 * r⁻¹ ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  let B := r⁻¹ ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k
  have hB : 0 ≤ B := by dsimp [B]; positivity
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ S, B * (Real.log n * zetaPrimeExpWeight (3 / 2 - r) n) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg n)]
      have hk : ‖zetaPrimeFilterKernel p N (3 / 2 + I * y) n‖ ≤
          r⁻¹ ^ N * zetaPrimeExpWeight (3 / 2 - r) n * ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
        simpa only [show (3 / 2 + I * (y : ℂ)).re = 3 / 2 by simp, zetaPrimeExpWeight] using
          norm_zetaPrimeFilterKernel_le_tilt p N (3 / 2 + I * y)
            (show (1 : ℝ) ≤ n by exact_mod_cast (hS n hn).1.pos) hr
      exact (mul_le_mul_of_nonneg_left hk (Real.log_natCast_nonneg n)).trans_eq (by dsimp [B]; ring)
    _ = B * ∑ n ∈ S, Real.log n * zetaPrimeExpWeight (3 / 2 - r) n := by rw [Finset.mul_sum]
    _ ≤ B * (R : ℝ) ^ 2 := mul_le_mul_of_nonneg_left
      (sum_primeLog_expWeight_le_square S R hS (by linarith)) hB
    _ = _ := by dsimp [B]; ring

/-- The entire one-prime squarefree contribution is independently
bounded, with its complete finite prime correction and every overlap paid. -/
theorem exists_zetaOnePrimeSquarefreeFilter_bound (y : ℝ) (hy : 1 < |y|)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N R : ℕ) (S : Finset ℕ), 1 ≤ D →
      (∀ a ∈ S, a.Prime ∧ a ≤ R) →
      ‖zetaOnePrimeSquarefreeFilter p D S N (3 / 2 + I * y)‖ ≤
        C * (1 + (R : ℝ) ^ 2) * D * Real.exp (4 * Real.sqrt R) * r⁻¹ ^ N *
          ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  obtain ⟨C, hC, hb⟩ := exists_zetaOnePrimeSquarefreePrefixFilter_bound y hy hr hr1
  refine ⟨C + 1, by positivity, ?_⟩
  intro p D N R S hD hS
  rw [zetaOnePrimeSquarefreeFilter,
    (hasSum_zetaOnePrimeSquarefreeFilter p D N hD S (fun a ha ↦ (hS a ha).1) (by norm_num)).tsum_eq]
  apply (norm_add_le _ _).trans
  apply (add_le_add (hb p D N R S hS) (norm_selectedPrimeFilter_le p N R S hS y hr hr1)).trans
  let E : ℝ := D * Real.exp (4 * Real.sqrt R)
  let B := r⁻¹ ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k
  have hE : 1 ≤ E := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hD)
    (Real.one_le_exp_iff.mpr (by positivity))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hR : (R : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 * E := by
    simpa using mul_le_mul_of_nonneg_left hE (sq_nonneg (R : ℝ))
  have hC' : C + (R : ℝ) ^ 2 ≤ (C + 1) * (1 + (R : ℝ) ^ 2) := by
    nlinarith [mul_nonneg hC.le (sq_nonneg (R : ℝ))]
  have hstep := mul_le_mul_of_nonneg_right hC' (by linarith : 0 ≤ E)
  have hsum : C * E + (R : ℝ) ^ 2 ≤ (C + 1) * (1 + (R : ℝ) ^ 2) * E := by
    nlinarith
  have h := mul_le_mul_of_nonneg_right hsum hB
  dsimp [B, E] at h
  convert h using 1 <;> ring

end
end RiemannGaussian
