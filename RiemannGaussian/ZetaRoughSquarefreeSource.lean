/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaOnePrimeSquarefreeBound
import RiemannGaussian.ZetaSquarefreeSource

/-!
# The full source after removing every selected prime

The last selected-prime contribution has an independent vanishing bound
at the actual quadratic cutoff. Its exact complement retains the full
analytic source on squarefree integers avoiding every selected prime.
The finite comparison includes both the old errors and the new deletion.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The unchanged squarefree coefficients on integers avoiding
every selected prime divisor. -/
def zetaRoughSquarefreeCoefficient (D : ℕ) (S : Finset ℕ) (n : ℕ) : ℂ :=
  if ∃ p ∈ S, p ∣ n then 0 else zetaSquarefreeCoefficient D S n

/-- The original squarefree survivor partitions exactly into the
last selected-prime contribution and the full rough complement. -/
theorem zetaSquarefreeCoefficient_eq_onePrime_add_rough (D : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (n : ℕ) :
    zetaSquarefreeCoefficient D S n =
      zetaOnePrimeSquarefreeCoefficient D S n + zetaRoughSquarefreeCoefficient D S n := by
  rw [zetaOnePrimeSquarefreeCoefficient_eq_sieved D S hS n]
  by_cases h : ∃ p ∈ S, p ∣ n <;> simp [zetaRoughSquarefreeCoefficient, h]

/-- The entire rough squarefree arithmetic response with its
original complex filter, phases, and divisor cutoff. -/
def zetaRoughSquarefreeFilter (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, zetaRoughSquarefreeCoefficient D S n * zetaPrimeFilterKernel p N s n

/-- The literal rough squarefree series is genuinely summable in
the Euler half-plane, with no additional cancellation assumption. -/
theorem summable_zetaRoughSquarefreeFilter (p : Polynomial ℂ) (D N : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ zetaRoughSquarefreeCoefficient D S n * zetaPrimeFilterKernel p N s n) := by
  have h := (summable_zetaSquarefreeFilter p D N hD S hS hs).indicator {n | ¬∃ a ∈ S, a ∣ n}
  apply h.congr
  intro n
  by_cases hn : ∃ a ∈ S, a ∣ n <;> simp [Set.indicator, zetaRoughSquarefreeCoefficient, hn]

/-- The coefficient partition commutes with both complete convergent
series, retaining every sign and physical kernel before any estimate. -/
theorem zetaSquarefreeFilter_eq_onePrime_add_rough (p : Polynomial ℂ) (D N : ℕ)
    (hD : 1 ≤ D) (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) {s : ℂ} (hs : 1 < s.re) :
    zetaSquarefreeFilter p D S N s =
      zetaOnePrimeSquarefreeFilter p D S N s + zetaRoughSquarefreeFilter p D S N s := by
  unfold zetaSquarefreeFilter zetaOnePrimeSquarefreeFilter zetaRoughSquarefreeFilter
  simp_rw [zetaSquarefreeCoefficient_eq_onePrime_add_rough D S hS, add_mul]
  exact (hasSum_zetaOnePrimeSquarefreeFilter p D N hD S hS hs).summable.tsum_add
    (summable_zetaRoughSquarefreeFilter p D N hD S hS hs)

/-- The rounded quadratic prime cutoff has its complete fourth-degree
budget at every order, including the initial zero cutoff. -/
theorem zetaRightHalfPrimePatternCutoff_sq_le (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    (zetaRightHalfPrimePatternCutoff rho N : ℝ) ^ 2 ≤
      zetaRightHalfPrimePatternSlope rho ^ 4 * (N : ℝ) ^ 4 := by
  let c := zetaRightHalfPrimePatternSlope rho
  have hc : 0 < c := zetaRightHalfPrimePatternSlope_pos rho hrho
  have hf : (⌊c * (N : ℝ)⌋₊ : ℝ) ≤ c * N := Nat.floor_le (by positivity)
  calc
    _ = (⌊c * (N : ℝ)⌋₊ : ℝ) ^ 4 := by simp [zetaRightHalfPrimePatternCutoff, c]; ring
    _ ≤ (c * (N : ℝ)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hf 4
    _ = _ := mul_pow _ _ _

/-- The full one-prime squarefree contribution has a vanishing
normalized bound at the actual divisor and quadratic prime cutoffs. -/
theorem exists_zetaRightHalfOnePrimeSquarefree_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        zetaOnePrimeSquarefreeFilter (zetaRightHalfPoleJetFilter rho hrho)
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
          (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)‖ ≤
        C * (1 + (N : ℝ) ^ 4) * zetaRightHalfSquareSieveRate rho ^ N := by
  let u : ℝ := 3 / 2 - rho.1.re
  let q := zetaMoebiusHeadGrowth u
  let c := zetaRightHalfPrimePatternSlope rho
  let r := zetaRightHalfSquareSieveRadius rho
  let p := zetaRightHalfPoleJetFilter rho hrho
  let B : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  obtain ⟨hr, hr1, _⟩ := zetaRightHalfSquareSieveRadius_bounds rho hrho
  have hq : 1 ≤ q := (one_lt_zetaMoebiusHeadGrowth hu hu1).le
  have hB : 0 ≤ B := by dsimp [B, r]; positivity
  obtain ⟨C, hC, hb⟩ := exists_zetaOnePrimeSquarefreeFilter_bound rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho) hr hr1
  refine ⟨C * u * B * (1 + c ^ 4) + 1, by positivity, fun N ↦ ?_⟩
  let D := zetaMoebiusGeometricCutoff q N
  have hD : (D : ℝ) ≤ q ^ N := Nat.floor_le (pow_nonneg (by linarith) N)
  have he := exp_primePatternCutoff_sqrt_le rho hrho N
  have hR := zetaRightHalfPrimePatternCutoff_sq_le rho hrho N
  have hbound := hb p D N (zetaRightHalfPrimePatternCutoff rho N)
    (zetaRightHalfPrimePatternPrimes rho N) (zetaRightHalfPoleJetCutoff_pos rho hrho N)
    (zetaRightHalfPrimePatternPrimes_eligible rho N)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (C * (1 + (zetaRightHalfPrimePatternCutoff rho N : ℝ) ^ 2) *
        D * Real.exp (4 * Real.sqrt (zetaRightHalfPrimePatternCutoff rho N)) * r⁻¹ ^ N * B) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ u ^ (N + 1) * (C * (1 + c ^ 4 * (N : ℝ) ^ 4) * q ^ N * q ^ N * r⁻¹ ^ N * B) := by gcongr
    _ = (C * u * B) * (1 + c ^ 4 * (N : ℝ) ^ 4) * ((u * q ^ 2) / r) ^ N := by
      rw [div_pow, mul_pow, pow_succ, show (q ^ 2) ^ N = (q ^ N) ^ 2 by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      simp only [inv_pow, div_eq_mul_inv]
      ring
    _ = (C * u * B) * (1 + c ^ 4 * (N : ℝ) ^ 4) * zetaRightHalfSquareSieveRate rho ^ N := by
      rw [zetaMoebiusHeadGrowth_rate hu]
      rfl
    _ ≤ (C * u * B * (1 + c ^ 4)) * (1 + (N : ℝ) ^ 4) * zetaRightHalfSquareSieveRate rho ^ N := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zetaRightHalfSquareSieveRate_bounds rho hrho).1.le N)
      have hp : 1 + c ^ 4 * (N : ℝ) ^ 4 ≤ (1 + c ^ 4) * (1 + (N : ℝ) ^ 4) := by
        nlinarith [show 0 ≤ c ^ 4 by positivity, show (0 : ℝ) ≤ (N : ℝ) ^ 4 by positivity]
      exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq (by ring)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
      (pow_nonneg (zetaRightHalfSquareSieveRate_bounds rho hrho).1.le N)

/-- The polynomial-times-geometric one-prime allowance tends to zero
for every hypothetical right-half zero. -/
theorem tendsto_zetaRightHalfOnePrimeSquarefreeAllowance (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (C : ℝ) :
    Tendsto (fun N : ℕ ↦ C * (1 + (N : ℝ) ^ 4) * zetaRightHalfSquareSieveRate rho ^ N)
      atTop (𝓝 0) := by
  obtain ⟨h0, h1⟩ := zetaRightHalfSquareSieveRate_bounds rho hrho
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1
  have hn := tendsto_pow_const_mul_const_pow_of_lt_one 4 h0.le h1
  have h := (hp.add hn).const_mul C
  convert h using 1
  · funext N
    ring
  · simp

/-- Every last selected-prime term is included in the independently
vanishing arithmetic response; no overlap or prime correction is assumed small. -/
theorem tendsto_zetaRightHalfOnePrimeSquarefreeFilter (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaOnePrimeSquarefreeFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
        (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_zetaRightHalfOnePrimeSquarefree_error_bound rho hrho
  exact squeeze_zero_norm hb (tendsto_zetaRightHalfOnePrimeSquarefreeAllowance rho hrho C)

/-- The full analytic multiplicity survives on squarefree integers
avoiding every selected prime through the quadratic cutoff. -/
theorem tendsto_zetaRightHalfRoughSquarefreeFilter (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaRoughSquarefreeFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
        (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := (tendsto_zetaRightHalfSquarefreeFilter rho hrho).sub
    (tendsto_zetaRightHalfOnePrimeSquarefreeFilter rho hrho)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [zetaSquarefreeFilter_eq_onePrime_add_rough _ _ N
    (zetaRightHalfPoleJetCutoff_pos rho hrho N) _
    (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1) (by norm_num)]
  ring

/-- The finite comparison with the original analytic source pays
every preceding arithmetic error and the complete last-prime deletion. -/
theorem exists_zetaRightHalfRoughSquarefreeFilter_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ N : ℕ,
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        (zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) -
          zetaRoughSquarefreeFilter (zetaRightHalfPoleJetFilter rho hrho)
            (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
            (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im))‖ ≤
        C₁ * (1 + (N : ℝ) ^ 4) * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
          C₂ * (1 + (N : ℝ) ^ 4) * zetaRightHalfSquareSieveRate rho ^ N := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hb⟩ := exists_zetaRightHalfSquarefreeFilter_error_bound rho hrho
  obtain ⟨C₃, hC₃, hc⟩ := exists_zetaRightHalfOnePrimeSquarefree_error_bound rho hrho
  refine ⟨C₁, C₂ + C₃, hC₁, by positivity, fun N ↦ ?_⟩
  let p := zetaRightHalfPoleJetFilter rho hrho
  let D := zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N
  let S := zetaRightHalfPrimePatternPrimes rho N
  let s : ℂ := 3 / 2 + I * rho.1.im
  have he : zetaRoughSquarefreeFilter p D S N s =
      zetaSquarefreeFilter p D S N s - zetaOnePrimeSquarefreeFilter p D S N s := by
    have h := zetaSquarefreeFilter_eq_onePrime_add_rough p D N
      (zetaRightHalfPoleJetCutoff_pos rho hrho N) S
      (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1) (s := s) (by norm_num [s])
    linear_combination -h
  have halg (a b c : ℂ) : a - (b - c) = a - b + c := by ring
  change ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    (zetaPrimeLogFilter p N s - zetaRoughSquarefreeFilter p D S N s)‖ ≤ _
  rw [he, halg, mul_add]
  apply (norm_add_le _ _).trans
  apply (add_le_add (hb N) (hc N)).trans
  have hpoly : C₂ ≤ C₂ * (1 + (N : ℝ) ^ 4) := by
    nlinarith [pow_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) 4]
  have hrate := mul_le_mul_of_nonneg_right hpoly
    (pow_nonneg (zetaRightHalfSquareSieveRate_bounds rho hrho).1.le N)
  nlinarith

end
end RiemannGaussian
