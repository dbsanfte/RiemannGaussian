/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimePatternResponse
import RiemannGaussian.ZetaMoebiusSievedPrimeTail

/-!
# A quadratic prime cutoff with a discharged complete overlap allowance

The selected primes extend to the square of an explicit linear cutoff.
The exact prime-pattern sieve deletes every integer having at least two
selected prime divisors. Its full signed arithmetic response has a proved
polynomial-times-geometric bound at each hypothetical right-half zero.
No coefficient search or unproved overlap-cost hypothesis is used.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The explicit slope whose exponential exactly matches the original
divisor-growth base after paying the complete overlap cost. -/
def zetaRightHalfPrimePatternSlope (rho : NontrivialZetaZero) : ℝ :=
  Real.log (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) / 8

/-- The slope is strictly positive at every hypothetical right-half zero. -/
theorem zetaRightHalfPrimePatternSlope_pos (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) : 0 < zetaRightHalfPrimePatternSlope rho := by
  apply div_pos _ (by norm_num)
  exact Real.log_pos (one_lt_zetaMoebiusHeadGrowth
    (by linarith [NontrivialZetaZero.re_lt_one rho]) (by linarith))

/-- The quadratic selected-prime cutoff, with exact integer rounding. -/
def zetaRightHalfPrimePatternCutoff (rho : NontrivialZetaZero) (N : ℕ) : ℕ :=
  ⌊zetaRightHalfPrimePatternSlope rho * (N : ℝ)⌋₊ ^ 2

/-- Every fixed prime eventually lies below the explicit quadratic cutoff. -/
theorem tendsto_zetaRightHalfPrimePatternCutoff (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (zetaRightHalfPrimePatternCutoff rho) atTop atTop := by
  have hreal : Tendsto (fun N : ℕ ↦ zetaRightHalfPrimePatternSlope rho * (N : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (zetaRightHalfPrimePatternSlope_pos rho hrho)
  have hf := tendsto_nat_floor_atTop.comp hreal
  apply tendsto_atTop_mono _ hf
  intro N
  dsimp [zetaRightHalfPrimePatternCutoff]
  nlinarith

/-- All primes through the quadratic cutoff are selected simultaneously. -/
def zetaRightHalfPrimePatternPrimes (rho : NontrivialZetaZero) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (zetaRightHalfPrimePatternCutoff rho N)).filter Nat.Prime

/-- The selected family has its exact prime and size conditions at
every order, including the empty initial selections. -/
theorem zetaRightHalfPrimePatternPrimes_eligible (rho : NontrivialZetaZero) (N : ℕ) :
    ∀ p ∈ zetaRightHalfPrimePatternPrimes rho N,
      p.Prime ∧ p ≤ zetaRightHalfPrimePatternCutoff rho N := by
  intro p hp
  obtain ⟨hI, hprime⟩ := Finset.mem_filter.mp hp
  exact ⟨hprime, (Finset.mem_Icc.mp hI).2⟩

/-- The complete cost of this actual simultaneous sieve is bounded
without an overlap assumption, including its logarithmic companion. -/
theorem primePatternSieveCost_actual_le (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    primePatternSieveCost (zetaRightHalfPrimePatternPrimes rho N) ≤
      (1 + zetaRightHalfPrimePatternSlope rho ^ 4 * (N : ℝ) ^ 4) *
        zetaMoebiusHeadGrowth (3 / 2 - rho.1.re) ^ N := by
  let c := zetaRightHalfPrimePatternSlope rho
  let q := zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)
  have hc : 0 < c := zetaRightHalfPrimePatternSlope_pos rho hrho
  have hq : 0 < q := (one_lt_zetaMoebiusHeadGrowth
    (by linarith [NontrivialZetaZero.re_lt_one rho]) (by linarith)).trans' (by norm_num)
  have hf : (⌊c * (N : ℝ)⌋₊ : ℝ) ≤ c * N := Nat.floor_le (by positivity)
  have hs : Real.sqrt (zetaRightHalfPrimePatternCutoff rho N) = (⌊c * (N : ℝ)⌋₊ : ℝ) := by
    simp [zetaRightHalfPrimePatternCutoff, c]
  have hexp : Real.exp (8 * Real.sqrt (zetaRightHalfPrimePatternCutoff rho N)) ≤ q ^ N := by
    rw [hs]
    calc
      _ ≤ Real.exp (8 * (c * (N : ℝ))) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp ((N : ℝ) * Real.log q) := by
        congr 1
        dsimp [c, zetaRightHalfPrimePatternSlope, q]
        ring
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log hq]
  have hpoly : (zetaRightHalfPrimePatternCutoff rho N : ℝ) ^ 2 ≤ c ^ 4 * (N : ℝ) ^ 4 := by
    calc
      _ = (⌊c * (N : ℝ)⌋₊ : ℝ) ^ 4 := by simp [zetaRightHalfPrimePatternCutoff, c]; ring
      _ ≤ (c * (N : ℝ)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hf 4
      _ = _ := mul_pow _ _ _
  exact (primePatternSieveCost_le_exp_sqrt _ _ (zetaRightHalfPrimePatternPrimes_eligible rho N)).trans
    (mul_le_mul (by linarith : (1 : ℝ) + (zetaRightHalfPrimePatternCutoff rho N : ℝ) ^ 2 ≤
      1 + c ^ 4 * (N : ℝ) ^ 4) hexp (Real.exp_pos _).le (by positivity))

/-- The entire actual prime-pattern union has a finite normalized
error bound. Every overlap, source-scale factor and integer cutoff is included. -/
theorem exists_zetaRightHalfPrimePattern_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        zetaMoebiusPrimePatternFilter (zetaRightHalfPoleJetFilter rho hrho)
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
          (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)‖ ≤
        C * (1 + (N : ℝ) ^ 4) * (Real.sqrt (3 / 2 - rho.1.re)) ^ N := by
  let u : ℝ := 3 / 2 - rho.1.re
  let q := zetaMoebiusHeadGrowth u
  let c := zetaRightHalfPrimePatternSlope rho
  let p := zetaRightHalfPoleJetFilter rho hrho
  let B : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hq : 1 ≤ q := (one_lt_zetaMoebiusHeadGrowth hu hu1).le
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  obtain ⟨C, hC, hb⟩ := exists_zetaMoebiusPrimePatternFilter_bound rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho)
  refine ⟨C * u * B * (1 + c ^ 4) + 1, by positivity, ?_⟩
  intro N
  let D := zetaMoebiusGeometricCutoff q N
  have hD : (D : ℝ) ≤ q ^ N := Nat.floor_le (pow_nonneg (by linarith) N)
  have hqN : 1 ≤ q ^ N := one_le_pow₀ hq
  have hsqrt : Real.sqrt (D : ℝ) ≤ q ^ N := Real.sqrt_le_iff.mpr
    ⟨by positivity, hD.trans (by nlinarith)⟩
  have hcost := primePatternSieveCost_actual_le rho hrho N
  have hbound := hb p D N (zetaRightHalfPrimePatternPrimes rho N)
    (fun r hr ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N r hr).1)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (C * Real.sqrt D * B * primePatternSieveCost (zetaRightHalfPrimePatternPrimes rho N)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ u ^ (N + 1) * (C * q ^ N * B * ((1 + c ^ 4 * (N : ℝ) ^ 4) * q ^ N)) := by
      gcongr
      · exact primePatternSieveCost_nonneg _
    _ = (C * u * B) * (1 + c ^ 4 * (N : ℝ) ^ 4) * (u * q ^ 2) ^ N := by
      rw [mul_pow, pow_succ, show (q ^ 2) ^ N = (q ^ N) ^ 2 by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      ring
    _ = (C * u * B) * (1 + c ^ 4 * (N : ℝ) ^ 4) * (Real.sqrt u) ^ N := by
      rw [zetaMoebiusHeadGrowth_rate hu]
    _ ≤ (C * u * B) * ((1 + c ^ 4) * (1 + (N : ℝ) ^ 4)) * (Real.sqrt u) ^ N := by
      gcongr
      nlinarith [show 0 ≤ c ^ 4 by positivity, show (0 : ℝ) ≤ (N : ℝ) ^ 4 by positivity]
    _ = (C * u * B * (1 + c ^ 4)) * (1 + (N : ℝ) ^ 4) * (Real.sqrt u) ^ N := by ring
    _ ≤ _ := by gcongr; linarith

/-- The complete polynomial-times-geometric allowance vanishes for
every hypothetical right-half zero. -/
theorem tendsto_zetaRightHalfPrimePatternAllowance (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (C : ℝ) :
    Tendsto (fun N : ℕ ↦ C * (1 + (N : ℝ) ^ 4) *
      (Real.sqrt (3 / 2 - rho.1.re)) ^ N) atTop (𝓝 0) := by
  have hu : 0 ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have h1 : Real.sqrt (3 / 2 - rho.1.re) < 1 := by
    nlinarith [Real.sq_sqrt hu, Real.sqrt_nonneg (3 / 2 - rho.1.re)]
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.sqrt_nonneg _) h1
  have hn := tendsto_pow_const_mul_const_pow_of_lt_one 4 (Real.sqrt_nonneg _) h1
  have h := (hp.add hn).const_mul C
  convert h using 1
  · funext N
    ring
  · simp

/-- The actual simultaneous deletion over all selected primes has
independent decay, with its complete overlap budget already discharged. -/
theorem tendsto_zetaRightHalfPrimePatternFilter (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaMoebiusPrimePatternFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
        (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_zetaRightHalfPrimePattern_error_bound rho hrho
  exact squeeze_zero_norm hb (tendsto_zetaRightHalfPrimePatternAllowance rho hrho C)

/-- The original simultaneous divisibility sieve over every pair of
selected primes, using the explicit quadratic prime cutoff. -/
def zetaRightHalfQuadraticPrimeSieve (rho : NontrivialZetaZero) (N : ℕ) : Finset ℕ :=
  primePairFactors (zetaRightHalfPrimePatternPrimes rho N)

/-- All selected pair factors satisfy the original sieve's analytic
eligibility conditions, with no remaining arithmetic premise. -/
theorem zetaRightHalfQuadraticPrimeSieve_eligible (rho : NontrivialZetaZero) (N : ℕ) :
    ∀ P ∈ zetaRightHalfQuadraticPrimeSieve rho N, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P :=
  primePairFactors_eligible _ (fun p hp ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N p hp).1)

/-- The literal surviving arithmetic series retains the whole analytic
multiplicity after every pair of selected primes is removed simultaneously. -/
theorem tendsto_zetaRightHalfQuadraticSievedPrimeTail (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaMoebiusSievedPrimeFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
        (zetaRightHalfQuadraticPrimeSieve rho N) N (3 / 2 + I * rho.1.im))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := (tendsto_zetaRightHalfDistinctPrimeTail rho hrho).sub
    (tendsto_zetaRightHalfPrimePatternFilter rho hrho)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [zetaMoebiusSievedPrimeFilter,
    (hasSum_zetaMoebiusSievedPrimeFilter _ _ N (zetaRightHalfPoleJetCutoff_pos rho hrho N) _
      (zetaRightHalfQuadraticPrimeSieve_eligible rho N) (by norm_num)).tsum_eq,
    zetaMoebiusPrimePatternFilter_eq_sieve _ _ _ _
      (fun p hp ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N p hp).1), mul_sub]
  rfl

/-- The entire original pole-jet response differs from the actual
survivor by one proved allowance. The finite head, prime powers, and
complete simultaneous prime-pattern union are all included. -/
theorem exists_zetaRightHalfQuadraticSievedPrimeTail_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        (zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) -
          zetaMoebiusSievedPrimeFilter (zetaRightHalfPoleJetFilter rho hrho)
            (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
            (zetaRightHalfQuadraticPrimeSieve rho N) N (3 / 2 + I * rho.1.im))‖ ≤
        C * (1 + (N : ℝ) ^ 4) * (Real.sqrt (3 / 2 - rho.1.re)) ^ N := by
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_zetaRightHalfDistinctPrimeTail_error_bound rho hrho
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_zetaRightHalfPrimePattern_error_bound rho hrho
  refine ⟨C₁ + C₂, by positivity, fun N ↦ ?_⟩
  have h := hb₂ N
  rw [zetaMoebiusPrimePatternFilter_eq_sieve _ _ _ _
    (fun p hp ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N p hp).1)] at h
  have halg (a b c : ℂ) : a - (b - c) = a - b + c := by ring
  rw [zetaMoebiusSievedPrimeFilter,
    (hasSum_zetaMoebiusSievedPrimeFilter _ _ N (zetaRightHalfPoleJetCutoff_pos rho hrho N) _
      (zetaRightHalfQuadraticPrimeSieve_eligible rho N) (by norm_num)).tsum_eq, halg, mul_add]
  apply (norm_add_le _ _).trans
  apply (add_le_add (hb₁ N) h).trans
  have hpoly : C₁ ≤ C₁ * (1 + (N : ℝ) ^ 4) := by nlinarith [pow_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) 4]
  nlinarith [mul_le_mul_of_nonneg_right hpoly (pow_nonneg (Real.sqrt_nonneg (3 / 2 - rho.1.re)) N)]

end
end RiemannGaussian
