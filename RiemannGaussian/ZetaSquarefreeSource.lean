/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeSieve
import RiemannGaussian.ZetaQuadraticWindowSource

/-!
# The full source survives deletion of every nonsquarefree integer

The explicit Cauchy radius retains enough margin for the original
quadratic prime sieve and all prime-square overlaps simultaneously.
The entire nonsquarefree response has independent geometric decay.
The actual squarefree survivor retains the complete analytic source
and one finite comparison with every original arithmetic error included.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The radius between the existing source-growth allowance and one,
leaving both a positive square-summability margin and strict geometric decay. -/
def zetaRightHalfSquareSieveRadius (rho : NontrivialZetaZero) : ℝ :=
  (1 + Real.sqrt (3 / 2 - rho.1.re)) / 2

/-- The selected radius is positive, below one, and strictly exceeds
the growth base after the entire first-power and square overlap costs. -/
theorem zetaRightHalfSquareSieveRadius_bounds (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    0 < zetaRightHalfSquareSieveRadius rho ∧ zetaRightHalfSquareSieveRadius rho < 1 ∧
      Real.sqrt (3 / 2 - rho.1.re) < zetaRightHalfSquareSieveRadius rho := by
  have hu : 0 ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hs : Real.sqrt (3 / 2 - rho.1.re) < 1 := by
    nlinarith [Real.sq_sqrt hu, Real.sqrt_nonneg (3 / 2 - rho.1.re)]
  unfold zetaRightHalfSquareSieveRadius
  constructor
  · positivity
  · constructor <;> linarith

/-- The exact rate after all first-power and square-overlap costs. -/
def zetaRightHalfSquareSieveRate (rho : NontrivialZetaZero) : ℝ :=
  Real.sqrt (3 / 2 - rho.1.re) / zetaRightHalfSquareSieveRadius rho

/-- The complete nonsquarefree allowance has a strictly decaying
geometric base at every hypothetical right-half zero. -/
theorem zetaRightHalfSquareSieveRate_bounds (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    0 < zetaRightHalfSquareSieveRate rho ∧ zetaRightHalfSquareSieveRate rho < 1 := by
  obtain ⟨hr, _, hs⟩ := zetaRightHalfSquareSieveRadius_bounds rho hrho
  exact ⟨div_pos (Real.sqrt_pos.mpr (by linarith [NontrivialZetaZero.re_lt_one rho])) hr,
    (div_lt_one hr).mpr hs⟩

/-- The original rounded quadratic prime cutoff fits the complete
square-intersection exponential cost at every order. -/
theorem exp_primePatternCutoff_sqrt_le (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    Real.exp (4 * Real.sqrt (zetaRightHalfPrimePatternCutoff rho N)) ≤
      zetaMoebiusHeadGrowth (3 / 2 - rho.1.re) ^ N := by
  let c := zetaRightHalfPrimePatternSlope rho
  let q := zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)
  have hc : 0 < c := zetaRightHalfPrimePatternSlope_pos rho hrho
  have hq : 0 < q := (one_lt_zetaMoebiusHeadGrowth
    (by linarith [NontrivialZetaZero.re_lt_one rho]) (by linarith)).trans' (by norm_num)
  have hf : (⌊c * (N : ℝ)⌋₊ : ℝ) ≤ c * N := Nat.floor_le (by positivity)
  have hs : Real.sqrt (zetaRightHalfPrimePatternCutoff rho N) = (⌊c * (N : ℝ)⌋₊ : ℝ) := by
    simp [zetaRightHalfPrimePatternCutoff, c]
  rw [hs]
  calc
    _ ≤ Real.exp (8 * (c * (N : ℝ))) := Real.exp_le_exp.mpr (by
      nlinarith [show (0 : ℝ) ≤ (⌊c * (N : ℝ)⌋₊ : ℝ) by positivity])
    _ = Real.exp ((N : ℝ) * Real.log q) := by
      congr 1
      dsimp [c, zetaRightHalfPrimePatternSlope, q]
      ring
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log hq]

/-- The entire actual nonsquarefree contribution is bounded by one
strictly decaying geometric allowance. Every prime square and all of
its overlaps with the quadratic prime sieve have already been included. -/
theorem exists_zetaRightHalfNonsquarefree_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        zetaNonsquarefreeFilter (zetaRightHalfPoleJetFilter rho hrho)
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
          (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)‖ ≤
        C * zetaRightHalfSquareSieveRate rho ^ N := by
  let u : ℝ := 3 / 2 - rho.1.re
  let q := zetaMoebiusHeadGrowth u
  let r := zetaRightHalfSquareSieveRadius rho
  let p := zetaRightHalfPoleJetFilter rho hrho
  let B : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  obtain ⟨hr, hr1, _⟩ := zetaRightHalfSquareSieveRadius_bounds rho hrho
  have hq : 1 ≤ q := (one_lt_zetaMoebiusHeadGrowth hu hu1).le
  have hB : 0 ≤ B := by dsimp [B, r]; positivity
  obtain ⟨C, hC, hb⟩ := exists_zetaNonsquarefreeFilter_bound rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho) hr hr1
  refine ⟨C * u * B + 1, by positivity, fun N ↦ ?_⟩
  let D := zetaMoebiusGeometricCutoff q N
  have hD : (D : ℝ) ≤ q ^ N := Nat.floor_le (pow_nonneg (by linarith) N)
  have he := exp_primePatternCutoff_sqrt_le rho hrho N
  have hbound := hb p D N (zetaRightHalfPrimePatternCutoff rho N)
    (zetaRightHalfPrimePatternPrimes rho N) (zetaRightHalfPoleJetCutoff_pos rho hrho N)
    (zetaRightHalfPrimePatternPrimes_eligible rho N)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (C * D * Real.exp (4 * Real.sqrt (zetaRightHalfPrimePatternCutoff rho N)) * r⁻¹ ^ N * B) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ u ^ (N + 1) * (C * q ^ N * q ^ N * r⁻¹ ^ N * B) := by gcongr
    _ = (C * u * B) * ((u * q ^ 2) / r) ^ N := by
      rw [div_pow, mul_pow, pow_succ, show (q ^ 2) ^ N = (q ^ N) ^ 2 by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      simp only [inv_pow, div_eq_mul_inv]
      ring
    _ = (C * u * B) * zetaRightHalfSquareSieveRate rho ^ N := by
      rw [zetaMoebiusHeadGrowth_rate hu]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith)
      (pow_nonneg (zetaRightHalfSquareSieveRate_bounds rho hrho).1.le N)

/-- The full original repeated-prime response tends to zero at the
hypothetical-zero normalization, with every infinite square included. -/
theorem tendsto_zetaRightHalfNonsquarefreeFilter (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaNonsquarefreeFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
        (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_zetaRightHalfNonsquarefree_error_bound rho hrho
  obtain ⟨h0, h1⟩ := zetaRightHalfSquareSieveRate_bounds rho hrho
  apply squeeze_zero_norm hb
  simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).const_mul C

/-- The full original multiplicity source survives on the literal
squarefree arithmetic sequence after the quadratic prime sieve. -/
theorem tendsto_zetaRightHalfSquarefreeFilter (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaSquarefreeFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
        (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := (tendsto_zetaRightHalfQuadraticSievedPrimeTail rho hrho).sub
    (tendsto_zetaRightHalfNonsquarefreeFilter rho hrho)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [zetaRightHalfQuadraticPrimeSieve,
    zetaMoebiusSievedPrimeFilter_eq_squarefree_add_nonsquarefree _ _ N
      (zetaRightHalfPoleJetCutoff_pos rho hrho N) _
      (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1) (by norm_num)]
  ring

/-- The finite comparison with the original pole-jet response pays
all earlier arithmetic errors and the complete nonsquarefree deletion. -/
theorem exists_zetaRightHalfSquarefreeFilter_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ N : ℕ,
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        (zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) -
          zetaSquarefreeFilter (zetaRightHalfPoleJetFilter rho hrho)
            (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
            (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im))‖ ≤
        C₁ * (1 + (N : ℝ) ^ 4) * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
          C₂ * zetaRightHalfSquareSieveRate rho ^ N := by
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_zetaRightHalfQuadraticSievedPrimeTail_error_bound rho hrho
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_zetaRightHalfNonsquarefree_error_bound rho hrho
  refine ⟨C₁, C₂, hC₁, hC₂, fun N ↦ ?_⟩
  let p := zetaRightHalfPoleJetFilter rho hrho
  let D := zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N
  let S := zetaRightHalfPrimePatternPrimes rho N
  let s : ℂ := 3 / 2 + I * rho.1.im
  have he : zetaSquarefreeFilter p D S N s = zetaMoebiusSievedPrimeFilter p D (primePairFactors S) N s -
      zetaNonsquarefreeFilter p D S N s := by
    have h := zetaMoebiusSievedPrimeFilter_eq_squarefree_add_nonsquarefree p D N
      (zetaRightHalfPoleJetCutoff_pos rho hrho N) S
      (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1) (s := s) (by norm_num [s])
    linear_combination -h
  have halg (a b c : ℂ) : a - (b - c) = a - b + c := by ring
  change ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    (zetaPrimeLogFilter p N s - zetaSquarefreeFilter p D S N s)‖ ≤ _
  rw [he, halg, mul_add]
  exact (norm_add_le _ _).trans (add_le_add (hb₁ N) (hb₂ N))

end
end RiemannGaussian
