/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeSource

/-!
# The complete signed source on squarefree surviving integers

All nonsquarefree arithmetic has an independent vanishing allowance,
including every prime square and all overlaps with the quadratic prime
sieve. The full source remains in the physical logarithmic window and
averaged-symbol Fourier region. The exact signed reflection and complete
finite error comparison are retained on the squarefree coefficients.
Their independent strict upper bound remains open.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- Squarefree restriction preserves the original arithmetic majorant
without a new coefficient-bound hypothesis. -/
theorem norm_zetaSquarefreeCoefficient_le (D : ℕ) (S : Finset ℕ) (n : ℕ) :
    ‖zetaSquarefreeCoefficient D S n‖ ≤ zetaMoebiusLogMajorant n := by
  unfold zetaSquarefreeCoefficient
  split_ifs
  · exact norm_zetaMoebiusSievedPrimeCoefficient_le D (primePairFactors S) n
  · simpa only [norm_zero] using zetaMoebiusLogMajorant_nonneg n

/-- The squarefree arithmetic coefficient retains its exact real
value before any physical phase or Fourier transformation. -/
theorem zetaSquarefreeCoefficient_im (D : ℕ) (S : Finset ℕ) (n : ℕ) :
    (zetaSquarefreeCoefficient D S n).im = 0 := by
  unfold zetaSquarefreeCoefficient
  split_ifs
  · exact zetaMoebiusSievedPrimeCoefficient_im D (primePairFactors S) n
  · simp

/-- The original coefficients restricted to squarefree integers by the
simultaneous quadratic prime sieve and physical logarithmic window. -/
def zetaRightHalfSquarefreeWindowCoefficient (rho : NontrivialZetaZero) (N : ℕ) : ℕ → ℂ :=
  zetaLogWindowCoefficient
    (zetaSquarefreeCoefficient
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfPrimePatternPrimes rho N)) N

/-- The new window coefficient is exactly the old quadratic-sieved
window coefficient on squarefree integers, with every remaining value unchanged. -/
theorem zetaRightHalfSquarefreeWindowCoefficient_eq (rho : NontrivialZetaZero) (N n : ℕ) :
    zetaRightHalfSquarefreeWindowCoefficient rho N n =
      if Squarefree n then zetaRightHalfQuadraticWindowCoefficient rho N n else 0 := by
  by_cases hs : Squarefree n <;> by_cases hw : n ∈ zetaLogWindow N <;>
    simp [zetaRightHalfSquarefreeWindowCoefficient, zetaRightHalfQuadraticWindowCoefficient,
      zetaLogWindowCoefficient, zetaSquarefreeCoefficient, zetaRightHalfQuadraticPrimeSieve, hs, hw]

/-- Every retained physical integer is now squarefree as well as
lying beyond the divisor-cutoff square, having two distinct primes,
and having at most one prime through the quadratic small-prime cutoff. -/
theorem zetaRightHalfSquarefreeWindowCoefficient_support (rho : NontrivialZetaZero)
    {N n : ℕ} (hN : 1 ≤ N) (hn : zetaRightHalfSquarefreeWindowCoefficient rho N n ≠ 0) :
    n ∈ zetaLogWindow N ∧
      zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N ^ 2 < n ∧
      Squarefree n ∧
      (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ n ∧ q ∣ n) ∧
      ((zetaRightHalfPrimePatternPrimes rho N).filter (fun p ↦ p ∣ n)).card ≤ 1 := by
  rw [zetaRightHalfSquarefreeWindowCoefficient_eq] at hn
  have hs : Squarefree n := by
    by_contra h
    simp [h] at hn
  rw [if_pos hs] at hn
  obtain ⟨hw, hD, hprimes, hsmall⟩ := zetaRightHalfQuadraticWindowCoefficient_support rho hN hn
  exact ⟨hw, hD, hs, hprimes, hsmall⟩

/-- Every centered complex Fourier product is retained on the actual
squarefree coefficients in the proved smaller frequency region. -/
def zetaRightHalfSquarefreeWindowFourierCarrier (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  zetaArithmeticCenteredPart (zetaRightHalfSquarefreeWindowCoefficient rho N)
    (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
    (zetaMoebiusResonantModes N (zetaAveragedResonanceThreshold N))

/-- The whole negative analytic multiplicity survives the actual
squarefree and quadratic prime sieves and both localizations, with every
premise discharged. -/
theorem tendsto_zetaRightHalfSquarefreeWindowFourierCarrier (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaRightHalfSquarefreeWindowFourierCarrier rho hrho N)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : ‖((3 / 2 - rho.1.re : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [NontrivialZetaZero.re_lt_one rho])]
    linarith
  have hp := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hu).comp (tendsto_add_atTop_nat 1)
  have he := tendsto_zetaArithmeticFilter_sub_averaged_window
    (fun N ↦ zetaSquarefreeCoefficient
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfPrimePatternPrimes rho N))
    (fun N ↦ norm_zetaSquarefreeCoefficient_le _ _)
    (zetaRightHalfPoleJetFilter rho hrho) rho.1.im
  have h := (tendsto_zetaRightHalfSquarefreeFilter rho hrho).sub (hp.mul he)
  simp only [mul_zero, sub_zero] at h
  convert h using 1
  funext N
  dsimp [zetaRightHalfSquarefreeWindowFourierCarrier, zetaRightHalfSquarefreeWindowCoefficient,
    zetaSquarefreeFilter, zetaArithmeticFilter, Function.comp_def]
  ring

/-- One finite comparison pays for the original head and prime powers,
the entire nonsquarefree deletion and quadratic prime-pattern union,
both physical outer shells, and every complementary Fourier interaction. -/
theorem exists_zetaRightHalfSquarefreeWindowFourier_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ N : ℕ, 2 ≤ N →
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        (zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) -
          zetaRightHalfSquarefreeWindowFourierCarrier rho hrho N)‖ ≤
        C₁ * (1 + (N : ℝ) ^ 4) * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
          C₂ * zetaRightHalfSquareSieveRate rho ^ N +
          zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hb⟩ := exists_zetaRightHalfSquarefreeFilter_error_bound rho hrho
  refine ⟨C₁, C₂, hC₁, hC₂, fun N hN ↦ ?_⟩
  let p := zetaRightHalfPoleJetFilter rho hrho
  let a := zetaSquarefreeCoefficient
    (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
    (zetaRightHalfPrimePatternPrimes rho N)
  let u : ℂ := ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1)
  have hu : ‖u‖ ≤ 1 := by
    have hu0 : 0 ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
    dsimp [u]
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
    exact pow_le_one₀ hu0 (by linarith)
  have he : u * (zetaPrimeLogFilter p N (3 / 2 + I * rho.1.im) -
      zetaRightHalfSquarefreeWindowFourierCarrier rho hrho N) =
      u * (zetaPrimeLogFilter p N (3 / 2 + I * rho.1.im) -
        zetaArithmeticFilter a p N (3 / 2 + I * rho.1.im)) +
      u * (zetaArithmeticFilter a p N (3 / 2 + I * rho.1.im) -
        zetaRightHalfSquarefreeWindowFourierCarrier rho hrho N) := by ring
  change ‖u * (zetaPrimeLogFilter p N (3 / 2 + I * rho.1.im) -
    zetaRightHalfSquarefreeWindowFourierCarrier rho hrho N)‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add (hb N)
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_right hu (norm_nonneg _)).trans
  simpa only [one_mul, zetaRightHalfSquarefreeWindowFourierCarrier, zetaRightHalfSquarefreeWindowCoefficient, p, a]
    using norm_zetaArithmeticFilter_sub_averaged_window_le a
    (norm_zetaSquarefreeCoefficient_le _ _) p N rho.1.im hN

/-- The complete finite allowance vanishes, with both arithmetic sieves
and all physical and frequency errors present in the same expression. -/
theorem tendsto_zetaRightHalfSquarefreeWindowTotalError (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (C₁ C₂ : ℝ) :
    Tendsto (fun N : ℕ ↦ C₁ * (1 + (N : ℝ) ^ 4) * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
      C₂ * zetaRightHalfSquareSieveRate rho ^ N +
      zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im)
      atTop (𝓝 0) := by
  obtain ⟨h0, h1⟩ := zetaRightHalfSquareSieveRate_bounds rho hrho
  have hrate := (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).const_mul C₂
  have h := ((tendsto_zetaRightHalfPrimePatternAllowance rho hrho C₁).add hrate).add
    (tendsto_zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) rho.1.im)
  simpa only [mul_zero, add_zero] using h

/-- The exact signed odd-reflection work of the actual surviving
coefficients, including every centered Fourier product and cyclic partner. -/
def zetaRightHalfSquarefreeWindowReflectionWork (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℝ :=
  zetaArithmeticReflectionWork (zetaRightHalfSquarefreeWindowCoefficient rho N)
    (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
    (zetaMoebiusResonantModes N (zetaAveragedResonanceThreshold N))

/-- Exact physical reflection cancellation commutes with the squarefree
restriction, quadratic prime sieve, and smaller frequency region,
retaining every centering term. -/
theorem zetaRightHalfSquarefreeWindowFourierCarrier_re_eq_reflection (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    (zetaRightHalfSquarefreeWindowFourierCarrier rho hrho N).re =
      -2 * zetaRightHalfSquarefreeWindowReflectionWork rho hrho N :=
  zetaArithmeticCenteredPart_re_eq_reflection _
    (zetaLogWindowCoefficient_im _ (zetaSquarefreeCoefficient_im _ _) N)
    _ _ _ _ (zetaMoebiusResonantModes_neg_closed N _)

/-- The signed surviving correlation still carries half the full
analytic multiplicity. Its independent strict upper bound remains open. -/
theorem tendsto_zetaRightHalfSquarefreeWindowReflectionWork (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ (3 / 2 - rho.1.re : ℝ) ^ (N + 1) *
      zetaRightHalfSquarefreeWindowReflectionWork rho hrho N)
      atTop (𝓝 ((analyticZetaZeroMultiplicity rho : ℝ) / 2)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_zetaRightHalfSquarefreeWindowFourierCarrier rho hrho)
  simp only [Function.comp_def, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Complex.neg_re, Complex.natCast_re, zetaRightHalfSquarefreeWindowFourierCarrier_re_eq_reflection] at h
  have ht := h.mul_const (-(1 / 2 : ℝ))
  convert ht using 1
  · funext N
    ring
  · congr 1
    ring

/-- The finite signed comparison with the original analytic source
retains the entire independently vanishing allowance, with the exact
reflection normalization. No surviving arithmetic term is discarded. -/
theorem exists_zetaRightHalfSquarefreeWindowReflection_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ N : ℕ, 2 ≤ N →
      |-(3 / 2 - rho.1.re : ℝ) ^ (N + 1) *
          (zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N
            (3 / 2 + I * rho.1.im)).re / 2 -
        (3 / 2 - rho.1.re : ℝ) ^ (N + 1) * zetaRightHalfSquarefreeWindowReflectionWork rho hrho N| ≤
        (C₁ * (1 + (N : ℝ) ^ 4) * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
          C₂ * zetaRightHalfSquareSieveRate rho ^ N +
          zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im) / 2 := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hb⟩ := exists_zetaRightHalfSquarefreeWindowFourier_error_bound rho hrho
  refine ⟨C₁, C₂, hC₁, hC₂, fun N hN ↦ ?_⟩
  let L := zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im)
  let u : ℝ := (3 / 2 - rho.1.re) ^ (N + 1)
  let z : ℂ := ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    (L - zetaRightHalfSquarefreeWindowFourierCarrier rho hrho N)
  have hz : z.re = u * (L.re + 2 * zetaRightHalfSquarefreeWindowReflectionWork rho hrho N) := by
    dsimp [z, u]
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.sub_re,
      zetaRightHalfSquarefreeWindowFourierCarrier_re_eq_reflection]
    ring
  change |-u * L.re / 2 - u * zetaRightHalfSquarefreeWindowReflectionWork rho hrho N| ≤ _
  have he : -u * L.re / 2 - u * zetaRightHalfSquarefreeWindowReflectionWork rho hrho N = -z.re / 2 := by
    rw [hz]
    ring
  rw [he, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right ((Complex.abs_re_le_norm z).trans (hb N hN)) (by norm_num)

end
end RiemannGaussian
