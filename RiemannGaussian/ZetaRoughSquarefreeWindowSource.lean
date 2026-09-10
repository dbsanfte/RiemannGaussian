/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRoughSquarefreeSource
import RiemannGaussian.ZetaSquarefreeWindowSource

/-!
# The complete signed source on rough squarefree integers

The entire last selected-prime contribution has an independent vanishing
allowance. Every remaining prime divisor exceeds the actual quadratic
cutoff. The full original signed source, physical window, averaged Fourier
region, exact odd reflection and complete finite error remain together.
The strict upper bound for this whole surviving correlation remains open.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- Avoiding every selected prime preserves the original arithmetic
majorant with no new coefficient-bound hypothesis. -/
theorem norm_zetaRoughSquarefreeCoefficient_le (D : ℕ) (S : Finset ℕ) (n : ℕ) :
    ‖zetaRoughSquarefreeCoefficient D S n‖ ≤ zetaMoebiusLogMajorant n := by
  unfold zetaRoughSquarefreeCoefficient
  split_ifs
  · simpa only [norm_zero] using zetaMoebiusLogMajorant_nonneg n
  · exact norm_zetaSquarefreeCoefficient_le D S n

/-- The surviving coefficient retains its exact real value before
any physical phase or Fourier transformation is applied. -/
theorem zetaRoughSquarefreeCoefficient_im (D : ℕ) (S : Finset ℕ) (n : ℕ) :
    (zetaRoughSquarefreeCoefficient D S n).im = 0 := by
  unfold zetaRoughSquarefreeCoefficient
  split_ifs
  · simp
  · exact zetaSquarefreeCoefficient_im D S n

/-- The original coefficients restricted to squarefree integers by the
simultaneous quadratic prime sieve and physical logarithmic window. -/
def zetaRightHalfRoughSquarefreeWindowCoefficient (rho : NontrivialZetaZero) (N : ℕ) : ℕ → ℂ :=
  zetaLogWindowCoefficient
    (zetaRoughSquarefreeCoefficient
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfPrimePatternPrimes rho N)) N

/-- The new coefficient is exactly the original squarefree window
coefficient on integers avoiding all selected primes, and zero elsewhere. -/
theorem zetaRightHalfRoughSquarefreeWindowCoefficient_eq (rho : NontrivialZetaZero) (N n : ℕ) :
    zetaRightHalfRoughSquarefreeWindowCoefficient rho N n =
      if ∃ p ∈ zetaRightHalfPrimePatternPrimes rho N, p ∣ n then 0
        else zetaRightHalfSquarefreeWindowCoefficient rho N n := by
  by_cases hs : ∃ p ∈ zetaRightHalfPrimePatternPrimes rho N, p ∣ n <;>
    by_cases hw : n ∈ zetaLogWindow N <;>
    simp [zetaRightHalfRoughSquarefreeWindowCoefficient, zetaRightHalfSquarefreeWindowCoefficient,
      zetaLogWindowCoefficient, zetaRoughSquarefreeCoefficient, hs, hw]

/-- Every remaining physical integer is squarefree and has at least
two prime divisors, each strictly exceeding the full quadratic prime cutoff. -/
theorem zetaRightHalfRoughSquarefreeWindowCoefficient_support (rho : NontrivialZetaZero)
    {N n : ℕ} (hN : 1 ≤ N) (hn : zetaRightHalfRoughSquarefreeWindowCoefficient rho N n ≠ 0) :
    n ∈ zetaLogWindow N ∧
      zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N ^ 2 < n ∧
      Squarefree n ∧
      (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ n ∧ q ∣ n) ∧
      (∀ p : ℕ, p.Prime → p ∣ n → zetaRightHalfPrimePatternCutoff rho N < p) := by
  rw [zetaRightHalfRoughSquarefreeWindowCoefficient_eq] at hn
  have hs : ¬∃ p ∈ zetaRightHalfPrimePatternPrimes rho N, p ∣ n := by
    intro h
    simp [h] at hn
  rw [if_neg hs] at hn
  obtain ⟨hw, hD, hsq, hprimes, _⟩ := zetaRightHalfSquarefreeWindowCoefficient_support rho hN hn
  refine ⟨hw, hD, hsq, hprimes, fun p hp hpn ↦ ?_⟩
  by_contra h
  exact hs ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.pos, by omega⟩, hp⟩, hpn⟩

/-- Every centered complex Fourier product is retained on the actual
squarefree coefficients in the proved smaller frequency region. -/
def zetaRightHalfRoughSquarefreeWindowFourierCarrier (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  zetaArithmeticCenteredPart (zetaRightHalfRoughSquarefreeWindowCoefficient rho N)
    (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
    (zetaMoebiusResonantModes N (zetaAveragedResonanceThreshold N))

/-- The whole negative analytic multiplicity survives the actual
squarefree and quadratic prime sieves and both localizations, with every
premise discharged. -/
theorem tendsto_zetaRightHalfRoughSquarefreeWindowFourierCarrier (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho N)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : ‖((3 / 2 - rho.1.re : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [NontrivialZetaZero.re_lt_one rho])]
    linarith
  have hp := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hu).comp (tendsto_add_atTop_nat 1)
  have he := tendsto_zetaArithmeticFilter_sub_averaged_window
    (fun N ↦ zetaRoughSquarefreeCoefficient
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfPrimePatternPrimes rho N))
    (fun N ↦ norm_zetaRoughSquarefreeCoefficient_le _ _)
    (zetaRightHalfPoleJetFilter rho hrho) rho.1.im
  have h := (tendsto_zetaRightHalfRoughSquarefreeFilter rho hrho).sub (hp.mul he)
  simp only [mul_zero, sub_zero] at h
  convert h using 1
  funext N
  dsimp [zetaRightHalfRoughSquarefreeWindowFourierCarrier, zetaRightHalfRoughSquarefreeWindowCoefficient,
    zetaRoughSquarefreeFilter, zetaArithmeticFilter, Function.comp_def]
  ring

/-- One finite comparison pays for the original head and prime powers,
the entire square and last-prime deletions and quadratic prime-pattern union,
both physical outer shells, and every complementary Fourier interaction. -/
theorem exists_zetaRightHalfRoughSquarefreeWindowFourier_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ N : ℕ, 2 ≤ N →
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        (zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) -
          zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho N)‖ ≤
        C₁ * (1 + (N : ℝ) ^ 4) * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
          C₂ * (1 + (N : ℝ) ^ 4) * zetaRightHalfSquareSieveRate rho ^ N +
          zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hb⟩ := exists_zetaRightHalfRoughSquarefreeFilter_error_bound rho hrho
  refine ⟨C₁, C₂, hC₁, hC₂, fun N hN ↦ ?_⟩
  let p := zetaRightHalfPoleJetFilter rho hrho
  let a := zetaRoughSquarefreeCoefficient
    (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
    (zetaRightHalfPrimePatternPrimes rho N)
  let u : ℂ := ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1)
  have hu : ‖u‖ ≤ 1 := by
    have hu0 : 0 ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
    dsimp [u]
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
    exact pow_le_one₀ hu0 (by linarith)
  have he : u * (zetaPrimeLogFilter p N (3 / 2 + I * rho.1.im) -
      zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho N) =
      u * (zetaPrimeLogFilter p N (3 / 2 + I * rho.1.im) -
        zetaArithmeticFilter a p N (3 / 2 + I * rho.1.im)) +
      u * (zetaArithmeticFilter a p N (3 / 2 + I * rho.1.im) -
        zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho N) := by ring
  change ‖u * (zetaPrimeLogFilter p N (3 / 2 + I * rho.1.im) -
    zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho N)‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add (hb N)
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_right hu (norm_nonneg _)).trans
  simpa only [one_mul, zetaRightHalfRoughSquarefreeWindowFourierCarrier, zetaRightHalfRoughSquarefreeWindowCoefficient, p, a]
    using norm_zetaArithmeticFilter_sub_averaged_window_le a
    (norm_zetaRoughSquarefreeCoefficient_le _ _) p N rho.1.im hN

/-- The complete finite allowance vanishes, with both arithmetic sieves
and all physical and frequency errors present in the same expression. -/
theorem tendsto_zetaRightHalfRoughSquarefreeWindowTotalError (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (C₁ C₂ : ℝ) :
    Tendsto (fun N : ℕ ↦ C₁ * (1 + (N : ℝ) ^ 4) * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
      C₂ * (1 + (N : ℝ) ^ 4) * zetaRightHalfSquareSieveRate rho ^ N +
      zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im)
      atTop (𝓝 0) := by
  have hrate := tendsto_zetaRightHalfOnePrimeSquarefreeAllowance rho hrho C₂
  have h := ((tendsto_zetaRightHalfPrimePatternAllowance rho hrho C₁).add hrate).add
    (tendsto_zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) rho.1.im)
  simpa only [mul_zero, add_zero] using h

/-- The exact signed odd-reflection work of the actual surviving
coefficients, avoiding every selected prime, with every centered product and cyclic partner. -/
def zetaRightHalfRoughSquarefreeWindowReflectionWork (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℝ :=
  zetaArithmeticReflectionWork (zetaRightHalfRoughSquarefreeWindowCoefficient rho N)
    (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
    (zetaMoebiusResonantModes N (zetaAveragedResonanceThreshold N))

/-- Exact physical reflection cancellation commutes with the rough squarefree
restriction and smaller frequency region,
retaining every centering term. -/
theorem zetaRightHalfRoughSquarefreeWindowFourierCarrier_re_eq_reflection (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    (zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho N).re =
      -2 * zetaRightHalfRoughSquarefreeWindowReflectionWork rho hrho N :=
  zetaArithmeticCenteredPart_re_eq_reflection _
    (zetaLogWindowCoefficient_im _ (zetaRoughSquarefreeCoefficient_im _ _) N)
    _ _ _ _ (zetaMoebiusResonantModes_neg_closed N _)

/-- The signed surviving correlation still carries half the full
analytic multiplicity. Its independent strict upper bound remains open. -/
theorem tendsto_zetaRightHalfRoughSquarefreeWindowReflectionWork (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ (3 / 2 - rho.1.re : ℝ) ^ (N + 1) *
      zetaRightHalfRoughSquarefreeWindowReflectionWork rho hrho N)
      atTop (𝓝 ((analyticZetaZeroMultiplicity rho : ℝ) / 2)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho)
  simp only [Function.comp_def, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Complex.neg_re, Complex.natCast_re, zetaRightHalfRoughSquarefreeWindowFourierCarrier_re_eq_reflection] at h
  have ht := h.mul_const (-(1 / 2 : ℝ))
  convert ht using 1
  · funext N
    ring
  · congr 1
    ring

/-- The finite signed comparison with the original analytic source
retains the entire independently vanishing allowance, with the exact
reflection normalization. No surviving arithmetic term is discarded. -/
theorem exists_zetaRightHalfRoughSquarefreeWindowReflection_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ N : ℕ, 2 ≤ N →
      |-(3 / 2 - rho.1.re : ℝ) ^ (N + 1) *
          (zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N
            (3 / 2 + I * rho.1.im)).re / 2 -
        (3 / 2 - rho.1.re : ℝ) ^ (N + 1) * zetaRightHalfRoughSquarefreeWindowReflectionWork rho hrho N| ≤
        (C₁ * (1 + (N : ℝ) ^ 4) * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
          C₂ * (1 + (N : ℝ) ^ 4) * zetaRightHalfSquareSieveRate rho ^ N +
          zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im) / 2 := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hb⟩ := exists_zetaRightHalfRoughSquarefreeWindowFourier_error_bound rho hrho
  refine ⟨C₁, C₂, hC₁, hC₂, fun N hN ↦ ?_⟩
  let L := zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im)
  let u : ℝ := (3 / 2 - rho.1.re) ^ (N + 1)
  let z : ℂ := ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    (L - zetaRightHalfRoughSquarefreeWindowFourierCarrier rho hrho N)
  have hz : z.re = u * (L.re + 2 * zetaRightHalfRoughSquarefreeWindowReflectionWork rho hrho N) := by
    dsimp [z, u]
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.sub_re,
      zetaRightHalfRoughSquarefreeWindowFourierCarrier_re_eq_reflection]
    ring
  change |-u * L.re / 2 - u * zetaRightHalfRoughSquarefreeWindowReflectionWork rho hrho N| ≤ _
  have he : -u * L.re / 2 - u * zetaRightHalfRoughSquarefreeWindowReflectionWork rho hrho N = -z.re / 2 := by
    rw [hz]
    ring
  rw [he, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right ((Complex.abs_re_le_norm z).trans (hb N hN)) (by norm_num)

end
end RiemannGaussian
