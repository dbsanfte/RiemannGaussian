/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaQuadraticPrimeSieve
import RiemannGaussian.ZetaAveragedWindowSource

/-!
# The complete signed source after the quadratic prime sieve

Every surviving physical integer has at most one prime divisor below the
explicit quadratic cutoff. The complete original source is transported
through this actual sieve, the physical logarithmic window, and the
averaged-symbol frequency region. All arithmetic and localization errors
are included in one finite comparison whose allowance tends to zero.
The remaining signed reflection work still needs an independent bound.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The original coefficients restricted by the simultaneous quadratic
prime sieve and the existing physical logarithmic window. -/
def zetaRightHalfQuadraticWindowCoefficient (rho : NontrivialZetaZero) (N : ℕ) : ℕ → ℂ :=
  zetaLogWindowCoefficient
    (zetaMoebiusSievedPrimeCoefficient
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfQuadraticPrimeSieve rho N)) N

/-- Every surviving coefficient lies beyond the divisor-cutoff square,
has at least two distinct prime divisors overall, and at most one prime
divisor among all primes through the explicit quadratic cutoff. -/
theorem zetaRightHalfQuadraticWindowCoefficient_support (rho : NontrivialZetaZero)
    {N n : ℕ} (hN : 1 ≤ N) (hn : zetaRightHalfQuadraticWindowCoefficient rho N n ≠ 0) :
    n ∈ zetaLogWindow N ∧
      zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N ^ 2 < n ∧
      (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ n ∧ q ∣ n) ∧
      ((zetaRightHalfPrimePatternPrimes rho N).filter (fun p ↦ p ∣ n)).card ≤ 1 := by
  have hw : n ∈ zetaLogWindow N := by
    by_contra h
    simp [zetaRightHalfQuadraticWindowCoefficient, zetaLogWindowCoefficient, h] at hn
  have ha : zetaMoebiusSievedPrimeCoefficient
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfQuadraticPrimeSieve rho N) n ≠ 0 := by
    simpa only [zetaRightHalfQuadraticWindowCoefficient, zetaLogWindowCoefficient, if_pos hw] using hn
  have hS : ¬∃ P ∈ zetaRightHalfQuadraticPrimeSieve rho N, P ∣ n := by
    by_contra h
    simp [zetaMoebiusSievedPrimeCoefficient, h] at ha
  have hd : zetaMoebiusDistinctPrimeCoefficient
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) n ≠ 0 := by
    simpa only [zetaMoebiusSievedPrimeCoefficient, if_pos hS] using ha
  refine ⟨hw, zetaLogWindow_gt_moebiusCutoff_sq rho hN hw,
    (zetaMoebiusDistinctPrimeCoefficient_support _ n hd).2, ?_⟩
  have hc : ¬2 ≤ ((zetaRightHalfPrimePatternPrimes rho N).filter (fun p ↦ p ∣ n)).card := by
    intro h
    exact hS ((primePairSieve_card_iff _
      (fun p hp ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N p hp).1) n).mp h)
  omega

/-- Every centered complex Fourier product is retained on the actual
quadratic-sieved coefficients in the proved smaller frequency region. -/
def zetaRightHalfQuadraticWindowFourierCarrier (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  zetaArithmeticCenteredPart (zetaRightHalfQuadraticWindowCoefficient rho N)
    (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
    (zetaMoebiusResonantModes N (zetaAveragedResonanceThreshold N))

/-- The whole negative analytic multiplicity survives the actual
quadratic prime sieve and both localizations, with every premise discharged. -/
theorem tendsto_zetaRightHalfQuadraticWindowFourierCarrier (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaRightHalfQuadraticWindowFourierCarrier rho hrho N)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : ‖((3 / 2 - rho.1.re : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [NontrivialZetaZero.re_lt_one rho])]
    linarith
  have hp := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hu).comp (tendsto_add_atTop_nat 1)
  have he := tendsto_zetaArithmeticFilter_sub_averaged_window
    (fun N ↦ zetaMoebiusSievedPrimeCoefficient
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfQuadraticPrimeSieve rho N))
    (fun N ↦ norm_zetaMoebiusSievedPrimeCoefficient_le _ _)
    (zetaRightHalfPoleJetFilter rho hrho) rho.1.im
  have h := (tendsto_zetaRightHalfQuadraticSievedPrimeTail rho hrho).sub (hp.mul he)
  simp only [mul_zero, sub_zero] at h
  convert h using 1
  funext N
  dsimp [zetaRightHalfQuadraticWindowFourierCarrier, zetaRightHalfQuadraticWindowCoefficient,
    zetaMoebiusSievedPrimeFilter, zetaArithmeticFilter, Function.comp_def]
  ring

/-- One finite comparison pays for the original head and prime powers,
the complete quadratic prime-pattern union, both physical outer shells,
and every complementary Fourier interaction. -/
theorem exists_zetaRightHalfQuadraticWindowFourier_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        (zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) -
          zetaRightHalfQuadraticWindowFourierCarrier rho hrho N)‖ ≤
        C * (1 + (N : ℝ) ^ 4) * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
          zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im := by
  obtain ⟨C, hC, hb⟩ := exists_zetaRightHalfQuadraticSievedPrimeTail_error_bound rho hrho
  refine ⟨C, hC, fun N hN ↦ ?_⟩
  let p := zetaRightHalfPoleJetFilter rho hrho
  let a := zetaMoebiusSievedPrimeCoefficient
    (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
    (zetaRightHalfQuadraticPrimeSieve rho N)
  let u : ℂ := ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1)
  have hu : ‖u‖ ≤ 1 := by
    have hu0 : 0 ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
    dsimp [u]
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
    exact pow_le_one₀ hu0 (by linarith)
  have he : u * (zetaPrimeLogFilter p N (3 / 2 + I * rho.1.im) -
      zetaRightHalfQuadraticWindowFourierCarrier rho hrho N) =
      u * (zetaPrimeLogFilter p N (3 / 2 + I * rho.1.im) -
        zetaArithmeticFilter a p N (3 / 2 + I * rho.1.im)) +
      u * (zetaArithmeticFilter a p N (3 / 2 + I * rho.1.im) -
        zetaRightHalfQuadraticWindowFourierCarrier rho hrho N) := by ring
  change ‖u * (zetaPrimeLogFilter p N (3 / 2 + I * rho.1.im) -
    zetaRightHalfQuadraticWindowFourierCarrier rho hrho N)‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add (hb N)
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_right hu (norm_nonneg _)).trans
  simpa only [one_mul, zetaRightHalfQuadraticWindowFourierCarrier, zetaRightHalfQuadraticWindowCoefficient, p, a]
    using norm_zetaArithmeticFilter_sub_averaged_window_le a
    (norm_zetaMoebiusSievedPrimeCoefficient_le _ _) p N rho.1.im hN

/-- The complete finite allowance vanishes, with the quadratic sieve
and all physical and frequency errors present in the same expression. -/
theorem tendsto_zetaRightHalfQuadraticWindowTotalError (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (C : ℝ) :
    Tendsto (fun N : ℕ ↦ C * (1 + (N : ℝ) ^ 4) * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
      zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im)
      atTop (𝓝 0) := by
  have h := (tendsto_zetaRightHalfPrimePatternAllowance rho hrho C).add
    (tendsto_zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) rho.1.im)
  simpa only [add_zero] using h

/-- The exact signed odd-reflection work of the actual surviving
coefficients, including every centered Fourier product and cyclic partner. -/
def zetaRightHalfQuadraticWindowReflectionWork (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℝ :=
  zetaArithmeticReflectionWork (zetaRightHalfQuadraticWindowCoefficient rho N)
    (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
    (zetaMoebiusResonantModes N (zetaAveragedResonanceThreshold N))

/-- Exact physical reflection cancellation commutes with the quadratic
prime sieve and smaller frequency region, retaining every centering term. -/
theorem zetaRightHalfQuadraticWindowFourierCarrier_re_eq_reflection (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    (zetaRightHalfQuadraticWindowFourierCarrier rho hrho N).re =
      -2 * zetaRightHalfQuadraticWindowReflectionWork rho hrho N :=
  zetaArithmeticCenteredPart_re_eq_reflection _
    (zetaLogWindowCoefficient_im _ (zetaMoebiusSievedPrimeCoefficient_im _ _) N)
    _ _ _ _ (zetaMoebiusResonantModes_neg_closed N _)

/-- The signed surviving correlation still carries half the full
analytic multiplicity. Its independent strict upper bound remains open. -/
theorem tendsto_zetaRightHalfQuadraticWindowReflectionWork (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ (3 / 2 - rho.1.re : ℝ) ^ (N + 1) *
      zetaRightHalfQuadraticWindowReflectionWork rho hrho N)
      atTop (𝓝 ((analyticZetaZeroMultiplicity rho : ℝ) / 2)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_zetaRightHalfQuadraticWindowFourierCarrier rho hrho)
  simp only [Function.comp_def, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Complex.neg_re, Complex.natCast_re, zetaRightHalfQuadraticWindowFourierCarrier_re_eq_reflection] at h
  have ht := h.mul_const (-(1 / 2 : ℝ))
  convert ht using 1
  · funext N
    ring
  · congr 1
    ring

/-- The finite signed comparison with the original analytic source
retains the entire independently vanishing allowance, with the exact
reflection normalization. No surviving arithmetic term is discarded. -/
theorem exists_zetaRightHalfQuadraticWindowReflection_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      |-(3 / 2 - rho.1.re : ℝ) ^ (N + 1) *
          (zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N
            (3 / 2 + I * rho.1.im)).re / 2 -
        (3 / 2 - rho.1.re : ℝ) ^ (N + 1) * zetaRightHalfQuadraticWindowReflectionWork rho hrho N| ≤
        (C * (1 + (N : ℝ) ^ 4) * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
          zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im) / 2 := by
  obtain ⟨C, hC, hb⟩ := exists_zetaRightHalfQuadraticWindowFourier_error_bound rho hrho
  refine ⟨C, hC, fun N hN ↦ ?_⟩
  let L := zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im)
  let u : ℝ := (3 / 2 - rho.1.re) ^ (N + 1)
  let z : ℂ := ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    (L - zetaRightHalfQuadraticWindowFourierCarrier rho hrho N)
  have hz : z.re = u * (L.re + 2 * zetaRightHalfQuadraticWindowReflectionWork rho hrho N) := by
    dsimp [z, u]
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.sub_re,
      zetaRightHalfQuadraticWindowFourierCarrier_re_eq_reflection]
    ring
  change |-u * L.re / 2 - u * zetaRightHalfQuadraticWindowReflectionWork rho hrho N| ≤ _
  have he : -u * L.re / 2 - u * zetaRightHalfQuadraticWindowReflectionWork rho hrho N = -z.re / 2 := by
    rw [hz]
    ring
  rw [he, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right ((Complex.abs_re_le_norm z).trans (hb N hN)) (by norm_num)

end
end RiemannGaussian
