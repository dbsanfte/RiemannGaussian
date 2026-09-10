/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusCubicSieve

/-!
# The full signed window source after the larger sieve

The cubic overlap budget is used on the original arithmetic coefficients,
then combined with the proved physical and Fourier localizations. Both
outer shells, all sieve overlaps, and the complementary Fourier interaction
have independent vanishing errors. The remaining signed reflection work
still carries half the analytic multiplicity and requires an independent
strict upper bound.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The actual coefficients after the larger sieve and exact window
restriction, retaining the unchanged divisor cutoff. -/
def zetaRightHalfCubicWindowCoefficient (rho : NontrivialZetaZero) (N : ℕ) : ℕ → ℂ :=
  zetaLogWindowCoefficient
    (zetaMoebiusSievedPrimeCoefficient
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfCubicSieve rho N)) N

/-- Every nonzero retained coefficient lies beyond the cutoff square
and has distinct prime divisors. Every distinct prime pair exceeds the
larger threshold, including its exact integer rounding. -/
theorem zetaRightHalfCubicWindowCoefficient_support (rho : NontrivialZetaZero)
    {N n : ℕ} (hN : 1 ≤ N) (hn : zetaRightHalfCubicWindowCoefficient rho N n ≠ 0) :
    n ∈ zetaLogWindow N ∧
      zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N ^ 2 < n ∧
      (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ n ∧ q ∣ n) ∧
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → p ∣ n → q ∣ n →
        Nat.log 2 (zetaMoebiusGeometricCutoff
          (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N ^ 3) ≤ p * q := by
  have hw : n ∈ zetaLogWindow N := by
    by_contra h
    simp [zetaRightHalfCubicWindowCoefficient, zetaLogWindowCoefficient, h] at hn
  have ha : zetaMoebiusSievedPrimeCoefficient
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfCubicSieve rho N) n ≠ 0 := by
    simpa only [zetaRightHalfCubicWindowCoefficient, zetaLogWindowCoefficient, if_pos hw] using hn
  have hs := zetaMoebiusSievedPrimeCoefficient_support _ _ n ha
  exact ⟨hw, zetaLogWindow_gt_moebiusCutoff_sq rho hN hw, hs.2⟩

/-- The larger sieve and smaller physical window retain every original
centered Fourier product in the proved frequency region. -/
def zetaRightHalfCubicWindowFourierCarrier (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  zetaArithmeticCenteredPart (zetaRightHalfCubicWindowCoefficient rho N)
    (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
    (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N))

/-- The actual complete source survives the larger sieve and both
localizations together, with its original analytic multiplicity. -/
theorem tendsto_zetaRightHalfCubicWindowFourierCarrier (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaRightHalfCubicWindowFourierCarrier rho hrho N)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : ‖((3 / 2 - rho.1.re : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [NontrivialZetaZero.re_lt_one rho])]
    linarith
  have hp := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hu).comp (tendsto_add_atTop_nat 1)
  have he := tendsto_zetaArithmeticFilter_sub_window_fourier
    (fun N ↦ zetaMoebiusSievedPrimeCoefficient
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfCubicSieve rho N))
    (fun N ↦ norm_zetaMoebiusSievedPrimeCoefficient_le _ _)
    (zetaRightHalfPoleJetFilter rho hrho) rho.1.im
  have h := (tendsto_zetaRightHalfCubicSievedPrimeTail rho hrho).sub (hp.mul he)
  simp only [mul_zero, sub_zero] at h
  convert h using 1
  funext N
  dsimp [zetaRightHalfCubicWindowFourierCarrier, zetaRightHalfCubicWindowCoefficient,
    zetaMoebiusSievedPrimeFilter, zetaArithmeticFilter, Function.comp_def]
  ring

/-- The complete pole-jet response differs from the new arithmetic
carrier by the independently controlled head/prime-power and sieve errors. -/
theorem exists_zetaRightHalfCubicSievedPrimeTail_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ N : ℕ,
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        (zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) -
          zetaMoebiusSievedPrimeFilter (zetaRightHalfPoleJetFilter rho hrho)
            (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
            (zetaRightHalfCubicSieve rho N) N (3 / 2 + I * rho.1.im))‖ ≤
        C₁ * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
          C₂ * zetaMoebiusCubicRate (3 / 2 - rho.1.re) ^ N := by
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_zetaRightHalfDistinctPrimeTail_error_bound rho hrho
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_zetaRightHalfMoebiusSieve_cubic_bound rho hrho
  refine ⟨C₁, C₂, hC₁, hC₂, fun N ↦ ?_⟩
  obtain ⟨hS, hcost⟩ := zetaRightHalfCubicSieve_budget rho hrho N
  have h := hb₂ N (zetaRightHalfCubicSieve rho N) hS hcost
  have halg (a b c : ℂ) : a - (b - c) = a - b + c := by ring
  rw [zetaMoebiusSievedPrimeFilter,
    (hasSum_zetaMoebiusSievedPrimeFilter _ _ N (zetaRightHalfPoleJetCutoff_pos rho hrho N) _ hS
      (by norm_num)).tsum_eq, halg, mul_add]
  exact (norm_add_le _ _).trans (add_le_add (hb₁ N) h)

/-- The finite comparison with the original analytic response pays for
every discarded arithmetic and Fourier contribution at once. -/
theorem exists_zetaRightHalfCubicWindowFourier_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ N : ℕ, 2 ≤ N →
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        (zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) -
          zetaRightHalfCubicWindowFourierCarrier rho hrho N)‖ ≤
        C₁ * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
          C₂ * zetaMoebiusCubicRate (3 / 2 - rho.1.re) ^ N +
          zetaLogWindowFourierError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hb⟩ := exists_zetaRightHalfCubicSievedPrimeTail_error_bound rho hrho
  refine ⟨C₁, C₂, hC₁, hC₂, fun N hN ↦ ?_⟩
  let p := zetaRightHalfPoleJetFilter rho hrho
  let a := zetaMoebiusSievedPrimeCoefficient
    (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
    (zetaRightHalfCubicSieve rho N)
  let u : ℂ := ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1)
  have hu : ‖u‖ ≤ 1 := by
    have hu0 : 0 ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
    dsimp [u]
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
    exact pow_le_one₀ hu0 (by linarith)
  have he : u * (zetaPrimeLogFilter p N (3 / 2 + I * rho.1.im) -
      zetaRightHalfCubicWindowFourierCarrier rho hrho N) =
      u * (zetaPrimeLogFilter p N (3 / 2 + I * rho.1.im) -
        zetaArithmeticFilter a p N (3 / 2 + I * rho.1.im)) +
      u * (zetaArithmeticFilter a p N (3 / 2 + I * rho.1.im) -
        zetaRightHalfCubicWindowFourierCarrier rho hrho N) := by ring
  change ‖u * (zetaPrimeLogFilter p N (3 / 2 + I * rho.1.im) -
    zetaRightHalfCubicWindowFourierCarrier rho hrho N)‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add (hb N)
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_right hu (norm_nonneg _)).trans
  simpa only [one_mul, zetaRightHalfCubicWindowFourierCarrier, zetaRightHalfCubicWindowCoefficient, p, a]
    using norm_zetaArithmeticFilter_sub_window_fourier_le a
    (norm_zetaMoebiusSievedPrimeCoefficient_le _ _) p N rho.1.im hN

/-- The entire error allowance tends to zero, including the larger
sieve's slower rate and both existing physical and Fourier errors. -/
theorem tendsto_zetaRightHalfCubicWindowTotalError (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (C₁ C₂ : ℝ) :
    Tendsto (fun N ↦ C₁ * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
      C₂ * zetaMoebiusCubicRate (3 / 2 - rho.1.re) ^ N +
      zetaLogWindowFourierError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im)
      atTop (𝓝 0) := by
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (zetaMoebiusCubicRate_pos (u := 3 / 2 - rho.1.re)
      (by linarith [NontrivialZetaZero.re_lt_one rho])).le
    (zetaMoebiusCubicRate_lt_one (by linarith))).const_mul C₂
  have h := (tendsto_zetaRightHalfWindowTotalError rho hrho C₁).add hp
  simp only [mul_zero, add_zero] at h
  convert h using 1
  funext N
  ring

/-- The surviving signed odd-reflection correlation, keeping the
larger arithmetic sieve and all cyclic partners of the original profile. -/
def zetaRightHalfCubicWindowReflectionWork (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℝ :=
  zetaArithmeticReflectionWork (zetaRightHalfCubicWindowCoefficient rho N)
    (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
    (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N))

/-- The exact signed reflection identity survives the larger sieve;
the imaginary physical channel and even real profile cancel as before. -/
theorem zetaRightHalfCubicWindowFourierCarrier_re_eq_reflection (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    (zetaRightHalfCubicWindowFourierCarrier rho hrho N).re =
      -2 * zetaRightHalfCubicWindowReflectionWork rho hrho N :=
  zetaArithmeticCenteredPart_re_eq_reflection _
    (zetaLogWindowCoefficient_im _ (zetaMoebiusSievedPrimeCoefficient_im _ _) N)
    _ _ _ _ (zetaMoebiusResonantModes_neg_closed N _)

/-- The exact surviving real correlation still carries half the full
analytic multiplicity. Its independent strict upper bound remains open. -/
theorem tendsto_zetaRightHalfCubicWindowReflectionWork (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ (3 / 2 - rho.1.re : ℝ) ^ (N + 1) *
      zetaRightHalfCubicWindowReflectionWork rho hrho N)
      atTop (𝓝 ((analyticZetaZeroMultiplicity rho : ℝ) / 2)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_zetaRightHalfCubicWindowFourierCarrier rho hrho)
  simp only [Function.comp_def, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Complex.neg_re, Complex.natCast_re, zetaRightHalfCubicWindowFourierCarrier_re_eq_reflection] at h
  have ht := h.mul_const (-(1 / 2 : ℝ))
  convert ht using 1
  · funext N
    ring
  · congr 1
    ring

/-- The surviving signed work has one finite comparison with the
original pole-jet response, retaining both independent arithmetic rates
and the full physical-window and complementary-frequency allowance. -/
theorem exists_zetaRightHalfCubicWindowReflection_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ N : ℕ, 2 ≤ N →
      |-(3 / 2 - rho.1.re : ℝ) ^ (N + 1) *
          (zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N
            (3 / 2 + I * rho.1.im)).re / 2 -
        (3 / 2 - rho.1.re : ℝ) ^ (N + 1) * zetaRightHalfCubicWindowReflectionWork rho hrho N| ≤
        (C₁ * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
          C₂ * zetaMoebiusCubicRate (3 / 2 - rho.1.re) ^ N +
          zetaLogWindowFourierError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im) / 2 := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hb⟩ := exists_zetaRightHalfCubicWindowFourier_error_bound rho hrho
  refine ⟨C₁, C₂, hC₁, hC₂, fun N hN ↦ ?_⟩
  let L := zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im)
  let u : ℝ := (3 / 2 - rho.1.re) ^ (N + 1)
  let z : ℂ := ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    (L - zetaRightHalfCubicWindowFourierCarrier rho hrho N)
  have hz : z.re = u * (L.re + 2 * zetaRightHalfCubicWindowReflectionWork rho hrho N) := by
    dsimp [z, u]
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.sub_re,
      zetaRightHalfCubicWindowFourierCarrier_re_eq_reflection]
    ring
  change |-u * L.re / 2 - u * zetaRightHalfCubicWindowReflectionWork rho hrho N| ≤ _
  have he : -u * L.re / 2 - u * zetaRightHalfCubicWindowReflectionWork rho hrho N = -z.re / 2 := by
    rw [hz]
    ring
  rw [he, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right ((Complex.abs_re_le_norm z).trans (hb N hN)) (by norm_num)

end
end RiemannGaussian
