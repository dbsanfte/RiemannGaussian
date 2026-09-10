/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaAveragedResonance
import RiemannGaussian.ZetaCubicWindowSource

/-!
# The complete signed source in the averaged-symbol frequency region

The actual cubic sieve and physical window are unchanged. Averaging the
inverse difference symbol justifies a smaller frequency region, preserving
the full source and every centered Fourier product inside it. The original
pole-jet comparison retains all arithmetic, physical, and frequency errors,
and its entire allowance tends to zero.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The unchanged actual cubic-sieved window coefficients in the
smaller frequency region. All complex products remain centered as before. -/
def zetaRightHalfAveragedWindowFourierCarrier (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  zetaArithmeticCenteredPart (zetaRightHalfCubicWindowCoefficient rho N)
    (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
    (zetaMoebiusResonantModes N (zetaAveragedResonanceThreshold N))

/-- The smaller actual frequency region still retains the whole
negative analytic multiplicity source, with every other hypothesis discharged. -/
theorem tendsto_zetaRightHalfAveragedWindowFourierCarrier (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaRightHalfAveragedWindowFourierCarrier rho hrho N)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : ‖((3 / 2 - rho.1.re : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [NontrivialZetaZero.re_lt_one rho])]
    linarith
  have hp := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hu).comp (tendsto_add_atTop_nat 1)
  have he := tendsto_zetaArithmeticFilter_sub_averaged_window
    (fun N ↦ zetaMoebiusSievedPrimeCoefficient
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfCubicSieve rho N))
    (fun N ↦ norm_zetaMoebiusSievedPrimeCoefficient_le _ _)
    (zetaRightHalfPoleJetFilter rho hrho) rho.1.im
  have h := (tendsto_zetaRightHalfCubicSievedPrimeTail rho hrho).sub (hp.mul he)
  simp only [mul_zero, sub_zero] at h
  convert h using 1
  funext N
  dsimp [zetaRightHalfAveragedWindowFourierCarrier, zetaRightHalfCubicWindowCoefficient,
    zetaMoebiusSievedPrimeFilter, zetaArithmeticFilter, Function.comp_def]
  ring

/-- Every original arithmetic error and the complete improved
localization allowance enter one finite bound for the actual carrier. -/
theorem exists_zetaRightHalfAveragedWindowFourier_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ N : ℕ, 2 ≤ N →
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        (zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) -
          zetaRightHalfAveragedWindowFourierCarrier rho hrho N)‖ ≤
        C₁ * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
          C₂ * zetaMoebiusCubicRate (3 / 2 - rho.1.re) ^ N +
          zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im := by
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
      zetaRightHalfAveragedWindowFourierCarrier rho hrho N) =
      u * (zetaPrimeLogFilter p N (3 / 2 + I * rho.1.im) -
        zetaArithmeticFilter a p N (3 / 2 + I * rho.1.im)) +
      u * (zetaArithmeticFilter a p N (3 / 2 + I * rho.1.im) -
        zetaRightHalfAveragedWindowFourierCarrier rho hrho N) := by ring
  change ‖u * (zetaPrimeLogFilter p N (3 / 2 + I * rho.1.im) -
    zetaRightHalfAveragedWindowFourierCarrier rho hrho N)‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add (hb N)
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_right hu (norm_nonneg _)).trans
  simpa only [one_mul, zetaRightHalfAveragedWindowFourierCarrier, zetaRightHalfCubicWindowCoefficient, p, a]
    using norm_zetaArithmeticFilter_sub_averaged_window_le a
    (norm_zetaMoebiusSievedPrimeCoefficient_le _ _) p N rho.1.im hN

/-- The entire new allowance vanishes, with every old arithmetic
error and the improved frequency bound present in the same expression. -/
theorem tendsto_zetaRightHalfAveragedWindowTotalError (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (C₁ C₂ : ℝ) :
    Tendsto (fun N ↦ C₁ * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
      C₂ * zetaMoebiusCubicRate (3 / 2 - rho.1.re) ^ N +
      zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im)
      atTop (𝓝 0) := by
  have hu0 : 0 ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hs : Real.sqrt (3 / 2 - rho.1.re) < 1 := by
    nlinarith [Real.sq_sqrt hu0, Real.sqrt_nonneg (3 / 2 - rho.1.re)]
  have h₁ := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.sqrt_nonneg _) hs).const_mul C₁
  have h₂ := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (zetaMoebiusCubicRate_pos (u := 3 / 2 - rho.1.re)
      (by linarith [NontrivialZetaZero.re_lt_one rho])).le
    (zetaMoebiusCubicRate_lt_one (by linarith))).const_mul C₂
  have h := (h₁.add h₂).add
    (tendsto_zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) rho.1.im)
  simpa only [mul_zero, add_zero] using h

/-- The exact signed odd-reflection work on the smaller frequency
region, with the unchanged cubic-sieved physical coefficients. -/
def zetaRightHalfAveragedWindowReflectionWork (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℝ :=
  zetaArithmeticReflectionWork (zetaRightHalfCubicWindowCoefficient rho N)
    (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
    (zetaMoebiusResonantModes N (zetaAveragedResonanceThreshold N))

/-- Physical reflection cancellation commutes with the smaller
frequency selection, including every centering correction. -/
theorem zetaRightHalfAveragedWindowFourierCarrier_re_eq_reflection (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    (zetaRightHalfAveragedWindowFourierCarrier rho hrho N).re =
      -2 * zetaRightHalfAveragedWindowReflectionWork rho hrho N :=
  zetaArithmeticCenteredPart_re_eq_reflection _
    (zetaLogWindowCoefficient_im _ (zetaMoebiusSievedPrimeCoefficient_im _ _) N)
    _ _ _ _ (zetaMoebiusResonantModes_neg_closed N _)

/-- The signed correlation in the smaller region still carries half
the full analytic multiplicity. Its independent strict upper bound is open. -/
theorem tendsto_zetaRightHalfAveragedWindowReflectionWork (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ (3 / 2 - rho.1.re : ℝ) ^ (N + 1) *
      zetaRightHalfAveragedWindowReflectionWork rho hrho N)
      atTop (𝓝 ((analyticZetaZeroMultiplicity rho : ℝ) / 2)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_zetaRightHalfAveragedWindowFourierCarrier rho hrho)
  simp only [Function.comp_def, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Complex.neg_re, Complex.natCast_re, zetaRightHalfAveragedWindowFourierCarrier_re_eq_reflection] at h
  have ht := h.mul_const (-(1 / 2 : ℝ))
  convert ht using 1
  · funext N
    ring
  · congr 1
    ring

/-- The exact signed comparison has the same complete vanishing
allowance as the complex carrier, divided by its reflection normalization. -/
theorem exists_zetaRightHalfAveragedWindowReflection_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ N : ℕ, 2 ≤ N →
      |-(3 / 2 - rho.1.re : ℝ) ^ (N + 1) *
          (zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N
            (3 / 2 + I * rho.1.im)).re / 2 -
        (3 / 2 - rho.1.re : ℝ) ^ (N + 1) * zetaRightHalfAveragedWindowReflectionWork rho hrho N| ≤
        (C₁ * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
          C₂ * zetaMoebiusCubicRate (3 / 2 - rho.1.re) ^ N +
          zetaAveragedWindowError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im) / 2 := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hb⟩ := exists_zetaRightHalfAveragedWindowFourier_error_bound rho hrho
  refine ⟨C₁, C₂, hC₁, hC₂, fun N hN ↦ ?_⟩
  let L := zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im)
  let u : ℝ := (3 / 2 - rho.1.re) ^ (N + 1)
  let z : ℂ := ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    (L - zetaRightHalfAveragedWindowFourierCarrier rho hrho N)
  have hz : z.re = u * (L.re + 2 * zetaRightHalfAveragedWindowReflectionWork rho hrho N) := by
    dsimp [z, u]
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.sub_re,
      zetaRightHalfAveragedWindowFourierCarrier_re_eq_reflection]
    ring
  change |-u * L.re / 2 - u * zetaRightHalfAveragedWindowReflectionWork rho hrho N| ≤ _
  have he : -u * L.re / 2 - u * zetaRightHalfAveragedWindowReflectionWork rho hrho N = -z.re / 2 := by
    rw [hz]
    ring
  rw [he, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right ((Complex.abs_re_le_norm z).trans (hb N hN)) (by norm_num)

end
end RiemannGaussian
