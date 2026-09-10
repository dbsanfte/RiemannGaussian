/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusResonanceDecay
import RiemannGaussian.FiniteFourierCentering

/-!
# The selected-zero source in centered arithmetic Fourier increments

The constant arithmetic Fourier component is independently negligible
on the shrinking resonant region. The complete source therefore survives
after its exact subtraction. Every fractional exponent below one quarter
gives a uniform modulus for the remaining actual Möbius Fourier increment;
the signed interaction of that increment with the kernel remains explicit.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- Every fractional arithmetic moment below one quarter is bounded by
a genuinely convergent divisor majorant, uniformly in both cutoffs. -/
theorem sum_norm_zetaMoebiusWeightedBandSamples_mul_rpow_le (D N : ℕ)
    {τ : ℝ} (hτ : τ < 1 / 4) :
    (∑ j, ‖zetaMoebiusWeightedBandSamples D N j‖ * (j.val : ℝ) ^ τ) ≤
      zetaMoebiusLogMajorantMass (5 / 4 - τ) := by
  have he (j : ZMod (2 ^ (32 * N) + 1)) :
      ‖zetaMoebiusWeightedBandSamples D N j‖ * (j.val : ℝ) ^ τ =
        zetaLogBandSamples N (fun n ↦ ‖zetaMoebiusLogTailCoefficient D n‖ *
          zetaPrimeExpWeight (5 / 4 - τ) n) j := by
    by_cases hj : j.val ∈ zetaPrimeLogBand N
    · have hj1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1
      have hj0 : (0 : ℝ) < j.val := by exact_mod_cast (show 0 < j.val by omega)
      simp only [zetaMoebiusWeightedBandSamples, zetaLogBandSamples, if_pos hj,
        norm_mul, norm_zetaPrimeFeature, zetaPrimeExpWeight, Real.rpow_def_of_pos hj0,
        mul_assoc, ← Real.exp_add, show (5 / 4 : ℂ).re = (5 / 4 : ℝ) by norm_num]
      congr 2
      ring
    · simp [zetaMoebiusWeightedBandSamples, zetaLogBandSamples, hj]
  simp_rw [he]
  rw [sum_zetaLogBandSamples]
  calc
    _ ≤ ∑ n ∈ zetaPrimeLogBand N,
        zetaMoebiusLogMajorant n * zetaPrimeExpWeight (5 / 4 - τ) n := by
      apply Finset.sum_le_sum
      intro n _
      exact mul_le_mul_of_nonneg_right (norm_zetaMoebiusLogTailCoefficient_le D n)
        (Real.exp_pos _).le
    _ ≤ _ := Summable.sum_le_tsum (zetaPrimeLogBand N)
      (fun n _ ↦ mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le)
      (summable_zetaMoebiusLogMajorant (by linarith))

/-- The actual arithmetic Fourier transform has a uniform fractional
modulus at zero for every exponent below one quarter. No cancellation
hypothesis, zero selection, or numerical coefficient family is used. -/
theorem norm_zetaMoebiusWeightedDFT_sub_zero_le (D N : ℕ)
    (k : ZMod (2 ^ (32 * N) + 1)) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1 / 4) :
    ‖ZMod.dft (zetaMoebiusWeightedBandSamples D N) (-k) -
      ZMod.dft (zetaMoebiusWeightedBandSamples D N) 0‖ ≤
      2 * ‖cyclicDifferenceSymbol k‖ ^ τ * zetaMoebiusLogMajorantMass (5 / 4 - τ) := by
  apply (norm_dft_sub_zero_le_fractional_moment
    (zetaMoebiusWeightedBandSamples D N) k hτ0 (by linarith)).trans
  exact mul_le_mul_of_nonneg_left (sum_norm_zetaMoebiusWeightedBandSamples_mul_rpow_le D N hτ1)
    (by positivity)

/-- All resonant Fourier increments obey the same bound, independent of
the divisor cutoff and of which frequency in the shrinking region is chosen. -/
theorem norm_zetaMoebiusWeightedDFT_sub_zero_resonant_le (D N : ℕ)
    (k : ZMod (2 ^ (32 * N) + 1))
    (hk : k ∈ zetaMoebiusResonantModes N (zetaMoebiusResonanceThreshold N))
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1 / 4) :
    ‖ZMod.dft (zetaMoebiusWeightedBandSamples D N) (-k) -
      ZMod.dft (zetaMoebiusWeightedBandSamples D N) 0‖ ≤
      2 * zetaMoebiusResonanceThreshold N ^ τ * zetaMoebiusLogMajorantMass (5 / 4 - τ) := by
  apply (norm_zetaMoebiusWeightedDFT_sub_zero_le D N k hτ0 hτ1).trans
  have hg : ‖cyclicDifferenceSymbol k‖ < zetaMoebiusResonanceThreshold N := by
    simpa [zetaMoebiusResonantModes] using hk
  gcongr
  exact zetaMoebiusLogMajorantMass_nonneg _

/-- The Fourier increments tend to zero uniformly over all moving
cutoffs and all frequencies in the shrinking region. This is a bound on
the arithmetic factor, not on the sum of its products with kernel modes. -/
theorem zetaMoebiusWeightedDFT_sub_zero_uniformly_small {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1 / 4) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ D : ℕ, ∀ k : ZMod (2 ^ (32 * N) + 1),
      k ∈ zetaMoebiusResonantModes N (zetaMoebiusResonanceThreshold N) →
      ‖ZMod.dft (zetaMoebiusWeightedBandSamples D N) (-k) -
        ZMod.dft (zetaMoebiusWeightedBandSamples D N) 0‖ < ε := by
  have ht := (Real.continuousAt_rpow_const 0 τ (Or.inr hτ0.le)).tendsto.comp
    tendsto_zetaMoebiusResonanceThreshold
  simp only [Function.comp_def, Real.zero_rpow hτ0.ne'] at ht
  have hb := (ht.const_mul 2).mul_const (zetaMoebiusLogMajorantMass (5 / 4 - τ))
  simp only [mul_zero, zero_mul] at hb
  filter_upwards [hb.eventually_lt_const hε] with N hN D k hk
  exact (norm_zetaMoebiusWeightedDFT_sub_zero_resonant_le D N k hk hτ0.le hτ1).trans_lt hN

/-- The true Möbius Fourier increment retains every divisor sign and
each cyclic phase difference before applying its modulus estimate. -/
theorem zetaMoebiusWeightedDFT_sub_zero_eq (D N : ℕ)
    (k : ZMod (2 ^ (32 * N) + 1)) :
    ZMod.dft (zetaMoebiusWeightedBandSamples D N) (-k) -
      ZMod.dft (zetaMoebiusWeightedBandSamples D N) 0 =
        ∑ n ∈ zetaPrimeLogBand N,
          (zetaMoebiusLogTailCoefficient D n * zetaPrimeFeature (5 / 4) n) *
            (ZMod.stdAddChar k ^ n - 1) := by
  rw [dft_sub_zero_eq]
  have he (j : ZMod (2 ^ (32 * N) + 1)) :
      zetaMoebiusWeightedBandSamples D N j * (ZMod.stdAddChar k ^ j.val - 1) =
        zetaLogBandSamples N (fun n ↦
          (zetaMoebiusLogTailCoefficient D n * zetaPrimeFeature (5 / 4) n) *
            (ZMod.stdAddChar k ^ n - 1)) j := by
    by_cases hj : j.val ∈ zetaPrimeLogBand N <;>
      simp [zetaMoebiusWeightedBandSamples, zetaLogBandSamples, hj]
  simp_rw [he]
  exact sum_zetaLogBandSamples _ _

/-- The resonant carrier with its constant arithmetic Fourier component
subtracted inside each full complex product. -/
def zetaMoebiusCenteredFourierPart (p : Polynomial ℂ) (D N : ℕ) (y : ℝ)
    (S : Finset (ZMod (2 ^ (32 * N) + 1))) : ℂ :=
  centeredFourierPart (zetaMoebiusWeightedBandSamples D N) (zetaQuarterKernelSamples p N y) S

/-- Centering preserves the literal arithmetic band exactly across every
frequency partition; no constant-component correction is discarded. -/
theorem zetaMoebiusBandFilter_eq_centered_fourier_parts (p : Polynomial ℂ)
    (D N : ℕ) (y : ℝ) (S : Finset (ZMod (2 ^ (32 * N) + 1))) :
    zetaMoebiusBandFilter p D N y = zetaMoebiusCenteredFourierPart p D N y S +
      zetaMoebiusCenteredFourierPart p D N y Sᶜ := by
  rw [zetaMoebiusBandFilter_eq_weighted_pair]
  exact sum_mul_eq_centeredFourierPart_add_compl _ _ _ (by simp [zetaQuarterKernelSamples])

/-- The new resonant norm allowance includes a positive fractional
phase factor. It is uniform over every actual divisor cutoff. -/
theorem norm_zetaMoebiusCenteredFourierPart_le (p : Polynomial ℂ) (D N : ℕ)
    (y : ℝ) (S : Finset (ZMod (2 ^ (32 * N) + 1))) {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ < 1 / 4) :
    ‖zetaMoebiusCenteredFourierPart p D N y S‖ ≤
      ((2 ^ (32 * N) + 1 : ℕ) : ℝ)⁻¹ * (2 * zetaMoebiusLogMajorantMass (5 / 4 - τ)) *
        ∑ k ∈ S, ‖cyclicDifferenceSymbol k‖ ^ τ * ‖ZMod.dft (zetaQuarterKernelSamples p N y) k‖ := by
  apply (norm_centeredFourierPart_le_fractional_moment
    (zetaMoebiusWeightedBandSamples D N) (zetaQuarterKernelSamples p N y) S hτ0
      (by linarith)).trans
  gcongr
  exact sum_norm_zetaMoebiusWeightedBandSamples_mul_rpow_le D N hτ1

/-- The entire difference from the previous resonant carrier is bounded
by the already controlled complementary difference budget. -/
theorem norm_zetaMoebiusCenteredFourierPart_sub_weighted_le (p : Polynomial ℂ)
    (D N : ℕ) (y : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ‖zetaMoebiusCenteredFourierPart p D N y (zetaMoebiusResonantModes N δ) -
      zetaMoebiusWeightedFourierPart p D N y (zetaMoebiusResonantModes N δ)‖ ≤
      zetaMoebiusLogMajorantMass (5 / 4) *
        (δ⁻¹ ^ 2 * ∑ j, ‖(cyclicDifference^[2] (zetaQuarterKernelSamples p N y)) j‖) := by
  apply (norm_centeredFourierPart_sub_le_difference
    (zetaMoebiusWeightedBandSamples D N) (zetaQuarterKernelSamples p N y)
    (zetaMoebiusResonantModes N δ) (by simp [zetaQuarterKernelSamples]) 2 hδ (by
      intro k hk
      have hn := Finset.mem_compl.mp hk
      simpa [zetaMoebiusResonantModes, not_lt] using hn)).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [ZMod.dft_apply_zero]
  exact (norm_sum_le _ _).trans (sum_norm_zetaMoebiusWeightedBandSamples_le D N)

/-- The constant Fourier component is independently negligible on the
whole shrinking resonant region, for every moving divisor schedule. -/
theorem tendsto_zetaMoebiusCenteredFourierPart_sub_weighted (p : Polynomial ℂ)
    (D : ℕ → ℕ) (y : ℝ) :
    Tendsto (fun N ↦
      zetaMoebiusCenteredFourierPart p (D N) N y
        (zetaMoebiusResonantModes N (zetaMoebiusResonanceThreshold N)) -
      zetaMoebiusWeightedFourierPart p (D N) N y
        (zetaMoebiusResonantModes N (zetaMoebiusResonanceThreshold N))) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun N ↦ norm_zetaMoebiusCenteredFourierPart_sub_weighted_le
    p (D N) N y (zetaMoebiusResonanceThreshold_pos N))
  simpa only [mul_zero] using (tendsto_shrinking_gap_cyclicSecond_quarterKernel p y).const_mul
    (zetaMoebiusLogMajorantMass (5 / 4))

/-- The full negative multiplicity survives in the centered arithmetic
increments. The removed constant component has been independently bounded,
and the fractional modulus has not been assumed to bound the signed sum. -/
theorem tendsto_zetaRightHalfMoebius_centered_resonance (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaMoebiusCenteredFourierPart (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) N rho.1.im
        (zetaMoebiusResonantModes N (zetaMoebiusResonanceThreshold N)))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu0 : 0 ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : 3 / 2 - rho.1.re < 1 := by linarith
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hu0 hu1).mul_const (3 / 2 - rho.1.re)
  simp only [← pow_succ, zero_mul] at hp
  have hpc := Complex.continuous_ofReal.continuousAt.tendsto.comp hp
  simp only [Function.comp_def, Complex.ofReal_pow, Complex.ofReal_zero] at hpc
  have hc := hpc.mul (tendsto_zetaMoebiusCenteredFourierPart_sub_weighted
    (zetaRightHalfPoleJetFilter rho hrho)
    (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re))) rho.1.im)
  have h := (tendsto_zetaRightHalfMoebius_shrinking_resonance rho hrho).add hc
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [mul_sub, add_sub_cancel]

end
end RiemannGaussian
