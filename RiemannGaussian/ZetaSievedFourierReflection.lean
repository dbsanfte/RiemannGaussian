/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteFourierReflection
import RiemannGaussian.ZetaSievedFourierTrig

/-!
# Exact parity cancellation in the actual sieved arithmetic work

The retained symbol region is closed under opposite frequencies. Its
centered real kernel is an exact signed sine product, odd under physical
reflection about half the arithmetic index. The actual imaginary physical
component and the canonical even real component both contribute zero.
The original multiplicity source remains in the coupled odd real work;
its independent one-sided bound is still the open obligation.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- Every original symbol region is closed under opposite frequencies,
including zero, self-opposite frequencies, and empty regions. -/
theorem zetaMoebiusResonantModes_neg_closed (N : ℕ) (δ : ℝ) :
    ∀ k ∈ zetaMoebiusResonantModes N δ, -k ∈ zetaMoebiusResonantModes N δ := by
  intro k hk
  simpa only [zetaMoebiusResonantModes, Finset.mem_filter, Finset.mem_univ,
    true_and, norm_cyclicDifferenceSymbol_neg] using hk

private theorem character_mul_eq_exp {q : ℕ} [NeZero q] (k n : ZMod q) :
    ZMod.stdAddChar (k * n) = Complex.exp ((cyclicPhaseAngle k n.val : ℂ) * I) := by
  rw [← stdAddChar_pow_eq_exp_phase, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul,
    ZMod.natCast_zmod_val, mul_comm]

private theorem character_sub_re {q : ℕ} [NeZero q] (k n m : ZMod q) :
    (ZMod.stdAddChar (k * (n - m))).re =
      Real.cos (cyclicPhaseAngle k n.val - cyclicPhaseAngle k m.val) := by
  rw [mul_sub, AddChar.map_sub_eq_div, character_mul_eq_exp, character_mul_eq_exp,
    ← Complex.exp_sub]
  have he : (cyclicPhaseAngle k n.val : ℂ) * I - (cyclicPhaseAngle k m.val : ℂ) * I =
      ((cyclicPhaseAngle k n.val - cyclicPhaseAngle k m.val : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [he, Complex.exp_re]
  simp

/-- The projection difference is an exact cosine difference at every
original cyclic index. Its two phases remain coupled inside the sum. -/
theorem cyclicCenteredRealKernel_eq_cosine {q : ℕ} [NeZero q]
    (S : Finset (ZMod q)) (n m : ZMod q) :
    cyclicCenteredRealKernel S n m = (q : ℝ)⁻¹ * ∑ k ∈ S,
      (Real.cos (cyclicPhaseAngle k n.val - cyclicPhaseAngle k m.val) -
        Real.cos (cyclicPhaseAngle k m.val)) := by
  have hq : (q : ℂ)⁻¹ = ((q : ℝ)⁻¹ : ℝ) := by simp
  unfold cyclicCenteredRealKernel cyclicFourierKernel
  rw [hq, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_sum, Complex.re_sum,
    ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [character_sub_re, character_mul_eq_exp, Complex.exp_re]
  simp

/-- Product-to-sum exposes the sign-bearing physical reflection factor.
The second sine reverses at the arithmetic midpoint; the cyclic identity
is valid without choosing a half-index in the finite group. -/
theorem cyclicCenteredRealKernel_eq_sine {q : ℕ} [NeZero q]
    (S : Finset (ZMod q)) (n m : ZMod q) :
    cyclicCenteredRealKernel S n m = (-2 / (q : ℝ)) * ∑ k ∈ S,
      Real.sin (cyclicPhaseAngle k n.val / 2) *
        Real.sin (cyclicPhaseAngle k n.val / 2 - cyclicPhaseAngle k m.val) := by
  have he (x y : ℝ) : Real.cos (x - y) - Real.cos y =
      -2 * Real.sin (x / 2) * Real.sin (x / 2 - y) := by
    rw [Real.cos_sub_cos, show ((x - y) + y) / 2 = x / 2 by ring,
      show ((x - y) - y) / 2 = x / 2 - y by ring]
  rw [cyclicCenteredRealKernel_eq_cosine, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [he]
  ring

/-- The arithmetic endpoint has a nonnegative exact cosine reserve.
The sign follows before estimating or separating the phase factors. -/
theorem cyclicCenteredRealKernel_self_nonneg {q : ℕ} [NeZero q]
    (S : Finset (ZMod q)) (n : ZMod q) : 0 ≤ cyclicCenteredRealKernel S n n := by
  rw [cyclicCenteredRealKernel_eq_cosine]
  simp only [sub_self, Real.cos_zero]
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun _ _ ↦ sub_nonneg.mpr (Real.cos_le_one _))

/-- The opposite endpoint has the opposite sign. This records why
positivity of the whole centered kernel cannot simply be presumed. -/
theorem cyclicCenteredRealKernel_zero_nonpos {q : ℕ} [NeZero q]
    (S : Finset (ZMod q)) (n : ZMod q) : cyclicCenteredRealKernel S n 0 ≤ 0 := by
  have h := cyclicCenteredRealKernel_reflect S n 0
  simp only [sub_zero] at h
  linarith [cyclicCenteredRealKernel_self_nonneg S n]

/-- A real Dirichlet parameter gives the original positive sampling
weight exactly, including the explicitly totalized unused zero index. -/
theorem zetaPrimeFeature_ofReal_eq_expWeight (σ : ℝ) (n : ℕ) :
    zetaPrimeFeature (σ : ℂ) n = (zetaPrimeExpWeight σ n : ℂ) := by
  unfold zetaPrimeFeature zetaPrimeExpWeight
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

private theorem quarter_weight_real (n : ℕ) :
    zetaPrimeFeature (5 / 4) n = (zetaPrimeExpWeight (5 / 4) n : ℂ) := by
  simpa using zetaPrimeFeature_ofReal_eq_expWeight (5 / 4) n

/-- The real weighted sample retains the signed real coefficient and
the complete original band mask. -/
theorem zetaArithmeticWeightedSamples_re (a : ℕ → ℂ) (N : ℕ)
    (j : ZMod (2 ^ (32 * N) + 1)) :
    (zetaArithmeticWeightedSamples a N j).re =
      zetaLogBandSamples N (fun n ↦ (a n).re * zetaPrimeExpWeight (5 / 4) n) j := by
  by_cases hj : j.val ∈ zetaPrimeLogBand N <;>
    simp [zetaArithmeticWeightedSamples, zetaLogBandSamples, hj, quarter_weight_real,
      Complex.mul_re]

/-- Real arithmetic coefficients stay real through exact band sampling
and Dirichlet weight transfer. -/
theorem zetaArithmeticWeightedSamples_im (a : ℕ → ℂ)
    (ha : ∀ n, (a n).im = 0) (N : ℕ) (j : ZMod (2 ^ (32 * N) + 1)) :
    (zetaArithmeticWeightedSamples a N j).im = 0 := by
  by_cases hj : j.val ∈ zetaPrimeLogBand N <;>
    simp [zetaArithmeticWeightedSamples, zetaLogBandSamples, hj, quarter_weight_real,
      Complex.mul_im, ha]

/-- The whole imaginary physical component of the actual quarter-line
kernel makes zero contribution to the relevant real sieved interaction.
This cancellation is exact for every finite cutoff and sieve. -/
theorem zetaMoebiusSievedFourier_imaginary_eq_zero (p : Polynomial ℂ)
    (D : ℕ) (S : Finset ℕ) (N : ℕ) (y : ℝ) :
    (centeredFourierPart
      (zetaArithmeticWeightedSamples (zetaMoebiusSievedPrimeCoefficient D S) N)
      (fun j ↦ I * ((zetaQuarterKernelSamples p N y j).im : ℂ))
      (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N))).re = 0 :=
  centeredFourierPart_re_imaginary_eq_zero _
    (zetaArithmeticWeightedSamples_im _ (zetaMoebiusSievedPrimeCoefficient_im D S) N) _ _
    (zetaMoebiusResonantModes_neg_closed N _)

/-- The canonical even real component also cancels after the full
arithmetic summation. All sieve signs and all cyclic reflection partners
are retained before this exact zero is used. -/
theorem zetaMoebiusSievedFourier_even_reflection_eq_zero (p : Polynomial ℂ)
    (D : ℕ) (S : Finset ℕ) (N : ℕ) (y : ℝ) :
    (∑ n, (zetaArithmeticWeightedSamples (zetaMoebiusSievedPrimeCoefficient D S) N n).re *
      ∑ m, cyclicCenteredRealKernel
        (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N)) n m *
          (((zetaQuarterKernelSamples p N y m).re +
            (zetaQuarterKernelSamples p N y (n - m)).re) / 2)) = 0 := by
  simp only [sum_cyclicCenteredRealKernel_mul_even_part_eq_zero, mul_zero, Finset.sum_const_zero]

/-- The same real arithmetic work expressed using only the surviving
odd reflection of the real physical kernel. The normalization matches
the preceding signed trigonometric work exactly. -/
def zetaArithmeticReflectionWork (a : ℕ → ℂ) (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (S : Finset (ZMod (2 ^ (32 * N) + 1))) : ℝ :=
  -(1 / 4 : ℝ) * ∑ n, (zetaArithmeticWeightedSamples a N n).re * ∑ m,
    cyclicCenteredRealKernel S n m *
      ((zetaQuarterKernelSamples p N y m).re - (zetaQuarterKernelSamples p N y (n - m)).re)

/-- The real carrier equals minus twice the reflection work. This
uses exact cancellation, with no new approximation or error allowance. -/
theorem zetaArithmeticCenteredPart_re_eq_reflection (a : ℕ → ℂ)
    (ha : ∀ n, (a n).im = 0) (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (S : Finset (ZMod (2 ^ (32 * N) + 1))) (hS : ∀ k ∈ S, -k ∈ S) :
    (zetaArithmeticCenteredPart a p N y S).re =
      -2 * zetaArithmeticReflectionWork a p N y S := by
  rw [zetaArithmeticCenteredPart, centeredFourierPart_re_eq_reflection _ _
    (zetaArithmeticWeightedSamples_im a ha N) S hS]
  unfold zetaArithmeticReflectionWork
  ring

/-- The signed sine-square and sine-cosine work is exactly its real
reflection form. The imaginary Fourier channel of the real kernel is
still present through the signed product-to-sum kernel. -/
theorem zetaArithmeticTrigWork_eq_reflection (a : ℕ → ℂ)
    (ha : ∀ n, (a n).im = 0) (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (S : Finset (ZMod (2 ^ (32 * N) + 1))) (hS : ∀ k ∈ S, -k ∈ S) :
    zetaArithmeticTrigWork (fun n ↦ (a n).re) p N y S =
      zetaArithmeticReflectionWork a p N y S := by
  have h₁ := zetaArithmeticCenteredPart_re_eq_trig a ha p N y S
  have h₂ := zetaArithmeticCenteredPart_re_eq_reflection a ha p N y S hS
  linarith

/-- The actual selected-zero work is unchanged when both exactly
annihilated physical components are removed. -/
theorem zetaRightHalfSievedTrigWork_eq_reflection (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    zetaRightHalfSievedTrigWork rho hrho N =
      zetaArithmeticReflectionWork
        (zetaMoebiusSievedPrimeCoefficient
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
          (zetaRightHalfMoebiusSieve rho N))
        (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
        (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N)) :=
  zetaArithmeticTrigWork_eq_reflection _ (zetaMoebiusSievedPrimeCoefficient_im _ _)
    _ _ _ _ (zetaMoebiusResonantModes_neg_closed N _)

/-- The whole positive multiplicity source survives in the odd real
reflection work. Its strict independent upper bound remains unproved. -/
theorem tendsto_zetaRightHalfSievedReflectionWork (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ (3 / 2 - rho.1.re : ℝ) ^ (N + 1) *
      zetaArithmeticReflectionWork
        (zetaMoebiusSievedPrimeCoefficient
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
          (zetaRightHalfMoebiusSieve rho N))
        (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
        (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N)))
      atTop (𝓝 ((analyticZetaZeroMultiplicity rho : ℝ) / 2)) := by
  simpa only [zetaRightHalfSievedTrigWork_eq_reflection] using
    tendsto_zetaRightHalfSievedTrigWork rho hrho

/-- The existing total error controls the exact real scalar comparison
with half its former allowance. This factor is solely the exact work
normalization; both cancellations introduce zero additional error. -/
theorem exists_zetaRightHalfReflection_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      |-(3 / 2 - rho.1.re : ℝ) ^ (N + 1) *
          (zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N
            (3 / 2 + I * rho.1.im)).re / 2 -
        (3 / 2 - rho.1.re : ℝ) ^ (N + 1) *
          zetaArithmeticReflectionWork
            (zetaMoebiusSievedPrimeCoefficient
              (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
              (zetaRightHalfMoebiusSieve rho N))
            (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
            (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N))| ≤
        (C * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
          ((1 / 2 : ℝ) ^ N * zetaMoebiusBandTailConstant (zetaRightHalfPoleJetFilter rho hrho) +
            2 * zetaMoebiusLogMajorantMass (9 / 8) *
              zetaQuarterGapError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
                (48 / 49) (14 / 15))) / 2 := by
  obtain ⟨C, hC, hb⟩ := exists_zetaRightHalfSievedFourier_error_bound rho hrho
  refine ⟨C, hC, fun N hN ↦ ?_⟩
  let L := zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im)
  let u : ℝ := (3 / 2 - rho.1.re) ^ (N + 1)
  let z : ℂ := ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    (L - zetaRightHalfSievedFourierCarrier rho hrho N)
  have hz : z.re = u * (L.re + 2 * zetaRightHalfSievedTrigWork rho hrho N) := by
    dsimp [z, u]
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.sub_re,
      zetaRightHalfSievedFourierCarrier_re_eq]
    ring
  rw [← zetaRightHalfSievedTrigWork_eq_reflection rho hrho N]
  change |-u * L.re / 2 - u * zetaRightHalfSievedTrigWork rho hrho N| ≤ _
  have he : -u * L.re / 2 - u * zetaRightHalfSievedTrigWork rho hrho N = -z.re / 2 := by
    rw [hz]
    ring
  rw [he, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right ((Complex.abs_re_le_norm z).trans (hb N hN)) (by norm_num)

end
end RiemannGaussian
