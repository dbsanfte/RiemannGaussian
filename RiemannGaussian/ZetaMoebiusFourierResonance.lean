/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteFourierResonance
import RiemannGaussian.ZetaMoebiusMomentBand

/-!
# Resonance analysis of the literal finite Möbius band

The genuine divisor coefficients and full complex factorial kernel are
embedded in a finite cyclic group. Fourier inversion preserves the band
exactly. A symbol gap controls the complementary interaction by the
kernel's cyclic differences; the resonant interaction is kept explicitly.
The complete interaction retains the selected-zero multiplicity limit.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- Embed an arithmetic function on the explicit logarithmic band, with
zero outside the band and no aliasing of its positive integer indices. -/
def zetaLogBandSamples {E : Type*} [Zero E] (N : ℕ) (a : ℕ → E)
    (j : ZMod (2 ^ (32 * N) + 1)) : E :=
  if j.val ∈ zetaPrimeLogBand N then a j.val else 0

/-- Summing the cyclic embedding recovers precisely the original band. -/
theorem sum_zetaLogBandSamples {E : Type*} [AddCommMonoid E] (N : ℕ) (a : ℕ → E) :
    (∑ j, zetaLogBandSamples N a j) = ∑ n ∈ zetaPrimeLogBand N, a n := by
  change (∑ j : Fin (2 ^ (32 * N) + 1),
    if j.val ∈ zetaPrimeLogBand N then a j.val else 0) = _
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ ↦
    if n ∈ zetaPrimeLogBand N then a n else 0)]
  have hsub : zetaPrimeLogBand N ⊆ Finset.range (2 ^ (32 * N) + 1) := by
    intro n hn
    have h := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    exact Finset.mem_range.mpr (by omega)
  calc
    _ = ∑ n ∈ zetaPrimeLogBand N, if n ∈ zetaPrimeLogBand N then a n else 0 := by
      exact (Finset.sum_subset hsub (fun n _ hn ↦ if_neg hn)).symm
    _ = _ := Finset.sum_congr rfl (fun n hn ↦ if_pos hn)

/-- The actual signed divisor coefficients on the finite band. -/
def zetaMoebiusBandSamples (D N : ℕ) : ZMod (2 ^ (32 * N) + 1) → ℂ :=
  zetaLogBandSamples N (zetaMoebiusLogTailCoefficient D)

/-- Samples of the full complex kernel. The unused zero index is set
to zero explicitly; its difference with the last sample is retained. -/
def zetaMoebiusKernelSamples (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (j : ZMod (2 ^ (32 * N) + 1)) : ℂ :=
  if j.val = 0 then 0 else zetaPrimeFilterKernel p N (3 / 2 + I * y) j.val

/-- The original finite Möbius band is the exact pairing of the two
sample vectors, with no change of its signs, phase, or factorial weights. -/
theorem zetaMoebiusBandFilter_eq_sample_pair (p : Polynomial ℂ) (D N : ℕ) (y : ℝ) :
    zetaMoebiusBandFilter p D N y = ∑ j,
      zetaMoebiusBandSamples D N j * zetaMoebiusKernelSamples p N y j := by
  have he (j : ZMod (2 ^ (32 * N) + 1)) :
      zetaMoebiusBandSamples D N j * zetaMoebiusKernelSamples p N y j =
        zetaLogBandSamples N (fun n ↦ zetaMoebiusLogTailCoefficient D n *
          zetaPrimeFilterKernel p N (3 / 2 + I * y) n) j := by
    by_cases hj : j.val ∈ zetaPrimeLogBand N
    · have hj0 : j.val ≠ 0 := by
        have h := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1
        omega
      simp [zetaMoebiusBandSamples, zetaLogBandSamples, zetaMoebiusKernelSamples, hj, hj0]
    · simp [zetaMoebiusBandSamples, zetaLogBandSamples, hj]
  simp_rw [he]
  rw [sum_zetaLogBandSamples, zetaMoebiusBandFilter_eq_sum]

/-- The signed interaction in a chosen finite frequency region. -/
def zetaMoebiusBandFourierPart (p : Polynomial ℂ) (D N : ℕ) (y : ℝ)
    (S : Finset (ZMod (2 ^ (32 * N) + 1))) : ℂ :=
  finiteFourierPart (zetaMoebiusBandSamples D N) (zetaMoebiusKernelSamples p N y) S

/-- Every frequency split retains the entire actual arithmetic band. -/
theorem zetaMoebiusBandFilter_eq_fourier_parts (p : Polynomial ℂ) (D N : ℕ) (y : ℝ)
    (S : Finset (ZMod (2 ^ (32 * N) + 1))) :
    zetaMoebiusBandFilter p D N y = zetaMoebiusBandFourierPart p D N y S +
      zetaMoebiusBandFourierPart p D N y Sᶜ := by
  rw [zetaMoebiusBandFilter_eq_sample_pair]
  exact sum_mul_eq_fourierPart_add_compl _ _ _

/-- The complete arithmetic energy is exactly its original finite sum. -/
theorem sum_norm_zetaMoebiusBandSamples_sq (D N : ℕ) :
    (∑ j, ‖zetaMoebiusBandSamples D N j‖ ^ 2) =
      ∑ n ∈ zetaPrimeLogBand N, ‖zetaMoebiusLogTailCoefficient D n‖ ^ 2 := by
  have he (j : ZMod (2 ^ (32 * N) + 1)) :
      ‖zetaMoebiusBandSamples D N j‖ ^ 2 =
        zetaLogBandSamples N (fun n ↦ ‖zetaMoebiusLogTailCoefficient D n‖ ^ 2) j := by
    by_cases hj : j.val ∈ zetaPrimeLogBand N
      <;> simp [zetaMoebiusBandSamples, zetaLogBandSamples, hj]
  simp_rw [he]
  exact sum_zetaLogBandSamples _ _

/-- The resonant set consists of all modes where the difference symbol
is below the requested threshold. It is defined for the entire family. -/
def zetaMoebiusResonantModes (N : ℕ) (δ : ℝ) : Finset (ZMod (2 ^ (32 * N) + 1)) :=
  Finset.univ.filter (fun k ↦ ‖cyclicDifferenceSymbol k‖ < δ)

/-- Every positive threshold retains the exact central mode. -/
theorem zero_mem_zetaMoebiusResonantModes (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 ∈ zetaMoebiusResonantModes N δ := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  simpa [cyclicDifferenceSymbol] using hδ

/-- A quantitative bound for the actual nonresonant interaction, valid
at every order and cutoff. Its physical difference energy includes the
cyclic boundary and retains the full complex kernel. -/
theorem norm_zetaMoebiusBand_sub_resonant_sq_le (p : Polynomial ℂ) (D N r : ℕ) (y : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ‖zetaMoebiusBandFilter p D N y -
      zetaMoebiusBandFourierPart p D N y (zetaMoebiusResonantModes N δ)‖ ^ 2 ≤
      (δ⁻¹ ^ r) ^ 2 *
        (∑ n ∈ zetaPrimeLogBand N, ‖zetaMoebiusLogTailCoefficient D n‖ ^ 2) *
        ∑ j, ‖(cyclicDifference^[r] (zetaMoebiusKernelSamples p N y)) j‖ ^ 2 := by
  rw [zetaMoebiusBandFilter_eq_fourier_parts p D N y (zetaMoebiusResonantModes N δ),
    add_sub_cancel_left]
  have h := norm_finiteFourierPart_sq_le_physical_difference
    (zetaMoebiusBandSamples D N) (zetaMoebiusKernelSamples p N y)
    (zetaMoebiusResonantModes N δ)ᶜ r hδ (by
      intro k hk
      have hn := Finset.mem_compl.mp hk
      simpa [zetaMoebiusResonantModes, not_lt] using hn)
  rw [sum_norm_zetaMoebiusBandSamples_sq] at h
  exact h

/-- The same nonresonant bound has a cutoff-independent arithmetic
majorant. This is an upper bound, not a claim that its normalized budget decays. -/
theorem norm_zetaMoebiusBand_sub_resonant_sq_le_majorant (p : Polynomial ℂ)
    (D N r : ℕ) (y : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ‖zetaMoebiusBandFilter p D N y -
      zetaMoebiusBandFourierPart p D N y (zetaMoebiusResonantModes N δ)‖ ^ 2 ≤
      (δ⁻¹ ^ r) ^ 2 * (∑ n ∈ zetaPrimeLogBand N, zetaMoebiusLogMajorant n ^ 2) *
        ∑ j, ‖(cyclicDifference^[r] (zetaMoebiusKernelSamples p N y)) j‖ ^ 2 := by
  apply (norm_zetaMoebiusBand_sub_resonant_sq_le p D N r y hδ).trans
  gcongr with n _
  exact norm_zetaMoebiusLogTailCoefficient_le D n

/-- Any moving frequency partition retains the full selected-zero
source in the sum of its two signed interactions. No part is declared
negligible on the strength of the exact decomposition alone. -/
theorem tendsto_zetaRightHalfMoebiusFourier_parts (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (S : (N : ℕ) → Finset (ZMod (2 ^ (32 * N) + 1))) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      (zetaMoebiusBandFourierPart (zetaRightHalfPoleJetFilter rho hrho)
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
          N rho.1.im (S N) +
        zetaMoebiusBandFourierPart (zetaRightHalfPoleJetFilter rho hrho)
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
          N rho.1.im (S N)ᶜ)) atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  simpa only [← zetaMoebiusBandFilter_eq_fourier_parts] using
    tendsto_zetaRightHalfMoebiusBand rho hrho

end
end RiemannGaussian
