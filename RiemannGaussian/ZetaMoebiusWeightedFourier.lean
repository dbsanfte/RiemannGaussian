/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusFourierResonance
import RiemannGaussian.ZetaPrimeKernelSecondDifference
import RiemannGaussian.FiniteFourierDifferenceDecay

/-!
# Exact Dirichlet weighting of the finite Möbius Fourier carrier

Moving the fixed weight `n^(-5/4)` to the arithmetic coefficients shifts
the kernel from real part `3/2` to `1/4` without changing their product.
The arithmetic absolute mass is then bounded independently of both band
size and divisor cutoff. Two differences of the shifted kernel provide
the remaining nonresonant budget.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The actual signed coefficients with a fixed convergent Dirichlet
weight; no coefficient search or cutoff-dependent fitting is involved. -/
def zetaMoebiusWeightedBandSamples (D N : ℕ) : ZMod (2 ^ (32 * N) + 1) → ℂ :=
  zetaLogBandSamples N (fun n ↦ zetaMoebiusLogTailCoefficient D n * zetaPrimeFeature (5 / 4) n)

/-- The exactly compensating quarter-line kernel, with its zero sample
specified separately from its genuine positive-index values. -/
def zetaQuarterKernelSamples (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (j : ZMod (2 ^ (32 * N) + 1)) : ℂ :=
  if j.val = 0 then 0 else zetaPrimeFilterKernel p N (1 / 4 + I * y) j.val

/-- Every positive sample through the endpoint retains the full kernel. -/
theorem zetaQuarterKernelSamples_nat (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {n : ℕ} (hn : 0 < n) (hN : n < 2 ^ (32 * N) + 1) :
    zetaQuarterKernelSamples p N y n = zetaPrimeFilterKernel p N (1 / 4 + I * y) n := by
  simp [zetaQuarterKernelSamples, ZMod.val_natCast_of_lt hN, hn.ne']

/-- The compensating parameter shift preserves each original complex
arithmetic atom before Fourier transformation. -/
theorem zetaPrimeFeature_mul_quarterKernel (p : Polynomial ℂ) (N n : ℕ) (y : ℝ) :
    zetaPrimeFeature (5 / 4) n * zetaPrimeFilterKernel p N (1 / 4 + I * y) n =
      zetaPrimeFilterKernel p N (3 / 2 + I * y) n := by
  rw [mul_comm, zetaPrimeFeature, ← neg_mul, ← zetaPrimeFilterKernel_add_parameter]
  congr 1
  ring

/-- The fixed Dirichlet weighting leaves the literal finite band unchanged. -/
theorem zetaMoebiusBandFilter_eq_weighted_pair (p : Polynomial ℂ) (D N : ℕ) (y : ℝ) :
    zetaMoebiusBandFilter p D N y =
      ∑ j, zetaMoebiusWeightedBandSamples D N j * zetaQuarterKernelSamples p N y j := by
  have he (j : ZMod (2 ^ (32 * N) + 1)) :
      zetaMoebiusWeightedBandSamples D N j * zetaQuarterKernelSamples p N y j =
        zetaLogBandSamples N (fun n ↦ zetaMoebiusLogTailCoefficient D n *
          zetaPrimeFilterKernel p N (3 / 2 + I * y) n) j := by
    by_cases hj : j.val ∈ zetaPrimeLogBand N
    · have hj0 : j.val ≠ 0 := by
        have h := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1
        omega
      simp only [zetaMoebiusWeightedBandSamples, zetaLogBandSamples, zetaQuarterKernelSamples,
        if_pos hj, if_neg hj0, mul_assoc, zetaPrimeFeature_mul_quarterKernel]
    · simp [zetaMoebiusWeightedBandSamples, zetaLogBandSamples, hj]
  simp_rw [he]
  rw [sum_zetaLogBandSamples, zetaMoebiusBandFilter_eq_sum]

/-- The arithmetic absolute mass is bounded independently of the
divisor cutoff and the growing Fourier group. -/
theorem sum_norm_zetaMoebiusWeightedBandSamples_le (D N : ℕ) :
    (∑ j, ‖zetaMoebiusWeightedBandSamples D N j‖) ≤ zetaMoebiusLogMajorantMass (5 / 4) := by
  have he (j : ZMod (2 ^ (32 * N) + 1)) :
      ‖zetaMoebiusWeightedBandSamples D N j‖ = zetaLogBandSamples N
        (fun n ↦ ‖zetaMoebiusLogTailCoefficient D n‖ * zetaPrimeExpWeight (5 / 4) n) j := by
    by_cases hj : j.val ∈ zetaPrimeLogBand N
      <;> simp [zetaMoebiusWeightedBandSamples, zetaLogBandSamples, hj, norm_zetaPrimeFeature]
  simp_rw [he]
  rw [sum_zetaLogBandSamples]
  calc
    _ ≤ ∑ n ∈ zetaPrimeLogBand N, zetaMoebiusLogMajorant n * zetaPrimeExpWeight (5 / 4) n := by
      apply Finset.sum_le_sum
      intro n _
      exact mul_le_mul_of_nonneg_right (norm_zetaMoebiusLogTailCoefficient_le D n) (Real.exp_pos _).le
    _ ≤ _ := Summable.sum_le_tsum (zetaPrimeLogBand N)
      (fun n _ ↦ mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le)
      (summable_zetaMoebiusLogMajorant (by norm_num))

/-- The signed finite Fourier interaction after the exact weight transfer. -/
def zetaMoebiusWeightedFourierPart (p : Polynomial ℂ) (D N : ℕ) (y : ℝ)
    (S : Finset (ZMod (2 ^ (32 * N) + 1))) : ℂ :=
  finiteFourierPart (zetaMoebiusWeightedBandSamples D N) (zetaQuarterKernelSamples p N y) S

/-- Every frequency split of the weighted vectors still recovers the
original arithmetic band with its full signs and phase. -/
theorem zetaMoebiusBandFilter_eq_weighted_fourier_parts (p : Polynomial ℂ) (D N : ℕ) (y : ℝ)
    (S : Finset (ZMod (2 ^ (32 * N) + 1))) :
    zetaMoebiusBandFilter p D N y = zetaMoebiusWeightedFourierPart p D N y S +
      zetaMoebiusWeightedFourierPart p D N y Sᶜ := by
  rw [zetaMoebiusBandFilter_eq_weighted_pair]
  exact sum_mul_eq_fourierPart_add_compl _ _ _

/-- The nonresonant estimate now has a fixed convergent arithmetic mass
instead of the unweighted energy of the entire expanding band. -/
theorem norm_zetaMoebiusWeightedFourierPart_compl_le (p : Polynomial ℂ)
    (D N r : ℕ) (y : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ‖zetaMoebiusWeightedFourierPart p D N y (zetaMoebiusResonantModes N δ)ᶜ‖ ≤
      δ⁻¹ ^ r * zetaMoebiusLogMajorantMass (5 / 4) *
        ∑ j, ‖(cyclicDifference^[r] (zetaQuarterKernelSamples p N y)) j‖ := by
  apply (norm_finiteFourierPart_le_sum_norm_difference
    (zetaMoebiusWeightedBandSamples D N) (zetaQuarterKernelSamples p N y)
    (zetaMoebiusResonantModes N δ)ᶜ r hδ (by
      intro k hk
      have hn := Finset.mem_compl.mp hk
      simpa [zetaMoebiusResonantModes, not_lt] using hn)).trans
  gcongr
  exact sum_norm_zetaMoebiusWeightedBandSamples_le D N

end
end RiemannGaussian
