/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaDominatedMomentBand
import RiemannGaussian.ZetaMoebiusWeightedFourier
import RiemannGaussian.FiniteFourierCentering

/-!
# Weighted Fourier localization for every dominated arithmetic family

The logarithmic band's lower endpoint makes its weighted arithmetic mass
decay geometrically. This gain holds for every complex coefficient family
dominated by the divisor majorant, including moving arithmetic sieves.
The exact centered Fourier pairing retains all coefficient signs and phases.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The original arithmetic coefficients with the exactly compensating
Dirichlet weight, sampled on the original logarithmic band. -/
def zetaArithmeticWeightedSamples (a : ℕ → ℂ) (N : ℕ) :
    ZMod (2 ^ (32 * N) + 1) → ℂ :=
  zetaLogBandSamples N (fun n ↦ a n * zetaPrimeFeature (5 / 4) n)

/-- Weight transfer preserves the full signed arithmetic band term by term. -/
theorem zetaArithmeticBand_eq_weighted_pair (a : ℕ → ℂ)
    (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    zetaArithmeticBand a p N y =
      ∑ j, zetaArithmeticWeightedSamples a N j * zetaQuarterKernelSamples p N y j := by
  have he (j : ZMod (2 ^ (32 * N) + 1)) :
      zetaArithmeticWeightedSamples a N j * zetaQuarterKernelSamples p N y j =
        zetaLogBandSamples N (fun n ↦ a n *
          zetaPrimeFilterKernel p N (3 / 2 + I * y) n) j := by
    by_cases hj : j.val ∈ zetaPrimeLogBand N
    · have hj0 : j.val ≠ 0 := by
        have h := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1
        omega
      simp only [zetaArithmeticWeightedSamples, zetaLogBandSamples, zetaQuarterKernelSamples,
        if_pos hj, if_neg hj0, mul_assoc, zetaPrimeFeature_mul_quarterKernel]
    · simp [zetaArithmeticWeightedSamples, zetaLogBandSamples, hj]
  simp_rw [he]
  rw [sum_zetaLogBandSamples]
  rfl

/-- Every convergent intermediate Dirichlet weight exposes a geometric
gain from the lower band endpoint. The estimate is uniform over all
dominated complex coefficient families. -/
theorem sum_norm_zetaArithmeticWeightedSamples_le_exp (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n) (N : ℕ)
    {σ : ℝ} (hσ : 1 < σ) (hσ' : σ ≤ 5 / 4) :
    (∑ j, ‖zetaArithmeticWeightedSamples a N j‖) ≤
      Real.exp (-(5 / 4 - σ) * (N : ℝ) * Real.log 2 / 4) *
        zetaMoebiusLogMajorantMass σ := by
  have he (j : ZMod (2 ^ (32 * N) + 1)) :
      ‖zetaArithmeticWeightedSamples a N j‖ = zetaLogBandSamples N
        (fun n ↦ ‖a n‖ * zetaPrimeExpWeight (5 / 4) n) j := by
    by_cases hj : j.val ∈ zetaPrimeLogBand N
      <;> simp [zetaArithmeticWeightedSamples, zetaLogBandSamples, hj, norm_zetaPrimeFeature]
  simp_rw [he]
  rw [sum_zetaLogBandSamples]
  have hw (n : ℕ) (hn : n ∈ zetaPrimeLogBand N) :
      zetaPrimeExpWeight (5 / 4) n ≤
        Real.exp (-(5 / 4 - σ) * (N : ℝ) * Real.log 2 / 4) *
          zetaPrimeExpWeight σ n := by
    have hl := (Finset.mem_filter.mp hn).2
    unfold zetaPrimeExpWeight
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hl.le (sub_nonneg.mpr hσ')
    nlinarith
  calc
    _ ≤ ∑ n ∈ zetaPrimeLogBand N, zetaMoebiusLogMajorant n *
        (Real.exp (-(5 / 4 - σ) * (N : ℝ) * Real.log 2 / 4) * zetaPrimeExpWeight σ n) := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul (ha n) (hw n hn) (Real.exp_pos _).le (zetaMoebiusLogMajorant_nonneg n)
    _ = Real.exp (-(5 / 4 - σ) * (N : ℝ) * Real.log 2 / 4) *
        ∑ n ∈ zetaPrimeLogBand N, zetaMoebiusLogMajorant n * zetaPrimeExpWeight σ n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Summable.sum_le_tsum (zetaPrimeLogBand N)
        (fun n _ ↦ mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le)
        (summable_zetaMoebiusLogMajorant hσ)) (Real.exp_pos _).le

/-- A rational geometric envelope for the band mass, with all constants
independent of the coefficient sequence and its arithmetic support. -/
theorem sum_norm_zetaArithmeticWeightedSamples_le (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n) (N : ℕ) :
    (∑ j, ‖zetaArithmeticWeightedSamples a N j‖) ≤
      (48 / 49 : ℝ) ^ N * zetaMoebiusLogMajorantMass (9 / 8) := by
  apply (sum_norm_zetaArithmeticWeightedSamples_le_exp a ha N
    (by norm_num : (1 : ℝ) < 9 / 8) (by norm_num)).trans
  apply mul_le_mul_of_nonneg_right _ (zetaMoebiusLogMajorantMass_nonneg _)
  have hb : Real.exp (-(1 / 48 : ℝ)) ≤ 48 / 49 := by
    rw [Real.exp_neg]
    have h := Real.add_one_le_exp (1 / 48 : ℝ)
    apply (inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 48 / 49)).mpr
    norm_num
    linarith
  calc
    _ ≤ Real.exp ((N : ℝ) * (-(1 / 48 : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have hl : (2 / 3 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (sub_nonneg.mpr hl.le)]
    _ = Real.exp (-(1 / 48 : ℝ)) ^ N := Real.exp_nat_mul _ _
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hb N

/-- The full signed band, expressed as centered arithmetic Fourier
increments paired with the quarter-line kernel. -/
def zetaArithmeticCenteredPart (a : ℕ → ℂ) (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (S : Finset (ZMod (2 ^ (32 * N) + 1))) : ℂ :=
  centeredFourierPart (zetaArithmeticWeightedSamples a N) (zetaQuarterKernelSamples p N y) S

/-- Every frequency partition preserves the original band exactly,
including the centering correction on both pieces. -/
theorem zetaArithmeticBand_eq_centered_parts (a : ℕ → ℂ)
    (p : Polynomial ℂ) (N : ℕ) (y : ℝ) (S : Finset (ZMod (2 ^ (32 * N) + 1))) :
    zetaArithmeticBand a p N y = zetaArithmeticCenteredPart a p N y S +
      zetaArithmeticCenteredPart a p N y Sᶜ := by
  rw [zetaArithmeticBand_eq_weighted_pair]
  exact sum_mul_eq_centeredFourierPart_add_compl _ _ _ (by simp [zetaQuarterKernelSamples])

/-- The centered arithmetic factor keeps the exact phase difference
and every original coefficient inside the same finite sum. -/
theorem zetaArithmeticWeightedDFT_sub_zero_eq (a : ℕ → ℂ) (N : ℕ)
    (k : ZMod (2 ^ (32 * N) + 1)) :
    ZMod.dft (zetaArithmeticWeightedSamples a N) (-k) -
      ZMod.dft (zetaArithmeticWeightedSamples a N) 0 =
        ∑ n ∈ zetaPrimeLogBand N, (a n * zetaPrimeFeature (5 / 4) n) *
          (ZMod.stdAddChar k ^ n - 1) := by
  rw [dft_sub_zero_eq]
  have he (j : ZMod (2 ^ (32 * N) + 1)) :
      zetaArithmeticWeightedSamples a N j * (ZMod.stdAddChar k ^ j.val - 1) =
        zetaLogBandSamples N (fun n ↦ (a n * zetaPrimeFeature (5 / 4) n) *
          (ZMod.stdAddChar k ^ n - 1)) j := by
    by_cases hj : j.val ∈ zetaPrimeLogBand N <;>
      simp [zetaArithmeticWeightedSamples, zetaLogBandSamples, hj]
  simp_rw [he]
  exact sum_zetaLogBandSamples _ _

/-- A symbol gap controls the whole centered interaction through the
absolute arithmetic mass and kernel differences. Both centering terms
are included in the bound. -/
theorem norm_centeredFourierPart_le_sum_norm_difference {q : ℕ} [NeZero q]
    (a f : ZMod q → ℂ) (S : Finset (ZMod q)) (r : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hS : ∀ k ∈ S, δ ≤ ‖cyclicDifferenceSymbol k‖) :
    ‖centeredFourierPart a f S‖ ≤
      2 * (∑ j, ‖a j‖) * (δ⁻¹ ^ r * ∑ j, ‖(cyclicDifference^[r] f) j‖) := by
  have ha : ‖ZMod.dft a 0‖ ≤ ∑ j, ‖a j‖ := by
    rw [ZMod.dft_apply_zero]
    exact norm_sum_le _ _
  have hzero : ‖finiteFourierPart cyclicZeroAtom f S‖ ≤
      δ⁻¹ ^ r * ∑ j, ‖(cyclicDifference^[r] f) j‖ := by
    simpa only [sum_norm_cyclicZeroAtom, mul_one] using
      norm_finiteFourierPart_le_sum_norm_difference cyclicZeroAtom f S r hδ hS
  rw [centeredFourierPart_eq_sub]
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  calc
    _ ≤ δ⁻¹ ^ r * (∑ j, ‖a j‖) * (∑ j, ‖(cyclicDifference^[r] f) j‖) +
        (∑ j, ‖a j‖) * (δ⁻¹ ^ r * ∑ j, ‖(cyclicDifference^[r] f) j‖) := by
      exact add_le_add (norm_finiteFourierPart_le_sum_norm_difference a f S r hδ hS)
        (mul_le_mul ha hzero (norm_nonneg _) (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)))
    _ = _ := by ring

/-- Every dominated arithmetic family has a complementary frequency
bound that retains the logarithmic band's additional geometric decay. -/
theorem norm_zetaArithmeticCenteredPart_compl_le (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n) (p : Polynomial ℂ)
    (N r : ℕ) (y : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ‖zetaArithmeticCenteredPart a p N y (zetaMoebiusResonantModes N δ)ᶜ‖ ≤
      2 * ((48 / 49 : ℝ) ^ N * zetaMoebiusLogMajorantMass (9 / 8)) *
        (δ⁻¹ ^ r * ∑ j, ‖(cyclicDifference^[r] (zetaQuarterKernelSamples p N y)) j‖) := by
  apply (norm_centeredFourierPart_le_sum_norm_difference
    (zetaArithmeticWeightedSamples a N) (zetaQuarterKernelSamples p N y)
    (zetaMoebiusResonantModes N δ)ᶜ r hδ (by
      intro k hk
      have hn := Finset.mem_compl.mp hk
      simpa [zetaMoebiusResonantModes, not_lt] using hn)).trans
  gcongr
  exact sum_norm_zetaArithmeticWeightedSamples_le a ha N

end
end RiemannGaussian
