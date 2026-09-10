/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteFourierCentering

/-!
# Physical tests of a fractional Fourier absolute budget

The absolute fractional Fourier mass must recover every physical sample
relative to the zero sample. This provides an independent test of whether
the decoupled norm budget could be small enough for a signed argument.
Its complementary mass retains the full cyclic difference cost.
-/

open Complex
open scoped Classical

namespace RiemannGaussian

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The normalized absolute Fourier mass with its fractional phase weight. -/
def fractionalFourierMass (τ : ℝ) (f : ZMod q → ℂ) (S : Finset (ZMod q)) : ℝ :=
  (q : ℝ)⁻¹ * ∑ k ∈ S, ‖cyclicDifferenceSymbol k‖ ^ τ * ‖ZMod.dft f k‖

/-- Every fractional Fourier absolute mass is nonnegative. -/
theorem fractionalFourierMass_nonneg (τ : ℝ) (f : ZMod q → ℂ) (S : Finset (ZMod q)) :
    0 ≤ fractionalFourierMass τ f S := by
  unfold fractionalFourierMass
  positivity

/-- The absolute mass partitions exactly, with the same cyclic normalization. -/
theorem fractionalFourierMass_add_compl (τ : ℝ) (f : ZMod q → ℂ) (S : Finset (ZMod q)) :
    fractionalFourierMass τ f S + fractionalFourierMass τ f Sᶜ =
      fractionalFourierMass τ f Finset.univ := by
  simp only [fractionalFourierMass, ← mul_add, Finset.sum_add_sum_compl]

/-- On a region with symbol norm at most one, increasing a nonnegative
fractional exponent decreases the absolute budget. This also handles zero. -/
theorem fractionalFourierMass_antitone_exponent (f : ZMod q → ℂ) (S : Finset (ZMod q))
    {τ υ : ℝ} (hτ : 0 ≤ τ) (hτυ : τ ≤ υ)
    (hS : ∀ k ∈ S, ‖cyclicDifferenceSymbol k‖ ≤ 1) :
    fractionalFourierMass υ f S ≤ fractionalFourierMass τ f S := by
  unfold fractionalFourierMass
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) (hS k hk) hτ hτυ) (norm_nonneg _)

/-- Fourier inversion keeps the complex phase increment at every physical sample. -/
theorem sub_zero_eq_fourier_increments (f : ZMod q → ℂ) (j : ZMod q) :
    f j - f 0 = (q : ℂ)⁻¹ * ∑ k,
      (ZMod.stdAddChar k ^ j.val - 1) * ZMod.dft f k := by
  have hj := congrFun (ZMod.dft.symm_apply_apply f) j
  have h0 := congrFun (ZMod.dft.symm_apply_apply f) 0
  rw [← hj, ← h0]
  simp only [ZMod.invDFT_apply, smul_eq_mul, mul_zero, AddChar.map_zero_eq_one, one_mul,
    ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have he : ZMod.stdAddChar (k * j) = ZMod.stdAddChar k ^ j.val := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]
  rw [he]
  ring

/-- A fractional absolute Fourier budget controls every physical sample,
so physical kernel values can disprove an overly small proposed budget. -/
theorem norm_sub_zero_le_fractionalFourierMass (f : ZMod q → ℂ) (j : ZMod q)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    ‖f j - f 0‖ ≤ 2 * (j.val : ℝ) ^ τ * fractionalFourierMass τ f Finset.univ := by
  rw [sub_zero_eq_fourier_increments, norm_mul, norm_inv, Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans
  calc
    _ ≤ (q : ℝ)⁻¹ * ∑ k,
        (2 * ((j.val : ℝ) * ‖cyclicDifferenceSymbol k‖) ^ τ) * ‖ZMod.dft f k‖ := by
      gcongr with k
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact norm_unit_pow_sub_one_le_rpow (by
        rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _) j.val hτ0 hτ1
    _ = _ := by
      simp only [fractionalFourierMass, Real.mul_rpow (Nat.cast_nonneg _) (norm_nonneg _),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- The counting-measure Fourier transform is bounded by the complete
physical absolute mass, uniformly in its frequency. -/
theorem norm_dft_le_sum_norm (f : ZMod q → ℂ) (k : ZMod q) :
    ‖ZMod.dft f k‖ ≤ ∑ j, ‖f j‖ := by
  rw [ZMod.dft_apply]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  simp only [smul_eq_mul, norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul]
  exact le_rfl

/-- A genuine symbol gap controls the full absolute fractional mass on
that region, including the complete physical difference cost. -/
theorem fractionalFourierMass_le_difference (f : ZMod q → ℂ) (S : Finset (ZMod q))
    (r : ℕ) {τ δ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hδ : 0 < δ)
    (hS : ∀ k ∈ S, δ ≤ ‖cyclicDifferenceSymbol k‖) :
    fractionalFourierMass τ f S ≤ 2 * δ⁻¹ ^ r * ∑ j, ‖(cyclicDifference^[r] f) j‖ := by
  have hweight (k : ZMod q) : ‖cyclicDifferenceSymbol k‖ ^ τ ≤ 2 := by
    have hn : ‖cyclicDifferenceSymbol k‖ ≤ 2 := by
      have h := norm_sub_le (ZMod.stdAddChar k) 1
      simpa only [cyclicDifferenceSymbol, ZMod.stdAddChar_apply, Circle.norm_coe,
        norm_one, one_add_one_eq_two] using h
    exact (Real.rpow_le_rpow (norm_nonneg _) hn hτ0).trans
      (Real.rpow_le_self_of_one_le (by norm_num) hτ1)
  have hb (k : ZMod q) (hk : k ∈ S) :
      ‖cyclicDifferenceSymbol k‖ ^ τ * ‖ZMod.dft f k‖ ≤
        2 * δ⁻¹ ^ r * ∑ j, ‖(cyclicDifference^[r] f) j‖ := by
    have hf := (norm_dft_le_difference_of_gap r f k hδ (hS k hk)).trans
      (mul_le_mul_of_nonneg_left (norm_dft_le_sum_norm _ _) (by positivity))
    calc
      _ ≤ 2 * (δ⁻¹ ^ r * ∑ j, ‖(cyclicDifference^[r] f) j‖) :=
        mul_le_mul (hweight k) hf (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  unfold fractionalFourierMass
  calc
    _ ≤ (q : ℝ)⁻¹ * ∑ _k ∈ S,
        (2 * δ⁻¹ ^ r * ∑ j, ‖(cyclicDifference^[r] f) j‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum hb
    _ ≤ (q : ℝ)⁻¹ * ∑ _k : ZMod q,
        (2 * δ⁻¹ ^ r * ∑ j, ‖(cyclicDifference^[r] f) j‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_univ_sum_of_nonneg (fun _ ↦ by positivity)
    _ = _ := by simp [NeZero.ne q]

end
end RiemannGaussian
