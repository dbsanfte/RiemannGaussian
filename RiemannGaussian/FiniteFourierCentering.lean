/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteFourierDifferenceDecay
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Centered finite Fourier interactions

A kernel with zero physical sample annihilates a constant Fourier
coefficient exactly. Subtracting the arithmetic Fourier value at zero
therefore preserves the full signed pairing. A partial frequency region
retains an explicit correction, controlled through its complement.
Fractional moments give a quantitative modulus for the centered factor.
-/

open Complex
open scoped Classical

namespace RiemannGaussian

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The unit atom at the zero sample, whose Fourier transform is constant. -/
def cyclicZeroAtom (j : ZMod q) : ℂ := if j = 0 then 1 else 0

/-- The zero atom has constant Fourier transform, at every frequency. -/
theorem dft_cyclicZeroAtom (k : ZMod q) :
    ZMod.dft (cyclicZeroAtom : ZMod q → ℂ) k = 1 := by
  simp [ZMod.dft_apply, cyclicZeroAtom]

/-- The zero atom has unit absolute mass. -/
theorem sum_norm_cyclicZeroAtom : (∑ j : ZMod q, ‖cyclicZeroAtom j‖) = 1 := by
  simp [cyclicZeroAtom, apply_ite norm]

/-- The arithmetic Fourier increment stays inside each complex product. -/
def centeredFourierPart (a f : ZMod q → ℂ) (S : Finset (ZMod q)) : ℂ :=
  (q : ℂ)⁻¹ * ∑ k ∈ S, (ZMod.dft a (-k) - ZMod.dft a 0) * ZMod.dft f k

/-- Centering on a partial region keeps its exact, generally nonzero correction. -/
theorem centeredFourierPart_eq_sub (a f : ZMod q → ℂ) (S : Finset (ZMod q)) :
    centeredFourierPart a f S = finiteFourierPart a f S -
      ZMod.dft a 0 * finiteFourierPart cyclicZeroAtom f S := by
  simp only [centeredFourierPart, finiteFourierPart, dft_cyclicZeroAtom, one_mul,
    sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- A zero physical sample makes the constant Fourier interaction on a
region exactly the negative of its interaction on the complement. -/
theorem finiteFourierPart_zeroAtom_add_compl (f : ZMod q → ℂ)
    (S : Finset (ZMod q)) (h0 : f 0 = 0) :
    finiteFourierPart cyclicZeroAtom f S + finiteFourierPart cyclicZeroAtom f Sᶜ = 0 := by
  rw [← sum_mul_eq_fourierPart_add_compl]
  simp [cyclicZeroAtom, h0]

/-- The full original pairing is preserved by centering, including its sign. -/
theorem sum_mul_eq_centeredFourierPart_add_compl (a f : ZMod q → ℂ)
    (S : Finset (ZMod q)) (h0 : f 0 = 0) :
    (∑ j, a j * f j) = centeredFourierPart a f S + centeredFourierPart a f Sᶜ := by
  rw [centeredFourierPart_eq_sub, centeredFourierPart_eq_sub,
    sum_mul_eq_fourierPart_add_compl a f S]
  have h := finiteFourierPart_zeroAtom_add_compl f S h0
  linear_combination ZMod.dft a 0 * h

/-- The centered interaction at the central frequency is exactly zero. -/
theorem centeredFourierPart_zero (a f : ZMod q → ℂ) :
    centeredFourierPart a f {0} = 0 := by
  simp [centeredFourierPart]

/-- Removing the central frequency leaves every centered interaction
unchanged; it contributes exactly zero before any estimate. -/
theorem centeredFourierPart_erase_zero (a f : ZMod q → ℂ) (S : Finset (ZMod q)) :
    centeredFourierPart a f (S.erase 0) = centeredFourierPart a f S := by
  unfold centeredFourierPart
  rw [Finset.sum_erase S (by simp)]

/-- The entire correction from centering a region is paid for on its
complement. No estimate of the kernel within the region is required. -/
theorem norm_centeredFourierPart_sub_le_difference (a f : ZMod q → ℂ)
    (S : Finset (ZMod q)) (h0 : f 0 = 0) (r : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hS : ∀ k ∈ Sᶜ, δ ≤ ‖cyclicDifferenceSymbol k‖) :
    ‖centeredFourierPart a f S - finiteFourierPart a f S‖ ≤
      ‖ZMod.dft a 0‖ * (δ⁻¹ ^ r * ∑ j, ‖(cyclicDifference^[r] f) j‖) := by
  have he : centeredFourierPart a f S - finiteFourierPart a f S =
      ZMod.dft a 0 * finiteFourierPart cyclicZeroAtom f Sᶜ := by
    rw [centeredFourierPart_eq_sub]
    have h := finiteFourierPart_zeroAtom_add_compl f S h0
    linear_combination -ZMod.dft a 0 * h
  rw [he, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa only [sum_norm_cyclicZeroAtom, mul_one] using
    norm_finiteFourierPart_le_sum_norm_difference cyclicZeroAtom f Sᶜ r hδ hS

private theorem norm_pow_sub_one_le {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) :
    ‖z ^ n - 1‖ ≤ (n : ℝ) * ‖z - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : z ^ (n + 1) - 1 = z * (z ^ n - 1) + (z - 1) := by ring
    rw [he]
    calc
      _ ≤ ‖z * (z ^ n - 1)‖ + ‖z - 1‖ := norm_add_le _ _
      _ ≤ (n : ℝ) * ‖z - 1‖ + ‖z - 1‖ := by rw [norm_mul, hz, one_mul]; gcongr
      _ = _ := by push_cast; ring

/-- Fractional interpolation retains the small phase gain without paying
for a full first moment. Both endpoints of the exponent interval are valid. -/
theorem norm_unit_pow_sub_one_le_rpow {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    ‖z ^ n - 1‖ ≤ 2 * ((n : ℝ) * ‖z - 1‖) ^ τ := by
  let x : ℝ := (n : ℝ) * ‖z - 1‖
  have hx0 : 0 ≤ x := by positivity
  by_cases hx : x ≤ 1
  · have hr : x ≤ x ^ τ := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge' hx0 hx hτ0 hτ1
    have hn := (norm_pow_sub_one_le hz n).trans hr
    change ‖z ^ n - 1‖ ≤ 2 * x ^ τ
    linarith [Real.rpow_nonneg hx0 τ]
  · have hr : 1 ≤ x ^ τ := by
      simpa only [Real.rpow_zero] using
        Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx) hτ0
    have hn : ‖z ^ n - 1‖ ≤ 2 := by
      simpa only [norm_pow, hz, one_pow, norm_one, one_add_one_eq_two] using norm_sub_le (z ^ n) 1
    change ‖z ^ n - 1‖ ≤ 2 * x ^ τ
    linarith

/-- The arithmetic Fourier increment is the original signed sum with its
exact phase difference at every sample. -/
theorem dft_sub_zero_eq (a : ZMod q → ℂ) (k : ZMod q) :
    ZMod.dft a (-k) - ZMod.dft a 0 =
      ∑ j, a j * (ZMod.stdAddChar k ^ j.val - 1) := by
  simp only [ZMod.dft_apply, smul_eq_mul, mul_neg, neg_neg,
    mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have he : ZMod.stdAddChar (j * k) = ZMod.stdAddChar k ^ j.val := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val]
  rw [he]
  ring

/-- A finite fractional physical moment controls the centered Fourier
factor uniformly, including at the central frequency and cyclic wraparound. -/
theorem norm_dft_sub_zero_le_fractional_moment (a : ZMod q → ℂ) (k : ZMod q)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    ‖ZMod.dft a (-k) - ZMod.dft a 0‖ ≤
      2 * ‖cyclicDifferenceSymbol k‖ ^ τ * ∑ j, ‖a j‖ * (j.val : ℝ) ^ τ := by
  rw [dft_sub_zero_eq]
  apply (norm_sum_le _ _).trans
  have hz : ‖ZMod.stdAddChar k‖ = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  calc
    _ ≤ ∑ j : ZMod q, ‖a j‖ * (2 * ((j.val : ℝ) * ‖ZMod.stdAddChar k - 1‖) ^ τ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_unit_pow_sub_one_le_rpow hz j.val hτ0 hτ1)
        (norm_nonneg _)
    _ = _ := by
      simp only [Real.mul_rpow (Nat.cast_nonneg _) (norm_nonneg _), cyclicDifferenceSymbol,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The exact centered pairing has a fractional phase weight in its
kernel budget. This estimate follows from the actual finite physical moment. -/
theorem norm_centeredFourierPart_le_fractional_moment (a f : ZMod q → ℂ)
    (S : Finset (ZMod q)) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    ‖centeredFourierPart a f S‖ ≤
      (q : ℝ)⁻¹ * (2 * ∑ j, ‖a j‖ * (j.val : ℝ) ^ τ) *
        ∑ k ∈ S, ‖cyclicDifferenceSymbol k‖ ^ τ * ‖ZMod.dft f k‖ := by
  rw [centeredFourierPart, norm_mul, norm_inv, Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans
  calc
    _ ≤ (q : ℝ)⁻¹ * ∑ k ∈ S,
        (2 * ‖cyclicDifferenceSymbol k‖ ^ τ * ∑ j, ‖a j‖ * (j.val : ℝ) ^ τ) *
          ‖ZMod.dft f k‖ := by
      gcongr with k hk
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_dft_sub_zero_le_fractional_moment a k hτ0 hτ1)
        (norm_nonneg _)
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      ring

end
end RiemannGaussian
