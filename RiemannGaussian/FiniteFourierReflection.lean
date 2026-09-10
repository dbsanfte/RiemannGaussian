/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteFourierCentering

/-!
# Opposite-frequency and physical-reflection cancellation

On a frequency region closed under negation, the Fourier projection kernel
is real and even. The real part of the centered interaction of real
arithmetic coefficients therefore annihilates the imaginary physical
kernel exactly. Its remaining physical kernel is odd under reflection
about half the arithmetic index, so only the corresponding signed
reflection difference of the real physical data contributes.
-/

open Complex
open scoped Classical

namespace RiemannGaussian

noncomputable section

variable {q : ℕ} [NeZero q]

private theorem character_conj (k : ZMod q) :
    starRingEnd ℂ (ZMod.stdAddChar k) = ZMod.stdAddChar (-k) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv,
    Circle.coe_inv_eq_conj]

omit [NeZero q] in
private theorem sum_neg_closed {E : Type*} [AddCommMonoid E]
    (S : Finset (ZMod q)) (hS : ∀ k ∈ S, -k ∈ S) (g : ZMod q → E) :
    (∑ k ∈ S, g (-k)) = ∑ k ∈ S, g k := by
  apply Finset.sum_bij (fun k _ ↦ -k)
  · exact hS
  · intro a _ b _ h
    exact neg_injective h
  · intro k hk
    exact ⟨-k, hS k hk, neg_neg k⟩
  · intro k _
    rfl

/-- The original cyclic difference gap is unchanged by reversing frequency. -/
theorem norm_cyclicDifferenceSymbol_neg (k : ZMod q) :
    ‖cyclicDifferenceSymbol (-k)‖ = ‖cyclicDifferenceSymbol k‖ := by
  have he : cyclicDifferenceSymbol (-k) = starRingEnd ℂ (cyclicDifferenceSymbol k) := by
    simp only [cyclicDifferenceSymbol, map_sub, map_one, character_conj]
  rw [he, Complex.norm_conj]

/-- The complete projection kernel of a finite region, with its original
Fourier normalization. No absolute values of characters are taken. -/
def cyclicFourierKernel (S : Finset (ZMod q)) (j : ZMod q) : ℂ :=
  (q : ℂ)⁻¹ * ∑ k ∈ S, ZMod.stdAddChar (k * j)

/-- Opposite frequencies make the physical projection kernel even. -/
theorem cyclicFourierKernel_neg (S : Finset (ZMod q))
    (hS : ∀ k ∈ S, -k ∈ S) (j : ZMod q) :
    cyclicFourierKernel S (-j) = cyclicFourierKernel S j := by
  unfold cyclicFourierKernel
  congr 1
  simpa only [mul_neg, neg_mul] using
    sum_neg_closed S hS (fun k ↦ ZMod.stdAddChar (k * j))

/-- Character conjugation reverses the physical kernel argument exactly. -/
theorem conj_cyclicFourierKernel (S : Finset (ZMod q)) (j : ZMod q) :
    starRingEnd ℂ (cyclicFourierKernel S j) = cyclicFourierKernel S (-j) := by
  simp only [cyclicFourierKernel, map_mul, map_inv₀, map_natCast, map_sum,
    character_conj, mul_neg]

/-- On a symmetric frequency region the imaginary projection kernel
cancels exactly, including the central and self-opposite modes. -/
theorem cyclicFourierKernel_im (S : Finset (ZMod q))
    (hS : ∀ k ∈ S, -k ∈ S) (j : ZMod q) :
    (cyclicFourierKernel S j).im = 0 := by
  have h := congrArg Complex.im ((conj_cyclicFourierKernel S j).trans
    (cyclicFourierKernel_neg S hS j))
  simp only [Complex.conj_im] at h
  linarith

/-- Exact physical reconstruction of the centered Fourier interaction.
The two kernel translates retain their relative sign at every sample. -/
theorem centeredFourierPart_eq_kernel (a f : ZMod q → ℂ) (S : Finset (ZMod q)) :
    centeredFourierPart a f S = ∑ n, a n * ∑ m,
      (cyclicFourierKernel S (n - m) - cyclicFourierKernel S (-m)) * f m := by
  have he (n m : ZMod q) :
      cyclicFourierKernel S (n - m) - cyclicFourierKernel S (-m) =
        (q : ℂ)⁻¹ * ∑ k ∈ S,
          (ZMod.stdAddChar k ^ n.val - 1) * ZMod.stdAddChar (-(m * k)) := by
    unfold cyclicFourierKernel
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    have hn : ZMod.stdAddChar k ^ n.val = ZMod.stdAddChar (k * n) := by
      rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]
    rw [hn, show k * (n - m) = k * n + -(m * k) by ring,
      show k * (-m) = -(m * k) by ring, AddChar.map_add_eq_mul]
    ring
  simp_rw [he]
  unfold centeredFourierPart
  simp_rw [dft_sub_zero_eq]
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The real centered projection kernel keeps the exact difference of
its two physical translates. -/
def cyclicCenteredRealKernel (S : Finset (ZMod q)) (n m : ZMod q) : ℝ :=
  (cyclicFourierKernel S (n - m)).re - (cyclicFourierKernel S m).re

/-- For real arithmetic coefficients, opposite-frequency pairing
eliminates the imaginary physical kernel from the required real part. -/
theorem centeredFourierPart_re_eq_kernel (a f : ZMod q → ℂ)
    (ha : ∀ n, (a n).im = 0) (S : Finset (ZMod q)) (hS : ∀ k ∈ S, -k ∈ S) :
    (centeredFourierPart a f S).re = ∑ n, (a n).re *
      ∑ m, cyclicCenteredRealKernel S n m * (f m).re := by
  rw [centeredFourierPart_eq_kernel]
  simp only [Complex.re_sum, Complex.mul_re, ha, zero_mul, sub_zero,
    Complex.sub_re, Complex.sub_im, cyclicFourierKernel_im S hS, sub_self,
    cyclicFourierKernel_neg S hS, cyclicCenteredRealKernel]

/-- An arbitrary imaginary physical perturbation contributes exactly
zero to the relevant real interaction on every symmetric region. -/
theorem centeredFourierPart_re_imaginary_eq_zero (a : ZMod q → ℂ)
    (ha : ∀ n, (a n).im = 0) (g : ZMod q → ℝ)
    (S : Finset (ZMod q)) (hS : ∀ k ∈ S, -k ∈ S) :
    (centeredFourierPart a (fun m ↦ I * (g m : ℂ)) S).re = 0 := by
  rw [centeredFourierPart_re_eq_kernel a _ ha S hS]
  simp

/-- The exact real target can be computed with the real physical
kernel while preserving all of its sine Fourier components. -/
theorem centeredFourierPart_re_eq_real_physical (a f : ZMod q → ℂ)
    (ha : ∀ n, (a n).im = 0) (S : Finset (ZMod q)) (hS : ∀ k ∈ S, -k ∈ S) :
    (centeredFourierPart a f S).re =
      (centeredFourierPart a (fun m ↦ ((f m).re : ℂ)) S).re := by
  rw [centeredFourierPart_re_eq_kernel a f ha S hS,
    centeredFourierPart_re_eq_kernel a _ ha S hS]
  rfl

/-- The centered real projection kernel reverses sign under reflection
about half the arithmetic index. This retains the cyclic wraparound exactly. -/
theorem cyclicCenteredRealKernel_reflect (S : Finset (ZMod q)) (n m : ZMod q) :
    cyclicCenteredRealKernel S n (n - m) = -cyclicCenteredRealKernel S n m := by
  unfold cyclicCenteredRealKernel
  rw [sub_sub_cancel]
  ring

/-- The exact midpoint contribution vanishes whenever it is present;
no division by two in the cyclic group is used. -/
theorem cyclicCenteredRealKernel_midpoint (S : Finset (ZMod q)) {n m : ZMod q}
    (hm : m + m = n) : cyclicCenteredRealKernel S n m = 0 := by
  subst n
  simp [cyclicCenteredRealKernel]

/-- Pairing physical reflection partners keeps only the signed odd
part of the real kernel. The even part cancels before any estimate. -/
theorem sum_cyclicCenteredRealKernel_mul_eq_reflection (S : Finset (ZMod q))
    (n : ZMod q) (g : ZMod q → ℝ) :
    (∑ m, cyclicCenteredRealKernel S n m * g m) =
      (1 / 2 : ℝ) * ∑ m, cyclicCenteredRealKernel S n m * (g m - g (n - m)) := by
  have he : (∑ m, cyclicCenteredRealKernel S n m * g (n - m)) =
      -(∑ m, cyclicCenteredRealKernel S n m * g m) := by
    calc
      _ = ∑ m, cyclicCenteredRealKernel S n (n - m) * g (n - (n - m)) := by
        apply Fintype.sum_bijective (fun m : ZMod q ↦ n - m)
          (Function.Involutive.bijective (by intro m; simp))
        intro m
        simp only [sub_sub_cancel]
      _ = _ := by simp only [cyclicCenteredRealKernel_reflect, sub_sub_cancel, neg_mul, Finset.sum_neg_distrib]
  simp only [mul_sub, Finset.sum_sub_distrib, he]
  ring

/-- Every reflection-even physical profile is annihilated exactly by
the centered real kernel, for every arithmetic row and finite region. -/
theorem sum_cyclicCenteredRealKernel_mul_even_eq_zero (S : Finset (ZMod q))
    (n : ZMod q) (g : ZMod q → ℝ) (hg : ∀ m, g (n - m) = g m) :
    (∑ m, cyclicCenteredRealKernel S n m * g m) = 0 := by
  rw [sum_cyclicCenteredRealKernel_mul_eq_reflection]
  simp [hg]

/-- The canonical reflection-even component is annihilated for every
profile, without requiring the profile itself to have a symmetry. -/
theorem sum_cyclicCenteredRealKernel_mul_even_part_eq_zero (S : Finset (ZMod q))
    (n : ZMod q) (g : ZMod q → ℝ) :
    (∑ m, cyclicCenteredRealKernel S n m * ((g m + g (n - m)) / 2)) = 0 := by
  apply sum_cyclicCenteredRealKernel_mul_even_eq_zero S n
    (fun m ↦ (g m + g (n - m)) / 2)
  intro m
  rw [sub_sub_cancel]
  ring

/-- The complete real pairing uses only the odd reflection of the
real physical kernel, with the original signed arithmetic coefficients
still outside the exact inner interaction. -/
theorem centeredFourierPart_re_eq_reflection (a f : ZMod q → ℂ)
    (ha : ∀ n, (a n).im = 0) (S : Finset (ZMod q)) (hS : ∀ k ∈ S, -k ∈ S) :
    (centeredFourierPart a f S).re = (1 / 2 : ℝ) * ∑ n, (a n).re *
      ∑ m, cyclicCenteredRealKernel S n m * ((f m).re - (f (n - m)).re) := by
  rw [centeredFourierPart_re_eq_kernel a f ha S hS]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [sum_cyclicCenteredRealKernel_mul_eq_reflection S n (fun m ↦ (f m).re)]
  ring

end
end RiemannGaussian
