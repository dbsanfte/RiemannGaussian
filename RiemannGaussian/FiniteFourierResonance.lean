/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite Fourier interactions and their exact difference equation

The finite Fourier pairing retains every complex interaction. A cyclic
difference supplies its exact frequency multiplier; inversion is used only
away from the central mode. These finite identities require no infinite
Poisson interchange or convergence premise.
-/

open Complex
open scoped Classical

namespace RiemannGaussian

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The forward cyclic difference, including the wraparound boundary. -/
def cyclicDifference (f : ZMod q → ℂ) (j : ZMod q) : ℂ := f (j + 1) - f j

/-- The exact Fourier multiplier of the forward cyclic difference. -/
def cyclicDifferenceSymbol (k : ZMod q) : ℂ := ZMod.stdAddChar k - 1

/-- Translation retains its complex Fourier phase. -/
theorem dft_cyclicShift (f : ZMod q → ℂ) (k : ZMod q) :
    ZMod.dft (fun j ↦ f (j + 1)) k = ZMod.stdAddChar k * ZMod.dft f k := by
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.mul_sum]
  apply Fintype.sum_equiv (Equiv.addRight (1 : ZMod q))
  intro j
  simp only [Equiv.coe_addRight]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

/-- The full complex difference equation before division by its symbol. -/
theorem dft_cyclicDifference (f : ZMod q → ℂ) (k : ZMod q) :
    ZMod.dft (cyclicDifference f) k = cyclicDifferenceSymbol k * ZMod.dft f k := by
  change ZMod.dft ((fun j ↦ f (j + 1)) - f) k = _
  rw [map_sub]
  simp only [Pi.sub_apply, dft_cyclicShift, cyclicDifferenceSymbol]
  ring

/-- Any number of cyclic differences retains the exact multiplier. -/
theorem dft_iterate_cyclicDifference (r : ℕ) (f : ZMod q → ℂ) (k : ZMod q) :
    ZMod.dft (cyclicDifference^[r] f) k = cyclicDifferenceSymbol k ^ r * ZMod.dft f k := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', dft_cyclicDifference, ih, pow_succ]
    ring

/-- Exactly the central mode has zero difference multiplier. -/
theorem cyclicDifferenceSymbol_eq_zero_iff (k : ZMod q) :
    cyclicDifferenceSymbol k = 0 ↔ k = 0 := by
  rw [cyclicDifferenceSymbol, sub_eq_zero,
    ← (ZMod.stdAddChar (N := q)).map_zero_eq_one, ZMod.injective_stdAddChar.eq_iff]

/-- Fourier inversion of a difference is valid at every noncentral mode. -/
theorem dft_eq_difference_quotient (r : ℕ) (f : ZMod q → ℂ) {k : ZMod q}
    (hk : k ≠ 0) :
    ZMod.dft f k = ZMod.dft (cyclicDifference^[r] f) k / cyclicDifferenceSymbol k ^ r := by
  rw [dft_iterate_cyclicDifference]
  exact (mul_div_cancel_left₀ _ (pow_ne_zero _
    (fun h ↦ hk ((cyclicDifferenceSymbol_eq_zero_iff k).mp h)))).symm

/-- The complete bilinear Fourier pairing, with no conjugation or sign lost. -/
theorem sum_mul_eq_dft_pair (a f : ZMod q → ℂ) :
    (∑ j, a j * f j) = (q : ℂ)⁻¹ * ∑ k, ZMod.dft a (-k) * ZMod.dft f k := by
  have hinv (j : ZMod q) : f j = (q : ℂ)⁻¹ *
      ∑ k, ZMod.stdAddChar (k * j) * ZMod.dft f k := by
    have h := congrFun (ZMod.dft.symm_apply_apply f) j
    simpa only [ZMod.invDFT_apply, smul_eq_mul] using h.symm
  calc
    _ = ∑ j, a j * ((q : ℂ)⁻¹ * ∑ k, ZMod.stdAddChar (k * j) * ZMod.dft f k) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← hinv]
    _ = (q : ℂ)⁻¹ * ∑ k, (∑ j, ZMod.stdAddChar (k * j) * a j) * ZMod.dft f k := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp only [ZMod.dft_apply, smul_eq_mul, mul_neg, neg_neg, mul_comm]

/-- The signed interaction in a specified frequency region. -/
def finiteFourierPart (a f : ZMod q → ℂ) (S : Finset (ZMod q)) : ℂ :=
  (q : ℂ)⁻¹ * ∑ k ∈ S, ZMod.dft a (-k) * ZMod.dft f k

/-- Every frequency partition preserves the original complex sum exactly. -/
theorem sum_mul_eq_fourierPart_add_compl (a f : ZMod q → ℂ) (S : Finset (ZMod q)) :
    (∑ j, a j * f j) = finiteFourierPart a f S + finiteFourierPart a f Sᶜ := by
  rw [sum_mul_eq_dft_pair, finiteFourierPart, finiteFourierPart, ← mul_add,
    Finset.sum_add_sum_compl]

/-- The central contribution retains both exact discrete means. -/
theorem finiteFourierPart_zero (a f : ZMod q → ℂ) :
    finiteFourierPart a f {0} = (q : ℂ)⁻¹ * (∑ j, a j) * (∑ j, f j) := by
  simp [finiteFourierPart, ZMod.dft_apply_zero, mul_assoc]

/-- A noncentral region has an exact normal form at every difference order.
The arithmetic Fourier coefficient is kept inside the same signed sum. -/
theorem finiteFourierPart_eq_difference (a f : ZMod q → ℂ) (S : Finset (ZMod q))
    (hS : 0 ∉ S) (r : ℕ) :
    finiteFourierPart a f S = (q : ℂ)⁻¹ * ∑ k ∈ S,
      ZMod.dft a (-k) * (ZMod.dft (cyclicDifference^[r] f) k / cyclicDifferenceSymbol k ^ r) := by
  unfold finiteFourierPart
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [← dft_eq_difference_quotient r f (fun h ↦ hS (h ▸ hk))]

private theorem norm_sum_mul_sq_le {ι : Type*} (S : Finset ι) (a b : ι → ℂ) :
    ‖∑ k ∈ S, a k * b k‖ ^ 2 ≤ (∑ k ∈ S, ‖a k‖ ^ 2) * ∑ k ∈ S, ‖b k‖ ^ 2 := by
  have hn : ‖∑ k ∈ S, a k * b k‖ ≤ ∑ k ∈ S, ‖a k‖ * ‖b k‖ := by
    simpa only [norm_mul] using norm_sum_le S (fun k ↦ a k * b k)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq S (fun k ↦ ‖a k‖) (fun k ↦ ‖b k‖))

/-- A frequency region is bounded by its two full Fourier energies. -/
theorem norm_finiteFourierPart_sq_le (a f : ZMod q → ℂ) (S : Finset (ZMod q)) :
    ‖finiteFourierPart a f S‖ ^ 2 ≤ (q : ℝ)⁻¹ ^ 2 *
      ((∑ k ∈ S, ‖ZMod.dft a (-k)‖ ^ 2) * ∑ k ∈ S, ‖ZMod.dft f k‖ ^ 2) := by
  rw [finiteFourierPart, norm_mul, mul_pow, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_sum_mul_sq_le S _ _) (sq_nonneg _)

/-- On a region with a positive symbol gap, the smooth factor is
controlled by its exact cyclic differences at any order. -/
theorem norm_dft_le_difference_of_gap (r : ℕ) (f : ZMod q → ℂ) (k : ZMod q)
    {δ : ℝ} (hδ : 0 < δ) (hk : δ ≤ ‖cyclicDifferenceSymbol k‖) :
    ‖ZMod.dft f k‖ ≤ δ⁻¹ ^ r * ‖ZMod.dft (cyclicDifference^[r] f) k‖ := by
  have hpow := pow_le_pow_left₀ hδ.le hk r
  have he : ‖ZMod.dft (cyclicDifference^[r] f) k‖ =
      ‖cyclicDifferenceSymbol k‖ ^ r * ‖ZMod.dft f k‖ := by
    rw [dft_iterate_cyclicDifference, norm_mul, norm_pow]
  have hm := mul_le_mul_of_nonneg_right hpow (norm_nonneg (ZMod.dft f k))
  rw [← he] at hm
  have hd : 0 < δ ^ r := pow_pos hδ _
  calc
    _ ≤ ‖ZMod.dft (cyclicDifference^[r] f) k‖ / δ ^ r := (le_div_iff₀ hd).mpr (by
      simpa only [mul_comm] using hm)
    _ = _ := by rw [div_eq_mul_inv, inv_pow]; ring

/-- The nonresonant interaction has a quantitative energy bound with
the exact difference cost and no separate estimates on divisor terms. -/
theorem norm_finiteFourierPart_sq_le_difference (a f : ZMod q → ℂ)
    (S : Finset (ZMod q)) (r : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hS : ∀ k ∈ S, δ ≤ ‖cyclicDifferenceSymbol k‖) :
    ‖finiteFourierPart a f S‖ ^ 2 ≤ (q : ℝ)⁻¹ ^ 2 *
      ((∑ k ∈ S, ‖ZMod.dft a (-k)‖ ^ 2) *
        (δ⁻¹ ^ r) ^ 2 * ∑ k ∈ S, ‖ZMod.dft (cyclicDifference^[r] f) k‖ ^ 2) := by
  have he : (∑ k ∈ S, ‖ZMod.dft f k‖ ^ 2) ≤
      (δ⁻¹ ^ r) ^ 2 * ∑ k ∈ S, ‖ZMod.dft (cyclicDifference^[r] f) k‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
      (norm_dft_le_difference_of_gap r f k hδ (hS k hk)) 2
  apply (norm_finiteFourierPart_sq_le a f S).trans
  have h := mul_le_mul_of_nonneg_left he
    (Finset.sum_nonneg (s := S) (fun k _ ↦ sq_nonneg ‖ZMod.dft a (-k)‖))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (sq_nonneg ((q : ℝ)⁻¹))

private theorem conj_stdAddChar (k : ZMod q) :
    starRingEnd ℂ (ZMod.stdAddChar k) = ZMod.stdAddChar (-k) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv,
    Circle.coe_inv_eq_conj]

/-- Conjugation reverses the Fourier frequency exactly. -/
theorem dft_conj (f : ZMod q → ℂ) (k : ZMod q) :
    ZMod.dft (fun j ↦ starRingEnd ℂ (f j)) k = starRingEnd ℂ (ZMod.dft f (-k)) := by
  simp only [ZMod.dft_apply, smul_eq_mul, map_sum, map_mul, conj_stdAddChar,
    mul_neg, neg_neg]

/-- Parseval with the counting-measure normalization made explicit. -/
theorem sum_norm_dft_sq (f : ZMod q → ℂ) :
    (∑ k, ‖ZMod.dft f k‖ ^ 2) = (q : ℝ) * ∑ j, ‖f j‖ ^ 2 := by
  have h := congrArg Complex.re (sum_mul_eq_dft_pair (fun j ↦ starRingEnd ℂ (f j)) f)
  simp only [dft_conj, neg_neg, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq, ← Complex.ofReal_sum] at h
  have hq : (q : ℂ)⁻¹ = ((q : ℝ)⁻¹ : ℝ) := by simp
  rw [hq, ← Complex.ofReal_mul] at h
  simp only [Complex.ofReal_re] at h
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  calc
    _ = (q : ℝ) * ((q : ℝ)⁻¹ * ∑ k, ‖ZMod.dft f k‖ ^ 2) := by
      rw [← mul_assoc, mul_inv_cancel₀ hq0, one_mul]
    _ = _ := by rw [← h]

/-- The spectral gap is exactly a trigonometric phase separation. -/
theorem norm_cyclicDifferenceSymbol_sq (k : ZMod q) :
    ‖cyclicDifferenceSymbol k‖ ^ 2 =
      2 - 2 * Real.cos (2 * Real.pi * (k.val : ℝ) / q) := by
  have hn : Complex.normSq (ZMod.stdAddChar k) = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.normSq_coe _
  have hr : (ZMod.stdAddChar k).re = Real.cos (2 * Real.pi * (k.val : ℝ) / q) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp, Circle.coe_exp, Complex.exp_re]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, sub_self, Real.exp_zero, Complex.mul_im,
      mul_one, one_mul]
    congr 1
    ring
  rw [cyclicDifferenceSymbol, Complex.sq_norm, Complex.normSq_sub, hn]
  simp only [map_one, mul_one, hr]
  ring

/-- The cyclic derivative energy includes its exact endpoint jump. -/
theorem sum_cyclicDifference_sq_eq_boundary (M : ℕ) (f : ZMod (M + 1) → ℂ) :
    (∑ j, ‖cyclicDifference f j‖ ^ 2) =
      (∑ n ∈ Finset.range M, ‖f ((n + 1 : ℕ) : ZMod (M + 1)) - f n‖ ^ 2) +
        ‖f 0 - f M‖ ^ 2 := by
  have he (j : ZMod (M + 1)) : ‖cyclicDifference f j‖ ^ 2 =
      ‖f ((j.val + 1 : ℕ) : ZMod (M + 1)) - f j.val‖ ^ 2 := by
    simp [cyclicDifference, Nat.cast_add]
  simp_rw [he]
  change (∑ j : Fin (M + 1),
    ‖f ((j.val + 1 : ℕ) : ZMod (M + 1)) - f j.val‖ ^ 2) = _
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ ↦
    ‖f ((n + 1 : ℕ) : ZMod (M + 1)) - f n‖ ^ 2), Finset.sum_range_succ]
  simp

/-- A genuine symbol gap controls the entire complementary interaction
by physical-space energies, including all cyclic boundary differences. -/
theorem norm_finiteFourierPart_sq_le_physical_difference (a f : ZMod q → ℂ)
    (S : Finset (ZMod q)) (r : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hS : ∀ k ∈ S, δ ≤ ‖cyclicDifferenceSymbol k‖) :
    ‖finiteFourierPart a f S‖ ^ 2 ≤ (δ⁻¹ ^ r) ^ 2 *
      (∑ j, ‖a j‖ ^ 2) * ∑ j, ‖(cyclicDifference^[r] f) j‖ ^ 2 := by
  have ha : (∑ k ∈ S, ‖ZMod.dft a (-k)‖ ^ 2) ≤ (q : ℝ) * ∑ j, ‖a j‖ ^ 2 := by
    calc
      _ ≤ ∑ k : ZMod q, ‖ZMod.dft a (-k)‖ ^ 2 :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ ↦ sq_nonneg _)
      _ = ∑ k : ZMod q, ‖ZMod.dft a k‖ ^ 2 := by
        exact Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ ↦ rfl)
      _ = _ := sum_norm_dft_sq a
  have hf : (∑ k ∈ S, ‖ZMod.dft (cyclicDifference^[r] f) k‖ ^ 2) ≤
      (q : ℝ) * ∑ j, ‖(cyclicDifference^[r] f) j‖ ^ 2 := by
    calc
      _ ≤ ∑ k, ‖ZMod.dft (cyclicDifference^[r] f) k‖ ^ 2 :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ ↦ sq_nonneg _)
      _ = _ := sum_norm_dft_sq _
  apply (norm_finiteFourierPart_sq_le_difference a f S r hδ hS).trans
  calc
    _ ≤ (q : ℝ)⁻¹ ^ 2 * (((q : ℝ) * ∑ j, ‖a j‖ ^ 2) *
        (δ⁻¹ ^ r) ^ 2 * ((q : ℝ) * ∑ j, ‖(cyclicDifference^[r] f) j‖ ^ 2)) := by
      gcongr
    _ = _ := by
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
      field_simp

end
end RiemannGaussian
