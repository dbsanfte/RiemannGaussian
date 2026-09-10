/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteFourierReflection
import RiemannGaussian.FiniteFourierFractionalBudget
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.PSeries

/-!
# Averaging the inverse difference symbol over the actual cyclic spectrum

The spectrum has a controlled density near its central mode. Pairing
opposite frequencies and summing the complete inverse-square tail gives
an inverse-gap cost, improving the inverse-square worst-mode estimate.
Every finite cyclic group, including the trivial group, is covered.
-/

open Complex
open scoped Classical

namespace RiemannGaussian
noncomputable section

variable {q : ℕ} [NeZero q]

/-- The difference symbol has a linear lower bound in its positive
half-cycle index, from the chord inequality for the sine function. -/
theorem four_mul_val_div_le_norm_cyclicDifferenceSymbol (k : ZMod q)
    (hk : 2 * k.val ≤ q) :
    4 * (k.val : ℝ) / q ≤ ‖cyclicDifferenceSymbol k‖ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hkR : 2 * (k.val : ℝ) ≤ q := by exact_mod_cast hk
  let t : ℝ := Real.pi * k.val / q
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hq).mpr
    nlinarith [Real.pi_pos]
  have hc : ZMod.stdAddChar k = Complex.exp (I * ((2 * t : ℝ) : ℂ)) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp, Circle.coe_exp]
    congr 1
    dsimp [t]
    push_cast
    ring
  rw [cyclicDifferenceSymbol, hc, Complex.norm_exp_I_mul_ofReal_sub_one,
    show 2 * t / 2 = t by ring, Real.norm_of_nonneg
      (mul_nonneg (by norm_num) (Real.sin_nonneg_of_mem_Icc ⟨ht0, by linarith⟩))]
  have hs := Real.mul_le_sin ht0 ht1
  have he : 2 / Real.pi * t = 2 * k.val / q := by
    dsimp [t]
    field_simp
  rw [he] at hs
  calc
    _ = 2 * (2 * (k.val : ℝ) / q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by norm_num)

private theorem sum_even_le_two_half (g : ZMod q → ℝ)
    (hg : ∀ k, 0 ≤ g k) (h0 : g 0 = 0) (he : ∀ k, g (-k) = g k) :
    (∑ k, g k) ≤ 2 * ∑ k ∈ (Finset.univ : Finset (ZMod q)).filter
      (fun k ↦ 0 < k.val ∧ 2 * k.val ≤ q), g k := by
  let B := (Finset.univ : Finset (ZMod q)).filter (fun k ↦ 0 < k.val ∧ 2 * k.val ≤ q)
  have hcover : Finset.univ.erase (0 : ZMod q) ⊆ B ∪ B.image Neg.neg := by
    intro k hk
    have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
    have hp : 0 < k.val := Nat.pos_of_ne_zero (fun h ↦ hk0 ((ZMod.val_eq_zero k).mp h))
    by_cases hh : 2 * k.val ≤ q
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp, hh⟩)
    · have : NeZero k := ⟨hk0⟩
      have hv := ZMod.val_lt k
      have hn : -k ∈ B := by
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, ZMod.val_neg_of_ne_zero]
        omega
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨-k, hn, neg_neg k⟩)
  have hsum : (∑ k, g k) = ∑ k ∈ Finset.univ.erase (0 : ZMod q), g k := by
    simpa only [h0, add_zero] using (Finset.sum_erase_add Finset.univ g (Finset.mem_univ 0)).symm
  have himage : (∑ k ∈ B.image Neg.neg, g k) = ∑ k ∈ B, g k := by
    rw [Finset.sum_image (by intro a _ b _ h; exact neg_injective h)]
    simp only [he]
  rw [hsum]
  calc
    _ ≤ ∑ k ∈ B ∪ B.image Neg.neg, g k :=
      Finset.sum_le_sum_of_subset_of_nonneg hcover (fun k _ _ ↦ hg k)
    _ ≤ (∑ k ∈ B, g k) + ∑ k ∈ B.image Neg.neg, g k := by
      have h : (∑ k ∈ B ∪ B.image Neg.neg, g k) + (∑ k ∈ B ∩ B.image Neg.neg, g k) =
          (∑ k ∈ B, g k) + ∑ k ∈ B.image Neg.neg, g k := Finset.sum_union_inter
      have hp : 0 ≤ ∑ k ∈ B ∩ B.image Neg.neg, g k := Finset.sum_nonneg (fun k _ ↦ hg k)
      linarith
    _ = _ := by rw [himage]; ring

private theorem sum_cutoff_envelope_le (q K : ℕ) (δ : ℝ) :
    (∑ n ∈ Finset.Icc 1 q,
      if n ≤ K then δ⁻¹ ^ 2 else ((q : ℝ) ^ 2 / 16) * ((n : ℝ) ^ 2)⁻¹) ≤
      K * δ⁻¹ ^ 2 + ((q : ℝ) ^ 2 / 16) * (2 / ((K : ℝ) + 1)) := by
  let S := Finset.Icc 1 q
  have he : (∑ n ∈ S, if n ≤ K then δ⁻¹ ^ 2 else
      ((q : ℝ) ^ 2 / 16) * ((n : ℝ) ^ 2)⁻¹) =
      (∑ _n ∈ S.filter (fun n ↦ n ≤ K), δ⁻¹ ^ 2) +
      ∑ n ∈ S.filter (fun n ↦ ¬n ≤ K), ((q : ℝ) ^ 2 / 16) * ((n : ℝ) ^ 2)⁻¹ := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n ≤ K <;> simp [hn]
  have hc : (S.filter (fun n ↦ n ≤ K)).card ≤ K := by
    have hs : S.filter (fun n ↦ n ≤ K) ⊆ Finset.Icc 1 K := by
      intro n hn
      obtain ⟨hnS, hnK⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hnS).1, hnK⟩
    simpa using Finset.card_le_card hs
  have ht : S.filter (fun n ↦ ¬n ≤ K) = Finset.Ioo K (q + 1) := by
    ext n
    simp only [S, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioo]
    omega
  rw [he, ht, ← Finset.mul_sum]
  apply add_le_add
  · simp only [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le K (q + 1)) (by positivity)

/-- The complete inverse-square symbol mass has an inverse-gap bound,
uniformly over the cyclic modulus and every selected gapped frequency set.
The central mode is excluded by the strictly positive gap hypothesis. -/
theorem sum_inv_sq_cyclicDifferenceSymbol_le {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (ZMod q)) (hS : ∀ k ∈ S, δ ≤ ‖cyclicDifferenceSymbol k‖) :
    (q : ℝ)⁻¹ * ∑ k ∈ S, ‖cyclicDifferenceSymbol k‖⁻¹ ^ 2 ≤ 2 / δ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  let K := ⌊(q : ℝ) * δ / 4⌋₊
  let g : ZMod q → ℝ := fun k ↦ min (δ⁻¹ ^ 2) (‖cyclicDifferenceSymbol k‖⁻¹ ^ 2)
  let B := (Finset.univ : Finset (ZMod q)).filter (fun k ↦ 0 < k.val ∧ 2 * k.val ≤ q)
  let f : ℕ → ℝ := fun n ↦ if n ≤ K then δ⁻¹ ^ 2 else
    ((q : ℝ) ^ 2 / 16) * ((n : ℝ) ^ 2)⁻¹
  have hg (k : ZMod q) : 0 ≤ g k := le_min (sq_nonneg _) (sq_nonneg _)
  have hsame (k : ZMod q) (hk : k ∈ S) : ‖cyclicDifferenceSymbol k‖⁻¹ ^ 2 = g k := by
    have hi : ‖cyclicDifferenceSymbol k‖⁻¹ ≤ δ⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hδ (hS k hk)
    exact (min_eq_right (pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) hi 2)).symm
  have hhalf : (∑ k, g k) ≤ 2 * ∑ k ∈ B, g k :=
    sum_even_le_two_half g hg (by simp [g, cyclicDifferenceSymbol, sq_nonneg])
      (fun k ↦ by simp only [g, norm_cyclicDifferenceSymbol_neg])
  have hpoint (k : ZMod q) (hk : k ∈ B) : g k ≤ f k.val := by
    obtain ⟨hk0, hkq⟩ := (Finset.mem_filter.mp hk).2
    have hkR : (0 : ℝ) < k.val := by exact_mod_cast hk0
    by_cases hl : k.val ≤ K
    · exact (min_le_left _ _).trans_eq (by simp [f, hl])
    · simp only [f, if_neg hl]
      apply (min_le_right _ _).trans
      have hi : ‖cyclicDifferenceSymbol k‖⁻¹ ≤ (4 * (k.val : ℝ) / q)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le (by positivity)
          (four_mul_val_div_le_norm_cyclicDifferenceSymbol k hkq)
      apply (pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) hi 2).trans_eq
      field_simp
      ring
  have hBsum : (∑ k ∈ B, g k) ≤ ∑ n ∈ Finset.Icc 1 q, f n := by
    calc
      _ ≤ ∑ k ∈ B, f k.val := Finset.sum_le_sum hpoint
      _ = ∑ n ∈ B.image ZMod.val, f n := by
        rw [Finset.sum_image (by intro a _ b _ h; exact ZMod.val_injective q h)]
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hk).2.1, (ZMod.val_lt k).le⟩
        · intro n _ _
          dsimp [f]
          split_ifs <;> positivity
  have hmass : (∑ k ∈ S, ‖cyclicDifferenceSymbol k‖⁻¹ ^ 2) ≤
      2 * ((K : ℝ) * δ⁻¹ ^ 2 + ((q : ℝ) ^ 2 / 16) * (2 / ((K : ℝ) + 1))) := by
    rw [Finset.sum_congr rfl hsame]
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun k _ _ ↦ hg k)).trans
    exact hhalf.trans ((mul_le_mul_of_nonneg_left hBsum (by norm_num)).trans
      (mul_le_mul_of_nonneg_left (sum_cutoff_envelope_le q K δ) (by norm_num)))
  have hKlo : (K : ℝ) ≤ (q : ℝ) * δ / 4 := Nat.floor_le (by positivity)
  have hKhi : (q : ℝ) * δ / 4 < (K : ℝ) + 1 := Nat.lt_floor_add_one _
  have hKpos : 0 < (K : ℝ) + 1 := by positivity
  have hlo : 2 * (K : ℝ) / ((q : ℝ) * δ ^ 2) ≤ 1 / (2 * δ) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hKlo hδ.le]
  have hhi : (q : ℝ) / (4 * ((K : ℝ) + 1)) ≤ 1 / δ := by
    apply (div_le_div_iff₀ (by positivity) hδ).mpr
    linarith
  apply (mul_le_mul_of_nonneg_left hmass (inv_nonneg.mpr hq.le)).trans
  calc
    _ = 2 * (K : ℝ) / ((q : ℝ) * δ ^ 2) + (q : ℝ) / (4 * ((K : ℝ) + 1)) := by
      field_simp
      ring
    _ ≤ 1 / (2 * δ) + 1 / δ := add_le_add hlo hhi
    _ = (3 / 2 : ℝ) * δ⁻¹ := by ring
    _ ≤ 2 * δ⁻¹ := mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr hδ.le)
    _ = 2 / δ := rfl

/-- The whole bilinear interaction is bounded using the actual sum of
inverse symbols. Individual frequency distances remain available until
the last estimate, instead of replacing them by one worst-case gap. -/
theorem norm_finiteFourierPart_le_inverseSymbolMass (a f : ZMod q → ℂ)
    (S : Finset (ZMod q)) (hS : ∀ k ∈ S, k ≠ 0) :
    ‖finiteFourierPart a f S‖ ≤
      ((q : ℝ)⁻¹ * ∑ k ∈ S, ‖cyclicDifferenceSymbol k‖⁻¹ ^ 2) *
        (∑ j, ‖a j‖) * ∑ j, ‖(cyclicDifference^[2] f) j‖ := by
  have hq : 0 ≤ (q : ℝ)⁻¹ := by positivity
  rw [finiteFourierPart, norm_mul, norm_inv, Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hq).trans
  calc
    _ ≤ (q : ℝ)⁻¹ * ∑ k ∈ S, ‖cyclicDifferenceSymbol k‖⁻¹ ^ 2 *
        (∑ j, ‖a j‖) * ∑ j, ‖(cyclicDifference^[2] f) j‖ := by
      apply mul_le_mul_of_nonneg_left _ hq
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul, dft_eq_difference_quotient 2 f (hS k hk), norm_div, norm_pow]
      calc
        _ ≤ (∑ j, ‖a j‖) * ((∑ j, ‖(cyclicDifference^[2] f) j‖) / ‖cyclicDifferenceSymbol k‖ ^ 2) := by
          gcongr
          · exact norm_dft_le_sum_norm a (-k)
          · exact norm_dft_le_sum_norm _ k
        _ = _ := by ring
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring

/-- Averaging the actual cyclic spectrum reduces the full second-
difference gap cost to one inverse power, independently of the modulus. -/
theorem norm_finiteFourierPart_le_averaged_gap (a f : ZMod q → ℂ)
    (S : Finset (ZMod q)) {δ : ℝ} (hδ : 0 < δ)
    (hS : ∀ k ∈ S, δ ≤ ‖cyclicDifferenceSymbol k‖) :
    ‖finiteFourierPart a f S‖ ≤ (2 / δ) * (∑ j, ‖a j‖) *
      ∑ j, ‖(cyclicDifference^[2] f) j‖ := by
  have hk (k : ZMod q) (hk : k ∈ S) : k ≠ 0 := by
    intro he
    have h := hS k hk
    simp [he, cyclicDifferenceSymbol] at h
    linarith
  apply (norm_finiteFourierPart_le_inverseSymbolMass a f S hk).trans
  gcongr
  exact sum_inv_sq_cyclicDifferenceSymbol_le hδ S hS

/-- Both terms of the centered Fourier interaction obey the averaged
inverse-gap estimate. The centering correction is paid in full. -/
theorem norm_centeredFourierPart_le_averaged_gap (a f : ZMod q → ℂ)
    (S : Finset (ZMod q)) {δ : ℝ} (hδ : 0 < δ)
    (hS : ∀ k ∈ S, δ ≤ ‖cyclicDifferenceSymbol k‖) :
    ‖centeredFourierPart a f S‖ ≤ (4 / δ) * (∑ j, ‖a j‖) *
      ∑ j, ‖(cyclicDifference^[2] f) j‖ := by
  have ha := norm_dft_le_sum_norm a 0
  have hzero : ‖finiteFourierPart cyclicZeroAtom f S‖ ≤
      (2 / δ) * ∑ j, ‖(cyclicDifference^[2] f) j‖ := by
    simpa only [sum_norm_cyclicZeroAtom, mul_one] using
      norm_finiteFourierPart_le_averaged_gap cyclicZeroAtom f S hδ hS
  rw [centeredFourierPart_eq_sub]
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  calc
    _ ≤ (2 / δ) * (∑ j, ‖a j‖) * (∑ j, ‖(cyclicDifference^[2] f) j‖) +
        (∑ j, ‖a j‖) * ((2 / δ) * ∑ j, ‖(cyclicDifference^[2] f) j‖) :=
      add_le_add (norm_finiteFourierPart_le_averaged_gap a f S hδ hS)
        (mul_le_mul ha hzero (norm_nonneg _) (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)))
    _ = _ := by ring

end
end RiemannGaussian
