/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovKorobovBilinearPhase

/-!
# Product-shift averaging of the actual Dirichlet block

The original finite Dirichlet sum is averaged over integer product shifts.
An exact identity retains the complex endpoint correction and every outer
base phase. Only the logarithmic Taylor remainder is then estimated.

This is the averaging and approximation step of Bellotti (2023), Lemma 8.2.
We use integer block lengths, so there is no hidden endpoint rounding. The
quantitative mean-value estimate for the resulting polynomial sum is a
separate, still open obligation.
-/

namespace RiemannGaussian.VinogradovKorobovBlock
noncomputable section
open scoped BigOperators
open VinogradovKorobovBilinearPhase

/-- The first `L` terms, with the starting point incorporated into `f`. -/
def block (f : ℕ → ℂ) (L : ℕ) : ℂ := ∑ n ∈ Finset.range L, f n

/-- The complete signed endpoint correction for a forward integer shift. -/
def boundary (f : ℕ → ℂ) (L p : ℕ) : ℂ :=
  block f p - block (fun n => f (L + n)) p

/-- Splitting a block pays no norm or endpoint approximation. -/
theorem block_add (f : ℕ → ℂ) (L p : ℕ) :
    block f (L + p) = block f L + block (fun n => f (L + n)) p := by
  exact Finset.sum_range_add f L p

/-- Every forward shift has its exact signed endpoint correction, even
when the shift exceeds the original block length. -/
theorem block_shift (f : ℕ → ℂ) (L p : ℕ) :
    block f L = block (fun n => f (n + p)) L + boundary f L p := by
  have h : block f L + block (fun n => f (L + n)) p =
      block f p + block (fun n => f (n + p)) L := by
    rw [← block_add, Nat.add_comm L p, block_add]
    simp only [Nat.add_comm]
  unfold boundary
  linear_combination h

/-- Arbitrary complex weights preserve the full averaged sum and the
weighted signed boundary; no independence of shifts is assumed. -/
theorem weighted_shift_identity {ι : Type*} (S : Finset ι) (p : ι → ℕ)
    (w : ι → ℂ) (f : ℕ → ℂ) (L : ℕ) :
    (∑ i ∈ S, w i) * block f L =
      (∑ n ∈ Finset.range L, ∑ i ∈ S, w i * f (n + p i)) +
      ∑ i ∈ S, w i * boundary f L (p i) := by
  rw [Finset.sum_mul]
  calc
    _ = ∑ i ∈ S, (w i * block (fun n => f (n + p i)) L +
        w i * boundary f L (p i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← mul_add, ← block_shift]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      simp only [block, Finset.mul_sum]
      exact Finset.sum_comm

/-- A unit-bounded sequence pays at most two terms per unit of shift.
The exact boundary remains available in `block_shift`. -/
theorem boundary_norm_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (L p : ℕ) :
    ‖boundary f L p‖ ≤ 2 * p := by
  have hb (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) : ‖block g p‖ ≤ p := by
    calc
      _ ≤ ∑ n ∈ Finset.range p, ‖g n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range p, (1 : ℝ) :=
        Finset.sum_le_sum (fun n _ => hg n)
      _ = _ := by simp
  exact (norm_sub_le _ _).trans (by
    have h₁ := hb f hf
    have h₂ := hb (fun n => f (L + n)) (fun n => hf (L + n))
    linarith)

/-- The literal imaginary power at a positive real starting point. -/
def dirichletTerm (t z : ℝ) (n : ℕ) : ℂ :=
  ((z + n : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I))

/-- The original base phase, retained across the whole outer block. -/
def basePhase (t z : ℝ) : ℂ :=
  Complex.exp (((-t * Real.log z : ℝ) : ℂ) * Complex.I)

/-- Each base phase has unit norm, without any restriction on its angle. -/
theorem norm_basePhase (t z : ℝ) : ‖basePhase t z‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- Actual imaginary powers are unit phases at every term of a positive block. -/
theorem dirichletTerm_eq {z : ℝ} (hz : 0 < z) (t : ℝ) (n : ℕ) :
    dirichletTerm t z n = basePhase t (z + n) := by
  have h := shifted_cpow_eq t (z := z + n) (a := 0) (b := 0) (by positivity)
    (by rfl) (by rfl)
  simpa [dirichletTerm, basePhase, logarithmicPhase] using h

/-- There is no growth loss in the imaginary-power amplitudes. -/
theorem norm_dirichletTerm {z : ℝ} (hz : 0 < z) (t : ℝ) (n : ℕ) :
    ‖dirichletTerm t z n‖ = 1 := by
  rw [dirichletTerm_eq hz, norm_basePhase]

/-- The integer product shift is exactly the coupled logarithmic phase. -/
theorem dirichletTerm_shift {z : ℝ} (hz : 0 < z) (t : ℝ) (n a b : ℕ) :
    dirichletTerm t z (n + a * b) =
      basePhase t (z + n) * logarithmicPhase t (z + n) a b := by
  simpa only [dirichletTerm, basePhase, Nat.cast_add, Nat.cast_mul, add_assoc] using
    shifted_cpow_eq t (z := z + n) (a := a) (b := b) (by positivity)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- All original outer phases and inner factor correlations before approximation. -/
def logarithmicBlock (t z : ℝ) (L : ℕ) (A B : Finset ℕ) : ℂ :=
  ∑ n ∈ Finset.range L, basePhase t (z + n) *
    ∑ a ∈ A, ∑ b ∈ B, logarithmicPhase t (z + n) a b

/-- The full coupled polynomial block, before any outer triangle inequality. -/
def polynomialBlock (k : ℕ) (t z : ℝ) (L : ℕ) (A B : Finset ℕ) : ℂ :=
  ∑ n ∈ Finset.range L, basePhase t (z + n) *
    ∑ a ∈ A, ∑ b ∈ B, polynomialPhase k t (z + n) a b

/-- The actual averaged endpoint correction, with its signs and phases intact. -/
def boundaryBlock (t z : ℝ) (L : ℕ) (A B : Finset ℕ) : ℂ :=
  ∑ a ∈ A, ∑ b ∈ B, boundary (dirichletTerm t z) L (a * b)

/-- The original Dirichlet block equals its complete product-shift average
plus the signed boundary. All outer base phases survive. -/
theorem averaged_dirichlet_identity {z : ℝ} (hz : 0 < z)
    (t : ℝ) (L : ℕ) (A B : Finset ℕ) :
    ((A.card : ℂ) * B.card) * block (dirichletTerm t z) L =
      logarithmicBlock t z L A B + boundaryBlock t z L A B := by
  have h := weighted_shift_identity (A ×ˢ B) (fun p => p.1 * p.2)
    (fun _ => 1) (dirichletTerm t z) L
  simpa only [Finset.sum_product, Finset.sum_const, Finset.card_product,
    nsmul_eq_mul, mul_one, one_mul, Nat.cast_mul, dirichletTerm_shift hz,
    ← Finset.mul_sum, logarithmicBlock, boundaryBlock] using h

/-- Only the Taylor perturbation is estimated. The complete polynomial
block, including cancellations between distinct outer base phases, survives. -/
theorem logarithmicBlock_sub_polynomialBlock_le {z M₁ M₂ : ℝ}
    (hz : 0 < z) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (k : ℕ) (t : ℝ) (L : ℕ) (A B : Finset ℕ)
    (hA : ∀ a ∈ A, (a : ℝ) ≤ M₁) (hB : ∀ b ∈ B, (b : ℝ) ≤ M₂) :
    ‖logarithmicBlock t z L A B - polynomialBlock k t z L A B‖ ≤
      ((A.card : ℝ) * B.card) * L *
        (|t| * (M₁ * M₂ / z) ^ (k + 1) / (k + 1)) := by
  unfold logarithmicBlock polynomialBlock
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.range L, ‖basePhase t (z + n) *
        (∑ a ∈ A, ∑ b ∈ B, logarithmicPhase t (z + n) a b) -
        basePhase t (z + n) *
        (∑ a ∈ A, ∑ b ∈ B, polynomialPhase k t (z + n) a b)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range L, ((A.card : ℝ) * B.card) *
        (|t| * (M₁ * M₂ / z) ^ (k + 1) / (k + 1)) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [← mul_sub, norm_mul, norm_basePhase, one_mul]
      have h := sum_error_le_card A B (fun a => (a : ℝ)) (fun b => (b : ℝ))
        k t (z := z + n) (by positivity)
        (fun a ha => ⟨Nat.cast_nonneg a, hA a ha⟩)
        (fun b hb => ⟨Nat.cast_nonneg b, hB b hb⟩)
      apply h.trans
      have hr : M₁ * M₂ / (z + n) ≤ M₁ * M₂ / z :=
        div_le_div_of_nonneg_left (mul_nonneg hM₁ hM₂) hz
          (le_add_of_nonneg_right (Nat.cast_nonneg _))
      gcongr
    _ = _ := by simp; ring

/-- The averaged endpoint cost uses the actual first moments of the two
shift sets. It does not replace every product by the largest product. -/
theorem boundaryBlock_norm_le {z : ℝ} (hz : 0 < z)
    (t : ℝ) (L : ℕ) (A B : Finset ℕ) :
    ‖boundaryBlock t z L A B‖ ≤
      2 * (∑ a ∈ A, (a : ℝ)) * ∑ b ∈ B, (b : ℝ) := by
  unfold boundaryBlock
  calc
    _ ≤ ∑ a ∈ A, ∑ b ∈ B, ‖boundary (dirichletTerm t z) L (a * b)‖ := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun a _ => norm_sum_le _ _)
    _ ≤ ∑ a ∈ A, ∑ b ∈ B, 2 * ((a : ℝ) * b) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      simpa only [Nat.cast_mul] using boundary_norm_le (dirichletTerm t z)
        (fun n => (norm_dirichletTerm hz t n).le) L (a * b)
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring

/-- An unconditional approximation theorem for the literal Dirichlet block.
The signed boundary is subtracted exactly before estimating the error. -/
theorem dirichlet_polynomial_error_le {z M₁ M₂ : ℝ}
    (hz : 0 < z) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (k : ℕ) (t : ℝ) (L : ℕ) (A B : Finset ℕ)
    (hA : ∀ a ∈ A, (a : ℝ) ≤ M₁) (hB : ∀ b ∈ B, (b : ℝ) ≤ M₂) :
    ‖((A.card : ℂ) * B.card) * block (dirichletTerm t z) L -
      polynomialBlock k t z L A B - boundaryBlock t z L A B‖ ≤
      ((A.card : ℝ) * B.card) * L *
        (|t| * (M₁ * M₂ / z) ^ (k + 1) / (k + 1)) := by
  rw [averaged_dirichlet_identity hz]
  convert logarithmicBlock_sub_polynomialBlock_le hz hM₁ hM₂ k t L A B hA hB using 1
  congr 1
  ring

/-- The polynomial approximation includes the complete signed endpoint
correction. Nonempty shift sets are required by its error theorem. -/
def approximation (k : ℕ) (t z : ℝ) (L : ℕ) (A B : Finset ℕ) : ℂ :=
  (polynomialBlock k t z L A B + boundaryBlock t z L A B) /
    ((A.card : ℂ) * B.card)

/-- The actual complex block, rather than just its norm, is approximated
with the explicit normalized Taylor allowance. -/
theorem block_sub_approximation_le {z M₁ M₂ : ℝ}
    (hz : 0 < z) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (k : ℕ) (t : ℝ) (L : ℕ) (A B : Finset ℕ)
    (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hA : ∀ a ∈ A, (a : ℝ) ≤ M₁) (hB : ∀ b ∈ B, (b : ℝ) ≤ M₂) :
    ‖block (dirichletTerm t z) L - approximation k t z L A B‖ ≤
      L * (|t| * (M₁ * M₂ / z) ^ (k + 1) / (k + 1)) := by
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast hAn.card_pos
  have hBc : (0 : ℝ) < B.card := by exact_mod_cast hBn.card_pos
  have hm : (0 : ℝ) < (A.card : ℝ) * B.card := mul_pos hAc hBc
  have hmc : (A.card : ℂ) * B.card ≠ 0 := mul_ne_zero
    (Nat.cast_ne_zero.mpr hAn.card_pos.ne') (Nat.cast_ne_zero.mpr hBn.card_pos.ne')
  have heq : block (dirichletTerm t z) L - approximation k t z L A B =
      (((A.card : ℂ) * B.card) * block (dirichletTerm t z) L -
        polynomialBlock k t z L A B - boundaryBlock t z L A B) /
      ((A.card : ℂ) * B.card) := by
    unfold approximation
    apply (eq_div_iff hmc).mpr
    rw [sub_mul, div_mul_cancel₀ _ hmc]
    ring
  rw [heq, norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  apply (div_le_iff₀ hm).mpr
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    dirichlet_polynomial_error_le hz hM₁ hM₂ k t L A B hA hB

/-- The normalized approximation retains the signed endpoint and the full
outer polynomial sum together under a single norm. -/
theorem dirichlet_norm_le_coupled {z M₁ M₂ : ℝ}
    (hz : 0 < z) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (k : ℕ) (t : ℝ) (L : ℕ) (A B : Finset ℕ)
    (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hA : ∀ a ∈ A, (a : ℝ) ≤ M₁) (hB : ∀ b ∈ B, (b : ℝ) ≤ M₂) :
    ‖block (dirichletTerm t z) L‖ ≤
      ‖polynomialBlock k t z L A B + boundaryBlock t z L A B‖ /
        ((A.card : ℝ) * B.card) +
      L * (|t| * (M₁ * M₂ / z) ^ (k + 1) / (k + 1)) := by
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast hAn.card_pos
  have hBc : (0 : ℝ) < B.card := by exact_mod_cast hBn.card_pos
  have hm : (0 : ℝ) < (A.card : ℝ) * B.card := mul_pos hAc hBc
  have he := dirichlet_polynomial_error_le hz hM₁ hM₂ k t L A B hA hB
  apply (mul_le_mul_iff_of_pos_left hm).mp
  calc
    _ = ‖((A.card : ℂ) * B.card) * block (dirichletTerm t z) L‖ := by
      rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    _ = ‖(polynomialBlock k t z L A B + boundaryBlock t z L A B) +
        (((A.card : ℂ) * B.card) * block (dirichletTerm t z) L -
          polynomialBlock k t z L A B - boundaryBlock t z L A B)‖ := by
      congr 1
      ring
    _ ≤ ‖polynomialBlock k t z L A B + boundaryBlock t z L A B‖ +
        ((A.card : ℝ) * B.card) * L *
          (|t| * (M₁ * M₂ / z) ^ (k + 1) / (k + 1)) :=
      (norm_add_le _ _).trans (add_le_add_right he _)
    _ = _ := by field_simp

/-- The usual separated estimate is a downstream corollary. The boundary
allowance is twice the product of the actual average shifts. -/
theorem dirichlet_norm_le {z M₁ M₂ : ℝ}
    (hz : 0 < z) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (k : ℕ) (t : ℝ) (L : ℕ) (A B : Finset ℕ)
    (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hA : ∀ a ∈ A, (a : ℝ) ≤ M₁) (hB : ∀ b ∈ B, (b : ℝ) ≤ M₂) :
    ‖block (dirichletTerm t z) L‖ ≤
      ‖polynomialBlock k t z L A B‖ / ((A.card : ℝ) * B.card) +
      (2 * (∑ a ∈ A, (a : ℝ)) * ∑ b ∈ B, (b : ℝ)) / ((A.card : ℝ) * B.card) +
      L * (|t| * (M₁ * M₂ / z) ^ (k + 1) / (k + 1)) := by
  apply (dirichlet_norm_le_coupled hz hM₁ hM₂ k t L A B hAn hBn hA hB).trans
  have hnorm := (norm_add_le (polynomialBlock k t z L A B)
    (boundaryBlock t z L A B)).trans (add_le_add_right (boundaryBlock_norm_le hz t L A B) _)
  rw [← add_div]
  gcongr

end
end RiemannGaussian.VinogradovKorobovBlock
