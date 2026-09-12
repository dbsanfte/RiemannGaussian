/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteResonancePartition

/-!
# A complete finite second-difference estimate

Increasing increments with positive lower separation and bounded upper
separation give a bound for the whole original exponential sum. The exact
resonance partition is preserved upstream: short resonant bands are paid
for by their actual cardinalities, and every remaining complete block is
bounded by periodic Kuzmin--Landau. Both endpoint cells are included.
The resonance allowance remains a free parameter, not a fitted family.
-/

namespace RiemannGaussian.DiscreteSecondDerivativeTest
noncomputable section
open PhaseIncrementInverse FiniteKuzminLandau MonotonePhaseBlocks
open FiniteResonancePartition
open scoped Classical

/-- Nonnegative lower separation forces monotonicity of the original
finite increment sequence. -/
theorem monotone_of_separation {d : ℕ → ℝ} {N : ℕ} {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hsep : ∀ i < N, ∀ j < N, i ≤ j → ℓ * ((j : ℝ) - i) ≤ d j - d i) :
    MonotoneOn d (Set.Iio N) := by
  intro i hi j hj hij
  have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hs := hsep i hi j hj hij
  have hp := mul_nonneg hℓ (sub_nonneg.mpr hijR)
  linarith

/-- The near-resonant band is bounded by its proved number of original
indices. Its two boundary allowances and one endpoint cost are explicit. -/
theorem resonant_band_bound (φ : ℕ → ℝ) (N : ℕ) (m : ℤ) {η ℓ : ℝ}
    (hη : 0 ≤ η) (hℓ : 0 < ℓ)
    (hsep : ∀ i < N, ∀ j < N, i ≤ j →
      ℓ * ((j : ℝ) - i) ≤ increment φ j - increment φ i) :
    ‖∑ n ∈ band (increment φ) N ((m : ℝ) * (2 * Real.pi) - η)
      ((m : ℝ) * (2 * Real.pi) + η), rotation (φ n)‖ ≤ 2 * η / ℓ + 1 := by
  have hc := band_card_le hℓ
    (show (m : ℝ) * (2 * Real.pi) - η ≤ (m : ℝ) * (2 * Real.pi) + η by linarith)
    (monotone_of_separation hℓ.le hsep) hsep
  have hn := norm_sum_le (band (increment φ) N ((m : ℝ) * (2 * Real.pi) - η)
    ((m : ℝ) * (2 * Real.pi) + η)) (fun n ↦ rotation (φ n))
  simp only [norm_rotation, Finset.sum_const, nsmul_eq_mul, mul_one] at hn
  have he : (m : ℝ) * (2 * Real.pi) + η - ((m : ℝ) * (2 * Real.pi) - η) =
      2 * η := by ring
  rw [he] at hc
  exact hn.trans hc

/-- Upper separation bounds the number of resonance cells touched by
the full sum, including both possible partial endpoint cells. -/
theorem cells_card_le_of_separation {d : ℕ → ℝ} {N : ℕ} (η : ℝ) {U : ℝ}
    (hU : 0 ≤ U) (hd : MonotoneOn d (Set.Iio N))
    (hsep : ∀ i < N, ∀ j < N, i ≤ j → d j - d i ≤ U * ((j : ℝ) - i)) :
    ((cells d N η).card : ℝ) ≤ U * N / (2 * Real.pi) + 2 := by
  apply (cells_card_le η hd).trans
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 2 * Real.pi)
  by_cases hN : N = 0
  · subst N
    simp
  have hs := hsep 0 (by omega) (N - 1) (by omega) (Nat.zero_le _)
  have hn : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
  simp only [Nat.cast_zero, sub_zero] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left hn hU)

/-- A finite exponential sum is bounded without excluding any resonance
or imposing any prior bound on the phase winding. -/
theorem bound (φ : ℕ → ℝ) (N : ℕ) {η ℓ U : ℝ}
    (hη : 0 < η) (hηπ : η ≤ Real.pi) (hℓ : 0 < ℓ) (hU : 0 ≤ U)
    (hlo : ∀ i < N, ∀ j < N, i ≤ j →
      ℓ * ((j : ℝ) - i) ≤ increment φ j - increment φ i)
    (hhi : ∀ i < N, ∀ j < N, i ≤ j →
      increment φ j - increment φ i ≤ U * ((j : ℝ) - i)) :
    ‖∑ n ∈ Finset.range N, rotation (φ n)‖ ≤
      (U * N / (2 * Real.pi) + 2) * (2 * η / ℓ + 1 + 2 * Real.pi / η) := by
  have hd := monotone_of_separation hℓ.le hlo
  rw [sum_eq_bands (increment φ) N (fun n ↦ rotation (φ n)) hη.le hηπ hd]
  calc
    _ ≤ ∑ m ∈ cells (increment φ) N η,
        ‖(∑ n ∈ band (increment φ) N ((m : ℝ) * (2 * Real.pi) - η)
          ((m : ℝ) * (2 * Real.pi) + η), rotation (φ n)) +
            ∑ n ∈ band (increment φ) N ((m : ℝ) * (2 * Real.pi) + η)
              ((m : ℝ) * (2 * Real.pi) + 2 * Real.pi - η), rotation (φ n)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m ∈ cells (increment φ) N η, (2 * η / ℓ + 1 + 2 * Real.pi / η) := by
      apply Finset.sum_le_sum
      intro m _
      exact (norm_add_le _ _).trans (add_le_add
        (resonant_band_bound φ N m hη.le hℓ hlo)
        (nonresonant_band_bound φ N m hη hd))
    _ = ((cells (increment φ) N η).card : ℝ) *
        (2 * η / ℓ + 1 + 2 * Real.pi / η) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (cells_card_le_of_separation η hU hd hhi)
      (by positivity)

end
end RiemannGaussian.DiscreteSecondDerivativeTest
