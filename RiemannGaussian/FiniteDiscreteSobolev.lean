import RiemannGaussian.EtaDivisorGcdBound

/-!
# Finite discrete sampling with an explicit difference cost

Point values of a complex sequence are controlled by a local mean square
and the square sum of its exact forward differences. Disjoint arithmetic
blocks retain the finite sampling geometry before these estimates are
summed. This is used downstream on the literal eta Fourier family.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- Finite complex sums satisfy the cardinality-weighted square bound. -/
theorem norm_sum_sq_le_card_mul_sum_norm_sq {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i ↦ ‖f i‖) (fun _ ↦ (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at h
  apply ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ ↦ norm_nonneg (f i)))).mpr
    (norm_sum_le _ _)).trans
  simpa only [mul_one, mul_comm] using h

/-- The exact complex difference has a two-square upper bound. -/
theorem norm_sub_sq_le_two_mul_norm_sq (z w : ℂ) :
    ‖z - w‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  have h := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (norm_sub_le z w)
  nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

/-- A point value is bounded by a later value and the exact intervening
forward differences, retaining their full finite interval. -/
theorem norm_sq_le_later_add_differences (f : ℕ → ℂ) (n j : ℕ) :
    ‖f n‖ ^ 2 ≤ 2 * ‖f (n + j)‖ ^ 2 +
      2 * j * ∑ k ∈ Finset.range j, ‖f (n + k + 1) - f (n + k)‖ ^ 2 := by
  have heq : f n = f (n + j) - ∑ k ∈ Finset.range j, (f (n + k + 1) - f (n + k)) := by
    have h := Finset.sum_range_sub (fun k ↦ f (n + k)) j
    have ht : (∑ k ∈ Finset.range j, (f (n + k + 1) - f (n + k))) = f (n + j) - f n := by
      simpa only [Nat.add_zero, Nat.add_assoc] using h
    rw [ht]
    ring
  calc
    _ ≤ 2 * ‖f (n + j)‖ ^ 2 +
        2 * ‖∑ k ∈ Finset.range j, (f (n + k + 1) - f (n + k))‖ ^ 2 := by
      conv_lhs => rw [heq]
      exact norm_sub_sq_le_two_mul_norm_sq _ _
    _ ≤ _ := by
      have h := norm_sum_sq_le_card_mul_sum_norm_sq (Finset.range j)
        (fun k ↦ f (n + k + 1) - f (n + k))
      simp only [Finset.card_range] at h
      nlinarith

/-- Every point in a sampling block gives the same bound in terms of
the complete block's forward-difference energy. -/
theorem norm_sq_le_block_point_add_differences (f : ℕ → ℂ) (n : ℕ) {j h : ℕ} (hj : j < h) :
    ‖f n‖ ^ 2 ≤ 2 * ‖f (n + j)‖ ^ 2 +
      2 * h * ∑ k ∈ Finset.range h, ‖f (n + k + 1) - f (n + k)‖ ^ 2 := by
  apply (norm_sq_le_later_add_differences f n j).trans
  apply add_le_add le_rfl
  have hs : (∑ k ∈ Finset.range j, ‖f (n + k + 1) - f (n + k)‖ ^ 2) ≤
      ∑ k ∈ Finset.range h, ‖f (n + k + 1) - f (n + k)‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj.le) (fun k _ _ ↦ sq_nonneg _)
  have hp := mul_le_mul (show (j : ℝ) ≤ h by exact_mod_cast hj.le) hs
    (Finset.sum_nonneg (fun k _ ↦ sq_nonneg _)) (Nat.cast_nonneg h)
  nlinarith

/-- A finite discrete Sobolev estimate with the actual block length:
the local mean square and forward-difference square sum control its first point. -/
theorem norm_sq_le_discrete_block_sobolev (f : ℕ → ℂ) (n : ℕ) {h : ℕ} (hh : 0 < h) :
    ‖f n‖ ^ 2 ≤ (2 / (h : ℝ)) * (∑ j ∈ Finset.range h, ‖f (n + j)‖ ^ 2) +
      2 * h * ∑ k ∈ Finset.range h, ‖f (n + k + 1) - f (n + k)‖ ^ 2 := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hs := Finset.sum_le_sum (s := Finset.range h)
    (fun j hj ↦ norm_sq_le_block_point_add_differences f n (Finset.mem_range.mp hj))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hs
  apply (le_of_mul_le_mul_left (a := (h : ℝ)) ?_ hhR)
  convert hs using 1
  field_simp

end

end RiemannGaussian
