import RiemannGaussian.EtaWeightedDivisorSampling

/-!
# Averaging the full physical inverse-square error

A telescoping reciprocal difference controls the entire moving window.
The resulting average retains both endpoints and removes an unnecessary
quadratic constraint on the starting cutoff of physical divisor estimates.
-/

open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- A positive integer reciprocal square is controlled by its adjacent reciprocal difference. -/
theorem nat_inv_sq_le_two_sub_inv {m : ℕ} (hm : 1 ≤ m) :
    1 / (m : ℝ) ^ 2 ≤ 2 * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (0 : ℝ) < m := by linarith
  apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
  field_simp
  nlinarith

/-- The whole inverse-square window is bounded by its two actual reciprocal endpoints. -/
theorem sum_range_inv_sq_le_endpoints {A : ℕ} (hA : 1 ≤ A) (L : ℕ) :
    (∑ n ∈ Finset.range L, 1 / ((A + n : ℕ) : ℝ) ^ 2) ≤
      2 * (1 / (A : ℝ) - 1 / ((A + L : ℕ) : ℝ)) := by
  calc
    _ ≤ ∑ n ∈ Finset.range L,
        2 * (1 / ((A + n : ℕ) : ℝ) - 1 / ((A + (n + 1) : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
        nat_inv_sq_le_two_sub_inv (show 1 ≤ A + n by omega)
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_range_sub']
      simp only [Nat.add_zero]

/-- Averaging preserves the gain from the actual length of the physical window. -/
theorem mean_range_inv_sq_le {A L : ℕ} (hA : 1 ≤ A) (hL : 0 < L) :
    (∑ n ∈ Finset.range L, 1 / ((A + n : ℕ) : ℝ) ^ 2) / L ≤
      2 / ((A : ℝ) * (A + L)) := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  apply (div_le_div_of_nonneg_right (sum_range_inv_sq_le_endpoints hA L) hLR.le).trans_eq
  push_cast
  field_simp
  ring

/-- The averaged physical error costs at most one coefficient energy
when the product range is physical and the averaging window is quadratic. -/
theorem nat_cube_div_window_le_one {T A L : ℕ} (hT : 1 ≤ T)
    (hTA : T ≤ A) (hTL : T ^ 2 ≤ L) :
    (T : ℝ) ^ 3 / ((A : ℝ) * (A + L)) ≤ 1 := by
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTAR : (T : ℝ) ≤ A := by exact_mod_cast hTA
  have hTLR : (T : ℝ) ^ 2 ≤ L := by exact_mod_cast hTL
  have hAR : (0 : ℝ) < A := by linarith
  have hLR : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  apply (div_le_one (mul_pos hAR (by positivity))).mpr
  have hmul := mul_le_mul hTAR hTLR (sq_nonneg (T : ℝ)) hAR.le
  nlinarith

end

end RiemannGaussian
