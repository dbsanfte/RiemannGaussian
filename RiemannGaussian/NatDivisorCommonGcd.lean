import RiemannGaussian.NatProductCollision

/-!
# A complete common-divisor estimate for the first gcd kernel

The unsquared gcd kernel controls coincident factorizations throughout a
finite hyperbolic product region. Its full common-divisor expansion and
exact divided-cutoff harmonic sums give a cubic harmonic bound.
-/

open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The complete first-gcd form is bounded through all common
divisors, retaining their exact divided-cutoff weights. -/
theorem sum_Icc_gcd_div_mul_le_common_divisors (T : ℕ) :
    (∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
      (Nat.gcd d e : ℝ) / ((d : ℝ) * e)) ≤
    ∑ g ∈ Finset.Icc 1 T, (g : ℝ) *
      (∑ d ∈ Finset.Icc 1 T, if g ∣ d then 1 / (d : ℝ) else 0) ^ 2 := by
  let s := Finset.Icc 1 T
  let w : ℕ → ℕ → ℝ := fun g d ↦ if g ∣ d then 1 / (d : ℝ) else 0
  have hw (g d : ℕ) : 0 ≤ w g d := by dsimp [w]; split_ifs <;> positivity
  calc
    _ ≤ ∑ d ∈ s, ∑ e ∈ s, ∑ g ∈ s, (g : ℝ) * w g d * w g e := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      have hdp : 0 < d := (Finset.mem_Icc.mp hd).1
      have hgp : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left e hdp
      have hgm : Nat.gcd d e ∈ s := Finset.mem_Icc.mpr
        ⟨hgp, (Nat.le_of_dvd hdp (Nat.gcd_dvd_left d e)).trans (Finset.mem_Icc.mp hd).2⟩
      have h := Finset.single_le_sum (f := fun g : ℕ ↦ (g : ℝ) * w g d * w g e)
        (fun g _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg g) (hw g d)) (hw g e)) hgm
      simpa only [w, if_pos (Nat.gcd_dvd_left d e), if_pos (Nat.gcd_dvd_right d e),
        div_eq_mul_inv, one_mul, mul_inv, mul_assoc] using h
    _ = ∑ d ∈ s, ∑ g ∈ s, ∑ e ∈ s, (g : ℝ) * w g d * w g e := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
    _ = ∑ g ∈ s, ∑ d ∈ s, ∑ e ∈ s, (g : ℝ) * w g d * w g e := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g hg
      simp only [← Finset.mul_sum, ← Finset.sum_mul, w]
      ring

/-- Every positive divisor retains its reciprocal weight after
the two exact divided-cutoff harmonic sums are combined. -/
theorem sum_Icc_gcd_div_mul_le_harmonic_cube (T : ℕ) :
    (∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
      (Nat.gcd d e : ℝ) / ((d : ℝ) * e)) ≤
      (∑ g ∈ Finset.Icc 1 T, 1 / (g : ℝ)) ^ 3 := by
  let H := ∑ g ∈ Finset.Icc 1 T, 1 / (g : ℝ)
  have hH : 0 ≤ H := Finset.sum_nonneg (fun g _ ↦ by positivity)
  apply (sum_Icc_gcd_div_mul_le_common_divisors T).trans
  calc
    _ = ∑ g ∈ Finset.Icc 1 T, (1 / (g : ℝ)) *
        (∑ a ∈ Finset.Icc 1 (T / g), 1 / (a : ℝ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro g hg
      have hgp : 0 < g := (Finset.mem_Icc.mp hg).1
      rw [sum_Icc_dvd_inv_eq hgp T]
      field_simp
    _ ≤ ∑ g ∈ Finset.Icc 1 T, (1 / (g : ℝ)) * H ^ 2 := by
      apply Finset.sum_le_sum
      intro g hg
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (sq_le_sq₀ (Finset.sum_nonneg (fun a _ ↦ by positivity)) hH).mpr
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc le_rfl (Nat.div_le_self T g)) (fun a _ _ ↦ by positivity)
    _ = _ := by
      rw [← Finset.sum_mul]
      dsimp [H]
      ring

end

end RiemannGaussian
