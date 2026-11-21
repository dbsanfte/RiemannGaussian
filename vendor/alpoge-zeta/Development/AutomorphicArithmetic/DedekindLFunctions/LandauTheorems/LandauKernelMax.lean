import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem landau_kernel_max (k : ℕ) {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    u ^ k * Real.exp (-a * u) / (k.factorial : ℝ) ≤ 1 / a ^ k := by
  have h := Real.pow_div_factorial_le_exp (a * u) (mul_nonneg ha.le hu) k
  have hak : 0 < a ^ k := pow_pos ha k
  rw [le_div_iff₀ hak]
  calc u ^ k * Real.exp (-a * u) / (k.factorial : ℝ) * a ^ k
      = (a * u) ^ k / (k.factorial : ℝ) * Real.exp (-(a * u)) := by
        rw [mul_pow, neg_mul]; ring
    _ ≤ Real.exp (a * u) * Real.exp (-(a * u)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

end Deduction

end
