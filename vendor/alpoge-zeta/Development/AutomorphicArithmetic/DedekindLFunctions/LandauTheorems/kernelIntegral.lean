import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem kernel_integral (k : ℕ) (a : ℝ) (ha : 0 < a) :
    ∫ u in Ioi (0 : ℝ), u ^ k * Real.exp (-a * u) / (k.factorial : ℝ) = (a ^ (k + 1))⁻¹ := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi hk ha
  have e : ∀ u : ℝ, u ^ k * Real.exp (-a * u) = u ^ (((k : ℝ) + 1) - 1) * Real.exp (-(a * u)) :=
    fun u => by rw [add_sub_cancel_right, Real.rpow_natCast, neg_mul]
  rw [MeasureTheory.integral_div]
  simp_rw [e]
  rw [key, Real.Gamma_nat_eq_factorial]
  have h2 : ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  rw [h2, Real.rpow_natCast, one_div, inv_pow, mul_div_assoc, div_self hf, mul_one]

end Deduction

end
