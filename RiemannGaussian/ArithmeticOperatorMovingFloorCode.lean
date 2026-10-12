/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorFloorInverseAudit

/-!
# Growing linear floor/Gamma codes still lose a zeta-zero power source

All moving physical endpoints and all complex row coefficients are kept.
The row set may grow, so this strengthens the fixed finite linear no-go.
At a diagnostic strip zero each physical floor observation is uniformly
bounded. Any joined code with exponential coefficient budget strictly
below the source growth is source-small, even with polynomial overhead.

This is a diagnostic operator theorem, not a bound for a literal twisted
Mangoldt sum and not a claim about nonlinear products of observations.
-/

namespace RiemannGaussian.ArithmeticOperatorMovingFloorCode
noncomputable section
open Complex Filter ArithmeticOperatorFloorBoundaryAudit ArithmeticOperatorFloorInverseAudit
open scoped Topology BigOperators

/-- Growing, complex-coded physical observations, with arbitrary cutoffs. -/
def movingCode {ι : Type*} (S : ℕ → Finset ι) (coeff : ℕ → ι → ℂ)
    (cutoff : ℕ → ι → ℝ) (s : ℂ) (J : ℕ) : ℂ :=
  ∑ i ∈ S J, coeff J i*truncatedResponse s (cutoff J i)

/-- The entire code is joined before estimating; no physical endpoint
restriction or fixed-cardinality hypothesis is needed. -/
theorem norm_movingCode_le {ι : Type*} (S : ℕ → Finset ι)
    (coeff : ℕ → ι → ℂ) (cutoff : ℕ → ι → ℝ) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1) (hz : riemannZeta s = 0) (J : ℕ) :
    ‖movingCode S coeff cutoff s J‖ ≤ (∑ i ∈ S J, ‖coeff J i‖)/s.re := by
  unfold movingCode
  calc
    _ ≤ ∑ i ∈ S J, ‖coeff J i*truncatedResponse s (cutoff J i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S J, ‖coeff J i‖*(1/s.re) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_truncatedResponse_le_of_zeta_zero hs hs1 hz _)
        (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Uniform growing-code rejection. A polynomial overhead and arbitrary
moving cutoff geometry cannot recover a source with larger exponential
rate than the TOTAL coefficient budget. Modular/Gaussian linear row
coding is included whenever it satisfies that explicit budget. -/
theorem tendsto_scaled_movingCode {ι : Type*} (S : ℕ → Finset ι)
    (coeff : ℕ → ι → ℂ) (cutoff : ℕ → ι → ℝ) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1) (hz : riemannZeta s = 0)
    (C : ℝ) (d : ℕ) (a b : ℝ) (hab : a < b)
    (hbudget : ∀ J, (∑ i ∈ S J, ‖coeff J i‖) ≤
      C*((J+1 : ℕ) : ℝ)^d*(Real.exp a)^J) :
    Tendsto (fun J : ℕ => ((Real.exp (-b))^J : ℂ)*movingCode S coeff cutoff s J)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun J : ℕ =>
      (C/s.re)*(((J+1 : ℕ) : ℝ)^d*(Real.exp (a-b))^J)) atTop (𝓝 0) := by
    simpa using (tendsto_shifted_polynomial_geometric d (Real.exp_pos _)
      (Real.exp_lt_one_iff.mpr (sub_neg.mpr hab))).const_mul (C/s.re)
  apply squeeze_zero_norm (fun J => ?_) ht
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (Real.exp (-b))^J*((∑ i ∈ S J, ‖coeff J i‖)/s.re) :=
      mul_le_mul_of_nonneg_left (norm_movingCode_le S coeff cutoff hs hs1 hz J)
        (pow_nonneg (Real.exp_pos _).le J)
    _ ≤ (Real.exp (-b))^J*(C*((J+1 : ℕ) : ℝ)^d*(Real.exp a)^J/s.re) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hbudget J) hs.le)
        (pow_nonneg (Real.exp_pos _).le J)
    _ = _ := by
      rw [show Real.exp (a-b) = Real.exp (-b)*Real.exp a by
        rw [← Real.exp_add]; congr 1; ring, mul_pow]
      ring

/-- The literal matched power scale is one instance of the preceding
gate, not an assumption that the actual prime sum is small. -/
theorem tendsto_power_scaled_polynomial_code {ι : Type*} (S : ℕ → Finset ι)
    (coeff : ℕ → ι → ℂ) (cutoff : ℕ → ι → ℝ) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1) (hz : riemannZeta s = 0)
    (C : ℝ) (d : ℕ)
    (hbudget : ∀ J, (∑ i ∈ S J, ‖coeff J i‖) ≤ C*((J+1 : ℕ) : ℝ)^d) :
    Tendsto (fun J : ℕ => ((Real.exp (-s.re*Real.log 2))^J : ℂ)*
      movingCode S coeff cutoff s J) atTop (𝓝 0) := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hh := tendsto_scaled_movingCode S coeff cutoff hs hs1 hz C d 0
    (s.re*Real.log 2) (mul_pos hs hlog) (by simpa using hbudget)
  simpa only [neg_mul] using hh

end
end RiemannGaussian.ArithmeticOperatorMovingFloorCode
