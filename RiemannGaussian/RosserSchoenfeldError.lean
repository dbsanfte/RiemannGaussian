/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldZeroFree

/-!
# The last numerical range in the Rosser--Schoenfeld theta comparison

Above `exp(5000)`, the explicit error expression from Theorem 11 is
strictly less than `0.47 / log x`, as required in the proof of Theorem 31.
The exponential is bounded by a proved Taylor term, with exact factorial
arithmetic. This proves the numerical implication only: the actual
prime-error bound in Theorem 11 remains a separate analytic obligation.
`RosserSchoenfeldLargeChebyshev` now proves the required large-range
theta allowance independently from the stronger proved zero-free edge.
-/

namespace RiemannGaussian.RosserSchoenfeldError
noncomputable section
open Real RosserSchoenfeldZeroFree

/-- The exact error expression in Rosser--Schoenfeld Theorem 11. -/
def sourceError (x : ℝ) : ℝ :=
  sqrt (log x) * exp (-sqrt (log x / sourceConstant))

/-- The complete error expression pays the logarithmic allowance throughout
the last source range; there is no unevaluated eventual threshold. -/
theorem sourceError_lt_log_allowance {x : ℝ} (hx : exp 5000 ≤ x) :
    sourceError x < (47 / 100) / log x := by
  have hx0 : 0 < x := (exp_pos 5000).trans_le hx
  have ht : 5000 ≤ log x := (le_log_iff_exp_le hx0).mpr hx
  have ht0 : 0 < log x := by linarith
  let y := sqrt (log x / sourceConstant)
  have hy0 : 0 < y := sqrt_pos.mpr (div_pos ht0 sourceConstant_pos)
  have hy2 : y ^ 2 = log x / sourceConstant :=
    sq_sqrt (div_nonneg ht0.le sourceConstant_pos.le)
  have hscale : log x = sourceConstant * y ^ 2 := by
    rw [hy2, mul_div_cancel₀ _ sourceConstant_pos.ne']
  have hty : log x ≤ 18 * y ^ 2 := by
    rw [hscale]
    exact mul_le_mul_of_nonneg_right sourceConstant_le_eighteen (sq_nonneg y)
  have hy : 16 ≤ y := by nlinarith
  have hs0 := sqrt_nonneg (log x)
  have hsq := sq_sqrt ht0.le
  have hs : sqrt (log x) ≤ 5 * y := by nlinarith
  have hmass : log x * sqrt (log x) ≤ 90 * y ^ 3 := by
    have hh := mul_le_mul hty hs hs0 (mul_nonneg (by norm_num) (sq_nonneg y))
    nlinarith only [hh]
  have he : y ^ 14 / (Nat.factorial 14 : ℝ) ≤ exp y := pow_div_factorial_le_exp y hy0.le 14
  have hcost : log x * sourceError x < 47 / 100 := by
    calc
      _ = log x * sqrt (log x) / exp y := by
        simp only [sourceError, y, exp_neg, div_eq_mul_inv]
        ring
      _ ≤ 90 * y ^ 3 / exp y := div_le_div_of_nonneg_right hmass (exp_pos y).le
      _ ≤ 90 * y ^ 3 / (y ^ 14 / (Nat.factorial 14 : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) he
      _ = 90 * (Nat.factorial 14 : ℝ) / y ^ 11 := by
        field_simp
      _ ≤ 90 * (Nat.factorial 14 : ℝ) / 16 ^ 11 := by gcongr
      _ < _ := by norm_num [Nat.factorial]
  apply (lt_div_iff₀ ht0).mpr
  simpa only [mul_comm] using hcost

end
end RiemannGaussian.RosserSchoenfeldError
