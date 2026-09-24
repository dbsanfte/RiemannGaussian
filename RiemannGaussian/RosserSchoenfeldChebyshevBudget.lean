/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldSmoothingBudget

/-!
# Explicit constants for monotone desmoothing

These elementary inequalities pay the literal logarithmic step, shifted
error allowances and linear Archimedean term in the large-argument
Chebyshev estimate. The step is exactly `1/(4*t)`.
-/

namespace RiemannGaussian.RosserSchoenfeldChebyshevBudget
noncomputable section
open Real

/-- The exact logarithmic step used for desmoothing. -/
def step (t : ℝ) : ℝ := 1/(4*t)

/-- The positive step is uniformly small on the published large range. -/
theorem step_bounds {t : ℝ} (ht : 5000 ≤ t) : 0 < step t ∧ step t ≤ 1/1000 := by
  unfold step
  constructor
  · positivity
  · apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith

/-- Both smoothed endpoints stay inside the already proved domain. -/
theorem shifted_domain {t : ℝ} (ht : 5000 ≤ t) : 4900 ≤ t-step t ∧ 4900 ≤ t+step t := by
  have hh := step_bounds ht
  constructor <;> linarith

/-- A quadratic upper bound for the forward exponential at the actual step size. -/
theorem exp_forward {h : ℝ} (hh : 0 ≤ h) (hh' : h ≤ 1/1000) :
    exp h ≤ 1+h+(101/100)*h^2 := by
  apply (exp_bound_div_one_sub_of_interval hh (by linarith)).trans
  apply (div_le_iff₀ (by linarith : 0 < 1-h)).mpr
  have hp := mul_nonneg (sq_nonneg h) (show 0 ≤ 1/100-(101/100)*h by linarith)
  nlinarith only [hp]

/-- The forward exponential pays at most a one-percent shift of an error allowance. -/
theorem exp_small {h : ℝ} (hh : 0 ≤ h) (hh' : h ≤ 1/1000) : exp h ≤ 101/100 := by
  apply (exp_bound_div_one_sub_of_interval hh (by linarith)).trans
  exact (div_le_iff₀ (by linarith : 0 < 1-h)).mpr (by linarith)

/-- The backward exponential retains its one-sided quadratic saving. -/
theorem exp_backward {h : ℝ} (hh : 0 ≤ h) : exp (-h) ≤ 1-h+h^2 := by
  rw [exp_neg, ← one_div]
  apply (one_div_le_one_div_of_le (by linarith : 0 < h+1) (add_one_le_exp h)).trans
  apply (div_le_iff₀ (by linarith : 0 < h+1)).mpr
  nlinarith [pow_nonneg hh 3]

/-- Moving the denominator backward costs less than one percent. -/
theorem backward_denominator {t : ℝ} (ht : 5000 ≤ t) :
    1/(64*(t-step t)^2) ≤ (101/100)/(64*t^2) := by
  have hh := step_bounds ht
  have hq : (999/1000)*t ≤ t-step t := by linarith
  have hq0 : 0 < t-step t := by linarith
  have hsq := sq_le_sq₀ (show 0 ≤ (999/1000 : ℝ)*t by positivity)
    (show 0 ≤ t-step t by linarith) |>.mpr hq
  apply (div_le_div_iff₀ (by positivity : 0 < 64*(t-step t)^2) (by positivity)).mpr
  nlinarith [sq_nonneg t]

/-- The forward error and exponential costs fit the target Chebyshev allowance. -/
theorem forward_loss {t : ℝ} (ht : 0 < t) :
    (101/100)*(step t)^2+(201/100)/(64*t^2) ≤ (2/5)*step t/t := by
  unfold step
  field_simp
  norm_num

/-- The backward error, exponential and linear costs fit the same allowance. -/
theorem backward_loss {t : ℝ} (ht : 0 < t) :
    (step t)^2+(201/100)/(64*t^2)+step t/(100*t) ≤ (2/5)*step t/t := by
  unfold step
  field_simp
  norm_num

/-- The elementary linear constant has its actual nonnegative sign. -/
theorem log_constant_nonneg : 0 ≤ log (2*Real.pi) := log_nonneg (by linarith [pi_gt_three])

/-- The full linear term is paid at the actual starting point. -/
theorem log_constant_le {t : ℝ} (ht : 5000 ≤ t) : log (2*Real.pi) ≤ exp t/(100*t) := by
  have hc : log (2*Real.pi) ≤ 4 := by
    rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) pi_ne_zero]
    have h2 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have hp := log_le_sub_one_of_pos pi_pos
    linarith [pi_lt_four]
  apply hc.trans
  apply (le_div_iff₀ (by positivity : 0 < 100*t)).mpr
  have he := pow_div_factorial_le_exp t (by linarith : 0 ≤ t) 2
  norm_num [Nat.factorial] at he
  nlinarith

/-- Prime powers beyond the primes cost less than a further one-percent allowance. -/
theorem prime_power_cost {t : ℝ} (ht : 5000 ≤ t) :
    2*exp (t/2)*t ≤ exp t/(100*t) := by
  have ht0 : 0 < t := by linarith
  have hh := pow_div_factorial_le_exp (t/2) (by positivity : 0 ≤ t/2) 4
  norm_num [Nat.factorial] at hh
  have hpow : 200*t^2 ≤ exp (t/2) := by nlinarith [sq_nonneg (t^2-76800)]
  have hm := mul_le_mul_of_nonneg_left hpow (exp_nonneg (t/2))
  have he : exp (t/2)*exp (t/2) = exp t := by rw [← exp_add]; congr 1; ring
  rw [he] at hm
  apply (le_div_iff₀ (by positivity : 0 < 100*t)).mpr
  nlinarith only [hm]

end
end RiemannGaussian.RosserSchoenfeldChebyshevBudget
