/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldLargeSmoothed
import RiemannGaussian.RosserSchoenfeldDesmoothing
import RiemannGaussian.RosserSchoenfeldChebyshevBudget

/-!
# Actual quantitative Chebyshev bounds above the published large cutoff

The complete smoothed prime formula, the proved zero-free region and the
complete high-zero tail give the smoothed error. Monotone desmoothing
and the actual prime-power allowance then bound `psi` and `theta`.
No prime-error or finite-verification premise is assumed.
-/

namespace RiemannGaussian.RosserSchoenfeldLargeChebyshev
noncomputable section
open Real
open RosserSchoenfeldPrimePrimitive RosserSchoenfeldChebyshevBudget

private theorem prime_upper {t : ℝ} (ht : 4900 ≤ t) :
    value t ≤ exp t-1-log (2*Real.pi)*t+exp t/(64*t^2) := by
  have hh := (abs_lt.mp (RosserSchoenfeldLargeSmoothed.abs_prime_sub_main_lt ht)).2
  linarith

private theorem prime_lower {t : ℝ} (ht : 4900 ≤ t) :
    exp t-1-log (2*Real.pi)*t-exp t/(64*t^2) ≤ value t := by
  have hh := (abs_lt.mp (RosserSchoenfeldLargeSmoothed.abs_prime_sub_main_lt ht)).1
  linarith

private theorem forward_error {t : ℝ} (ht : 5000 ≤ t) :
    exp (t+step t)/(64*(t+step t)^2) ≤ (101/100)*exp t/(64*t^2) := by
  have hh := step_bounds ht
  have ht0 : 0 < t := by linarith
  calc
    _ ≤ exp (t+step t)/(64*t^2) :=
      div_le_div_of_nonneg_left (exp_nonneg _) (by positivity) (by nlinarith)
    _ = exp t*exp (step t)/(64*t^2) := by rw [exp_add]
    _ ≤ exp t*(101/100)/(64*t^2) := by gcongr; exact exp_small hh.1.le hh.2
    _ = _ := by ring

private theorem backward_error {t : ℝ} (ht : 5000 ≤ t) :
    exp (t-step t)/(64*(t-step t)^2) ≤ (101/100)*exp t/(64*t^2) := by
  have hh := step_bounds ht
  have hq0 : 0 < t-step t := by linarith
  calc
    _ ≤ exp t/(64*(t-step t)^2) := by gcongr; linarith
    _ = exp t*(1/(64*(t-step t)^2)) := by ring
    _ ≤ exp t*((101/100)/(64*t^2)) :=
      mul_le_mul_of_nonneg_left (backward_denominator ht) (exp_nonneg t)
    _ = _ := by ring

/-- The actual Chebyshev psi sum obeys an explicit upper bound from `exp(5000)`. -/
theorem psi_upper {t : ℝ} (ht : 5000 ≤ t) :
    Chebyshev.psi (exp t) ≤ exp t*(1+(2/5)/t) := by
  have ht0 : 0 < t := by linarith
  have hh := step_bounds ht
  have hi := RosserSchoenfeldDesmoothing.prime_increment_lower
    (a := t) (b := t+step t) (by linarith)
  have hu := prime_upper (shifted_domain ht).2
  have hl := prime_lower (show 4900 ≤ t by linarith)
  have he := forward_error ht
  rw [exp_add] at hu he
  have hx := mul_le_mul_of_nonneg_left (exp_forward hh.1.le hh.2) (exp_nonneg t)
  have hc := mul_nonneg log_constant_nonneg hh.1.le
  have hb := mul_le_mul_of_nonneg_left (forward_loss ht0) (exp_nonneg t)
  apply (mul_le_mul_iff_right₀ hh.1).mp
  ring_nf at hi hu hl he hx hc hb ⊢
  nlinarith only [hi, hu, hl, he, hx, hc, hb]

/-- The actual Chebyshev psi sum obeys the matching explicit lower bound. -/
theorem psi_lower {t : ℝ} (ht : 5000 ≤ t) :
    exp t*(1-(2/5)/t) ≤ Chebyshev.psi (exp t) := by
  have ht0 : 0 < t := by linarith
  have hh := step_bounds ht
  have hi := RosserSchoenfeldDesmoothing.prime_increment_upper
    (a := t-step t) (b := t) (by linarith)
  have hu := prime_upper (shifted_domain ht).1
  have hl := prime_lower (show 4900 ≤ t by linarith)
  have he := backward_error ht
  rw [sub_eq_add_neg, exp_add] at hu he
  have hx := mul_le_mul_of_nonneg_left (exp_backward hh.1.le) (exp_nonneg t)
  have hc := mul_le_mul_of_nonneg_right (log_constant_le ht) hh.1.le
  have hb := mul_le_mul_of_nonneg_left (backward_loss ht0) (exp_nonneg t)
  apply (mul_le_mul_iff_right₀ hh.1).mp
  ring_nf at hi hu hl he hx hc hb ⊢
  nlinarith only [hi, hu, hl, he, hx, hc, hb]

/-- A two-sided error estimate for the actual psi function, with an explicit start. -/
theorem abs_psi_sub_exp_le {t : ℝ} (ht : 5000 ≤ t) :
    |Chebyshev.psi (exp t)-exp t| ≤ (2/5)*exp t/t := by
  have hl := psi_lower ht
  have hu := psi_upper ht
  rw [show exp t*(1-(2/5)/t) = exp t-(2/5)*exp t/t by ring] at hl
  rw [show exp t*(1+(2/5)/t) = exp t+(2/5)*exp t/t by ring] at hu
  apply abs_le.mpr
  constructor <;> linarith

private theorem sqrt_exp (t : ℝ) : sqrt (exp t) = exp (t/2) := by
  apply (sq_eq_sq₀ (sqrt_nonneg _) (exp_nonneg _)).mp
  rw [sq_sqrt (exp_nonneg _), pow_two, ← exp_add]
  congr 1
  ring

/-- The actual theta error, after all prime powers have been paid. -/
theorem abs_theta_sub_exp_le {t : ℝ} (ht : 5000 ≤ t) :
    |Chebyshev.theta (exp t)-exp t| ≤ (41/100)*exp t/t := by
  have hx : 1 ≤ exp t := one_le_exp_iff.mpr (by linarith)
  have hp := Chebyshev.psi_sub_theta_le hx
  rw [sqrt_exp, log_exp] at hp
  have hp' : |Chebyshev.theta (exp t)-Chebyshev.psi (exp t)| ≤ exp t/(100*t) := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _))]
    exact hp.trans (prime_power_cost ht)
  have hh := abs_add_le (Chebyshev.theta (exp t)-Chebyshev.psi (exp t))
    (Chebyshev.psi (exp t)-exp t)
  rw [sub_add_sub_cancel] at hh
  have hpsi := abs_psi_sub_exp_le ht
  apply hh.trans
  calc
    _ ≤ exp t/(100*t)+(2/5)*exp t/t := add_le_add hp' hpsi
    _ = _ := by ring

/-- The published large-range theta allowance is discharged for actual primes.
The stronger proved constant is `41/100`; the source requires `47/100`. -/
theorem abs_theta_sub_self_lt_published {x : ℝ} (hx : exp 5000 ≤ x) :
    |Chebyshev.theta x-x| < (47/100)*x/log x := by
  have hx0 : 0 < x := (exp_pos 5000).trans_le hx
  have ht : 5000 ≤ log x := (le_log_iff_exp_le hx0).mpr hx
  have hh := abs_theta_sub_exp_le ht
  rw [exp_log hx0] at hh
  apply hh.trans_lt
  apply div_lt_div_of_pos_right _ (by linarith : 0 < log x)
  nlinarith

end
end RiemannGaussian.RosserSchoenfeldLargeChebyshev
