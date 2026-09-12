/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.DirichletPowerParameters
import RiemannGaussian.LogarithmicDerivativeFamily

/-!
# Uniform factorial costs in logarithmic derivative estimates

The factorial and dyadic denominator are retained as one exact factor.
Both its positive and negative shrinking powers are bounded uniformly in
the derivative order. The actual derivative scale is then rewritten in
separate height and block powers, with no factorial hidden in a constant.
-/

namespace RiemannGaussian.DirichletPowerCoefficients
noncomputable section
open DerivativePowerExponents DirichletPowerParameters LogarithmicDerivativeFamily

/-- The exact factorial and dyadic factor in the lower derivative scale. -/
def factor (k : ℕ) : ℝ := ((k + 1).factorial : ℝ) / (2 : ℝ) ^ (k + 2)

/-- The exact factorial factor is positive at every derivative order. -/
theorem factor_pos (k : ℕ) : 0 < factor k := by
  unfold factor
  positivity

/-- A coarse double-exponential bound for the factorial, proved for
every order and used only under its shrinking real exponent. -/
theorem factorial_le_double_power (k : ℕ) : (k + 1).factorial ≤ (2 : ℕ) ^ (2 ^ k) := by
  have hlin : ∀ j : ℕ, j + 1 ≤ (2 : ℕ) ^ j := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih => rw [pow_succ]; omega
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hk : k + 2 ≤ (2 : ℕ) ^ (2 ^ k) :=
      (hlin (k + 1)).trans (pow_le_pow_right₀ (by norm_num) (hlin k))
    rw [Nat.factorial_succ]
    calc
      _ ≤ ((2 : ℕ) ^ (2 ^ k)) * ((2 : ℕ) ^ (2 ^ k)) := Nat.mul_le_mul hk ih
      _ = _ := by rw [← pow_add, pow_succ]; congr 1; omega

/-- Even the unscaled factorial has a shrinking exponent bounded by one
in the auxiliary double-exponential comparison. -/
theorem double_power_exponent_le_one (k : ℕ) : (2 : ℝ) ^ k * alpha k ≤ 1 := by
  have hP : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hd := denominator_ge_two k
  unfold alpha
  rw [mul_one_div]
  apply (div_le_one (by linarith)).mpr
  rw [pow_add]
  norm_num
  nlinarith

/-- The exact factorial factor raised to its positive scale exponent
costs at most two, uniformly in the order. -/
theorem factor_positive_power_le_two (k : ℕ) : factor k ^ alpha k ≤ 2 := by
  have hf : ((k + 1).factorial : ℝ) ≤ (2 : ℝ) ^ (2 ^ k) := by
    exact_mod_cast factorial_le_double_power k
  have hfac : factor k ≤ (2 : ℝ) ^ (2 ^ k) := by
    apply (div_le_self (by positivity : (0 : ℝ) ≤ (k + 1).factorial)
      (one_le_pow₀ (by norm_num))).trans hf
  have he : (((2 : ℕ) ^ k : ℕ) : ℝ) * alpha k ≤ 1 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using double_power_exponent_le_one k
  calc
    _ ≤ ((2 : ℝ) ^ (2 ^ k)) ^ alpha k :=
      Real.rpow_le_rpow (factor_pos k).le hfac (alpha_pos k).le
    _ = (2 : ℝ) ^ ((((2 : ℕ) ^ k : ℕ) : ℝ) * alpha k) :=
      (Real.rpow_natCast_mul (by norm_num) _ _).symm
    _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) he
    _ = 2 := Real.rpow_one _

/-- The reciprocal factorial factor has the same uniform cost, with its
actual positive denominator retained. -/
theorem factor_negative_power_le_two (k : ℕ) : factor k ^ (-alpha k) ≤ 2 := by
  have hf : (1 : ℝ) ≤ (k + 1).factorial := by
    exact_mod_cast (Nat.factorial_pos (k + 1))
  have hi : 1 / factor k ≤ (2 : ℝ) ^ (k + 2) := by
    unfold factor
    rw [one_div_div]
    exact div_le_self (by positivity) hf
  have he : ((k + 2 : ℕ) : ℝ) * alpha k ≤ 1 := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using order_mul_alpha_le_one k
  calc
    _ = (1 / factor k) ^ alpha k := by
      rw [Real.div_rpow (by norm_num) (factor_pos k).le, Real.one_rpow,
        Real.rpow_neg (factor_pos k).le, one_div]
    _ ≤ ((2 : ℝ) ^ (k + 2)) ^ alpha k :=
      Real.rpow_le_rpow (one_div_pos.mpr (factor_pos k)).le hi (alpha_pos k).le
    _ = (2 : ℝ) ^ (((k + 2 : ℕ) : ℝ) * alpha k) :=
      (Real.rpow_natCast_mul (by norm_num) _ _).symm
    _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) he
    _ = 2 := Real.rpow_one _

/-- The literal lower derivative scale separates exactly into its
factorial factor, height and block size. -/
theorem lowerScale_eq_factor (t X : ℝ) (k : ℕ) :
    lowerScale t X k = factor k * t / X ^ (k + 2) := by
  unfold lowerScale factor
  rw [mul_pow]
  ring

/-- Every real power of the actual derivative scale retains its exact
factorial, height and block powers. -/
theorem scale_power (k : ℕ) {t X : ℝ} (ht : 0 < t) (hX : 0 < X) (q : ℝ) :
    lowerScale t X k ^ q = factor k ^ q * t ^ q * X ^ (-((k : ℝ) + 2) * q) := by
  rw [lowerScale_eq_factor,
    Real.div_rpow (mul_nonneg (factor_pos k).le ht.le) (by positivity),
    Real.mul_rpow (factor_pos k).le ht.le,
    ← Real.rpow_natCast_mul hX.le, div_eq_mul_inv, ← Real.rpow_neg hX.le]
  congr 2
  push_cast
  ring

end
end RiemannGaussian.DirichletPowerCoefficients
