/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.DerivativeRecursionBudget

/-!
# Exact exponents in the uniform derivative bound

At derivative order `k+2` the scale exponent is `1/(2^(k+2)-2)`.
The amplitude exponent halves at each step, while the complementary
length exponent approaches one. Their exact recurrence identities
control every real-power manipulation in the analytic shift choice.
-/

namespace RiemannGaussian.DerivativePowerExponents
noncomputable section

/-- The positive lower-derivative-scale exponent at order `k+2`. -/
def alpha (k : ℕ) : ℝ := 1 / ((2 : ℝ) ^ (k + 2) - 2)

/-- The exponent of the upper/lower derivative ratio. -/
def amp (k : ℕ) : ℝ := 1 / (2 : ℝ) ^ k

/-- The exponent of the length in the complementary error term. -/
def beta (k : ℕ) : ℝ := 1 - amp k

/-- The scale denominator stays at least two at every order. -/
theorem denominator_ge_two (k : ℕ) : 2 ≤ (2 : ℝ) ^ (k + 2) - 2 := by
  have h : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  rw [pow_add]
  norm_num
  linarith

/-- The scale exponent is strictly positive. -/
theorem alpha_pos (k : ℕ) : 0 < alpha k := by
  unfold alpha
  have h := denominator_ge_two k
  positivity

/-- All scale exponents lie below the integrable half-power endpoint. -/
theorem alpha_le_half (k : ℕ) : alpha k ≤ 1 / 2 := by
  have h := denominator_ge_two k
  unfold alpha
  apply (div_le_iff₀ (by linarith : 0 < (2 : ℝ) ^ (k + 2) - 2)).mpr
  linarith

/-- The base scale exponent is exactly one half. -/
theorem alpha_zero : alpha 0 = 1 / 2 := by norm_num [alpha]

/-- The scale exponent obeys the exact differencing recurrence. -/
theorem alpha_succ (k : ℕ) : alpha (k + 1) = alpha k / (2 + 2 * alpha k) := by
  have h := denominator_ge_two k
  unfold alpha
  rw [show k + 1 + 2 = (k + 2) + 1 by omega, pow_succ]
  have hP : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hB : -1 + (2 : ℝ) ^ k * 4 ≠ 0 := by nlinarith
  field_simp
  ring_nf
  field_simp

/-- The shift scale balances the leading powers exactly. -/
theorem alpha_balance (k : ℕ) : alpha k * (1 - 2 * alpha (k + 1)) = 2 * alpha (k + 1) := by
  rw [alpha_succ]
  have h := alpha_pos k
  field_simp
  ring

/-- The amplitude exponent is positive at every finite order. -/
theorem amp_pos (k : ℕ) : 0 < amp k := by
  unfold amp
  positivity

/-- The amplitude exponent never exceeds one. -/
theorem amp_le_one (k : ℕ) : amp k ≤ 1 := by
  unfold amp
  exact (div_le_one (by positivity : 0 < (2 : ℝ) ^ k)).mpr (one_le_pow₀ (by norm_num))

/-- The base amplitude exponent is one. -/
theorem amp_zero : amp 0 = 1 := by norm_num [amp]

/-- Differencing halves the amplitude exponent exactly. -/
theorem amp_succ (k : ℕ) : amp (k + 1) = amp k / 2 := by
  unfold amp
  rw [pow_succ]
  ring

/-- The complementary length exponent is nonnegative. -/
theorem beta_nonneg (k : ℕ) : 0 ≤ beta k := sub_nonneg.mpr (amp_le_one k)

/-- The complementary length exponent is at most one. -/
theorem beta_le_one (k : ℕ) : beta k ≤ 1 := by
  unfold beta
  linarith [amp_pos k]

/-- The base complementary term has no length power. -/
theorem beta_zero : beta 0 = 0 := by norm_num [beta, amp]

/-- The complementary length exponent follows the exact square-root
recurrence from the full differencing inequality. -/
theorem beta_succ (k : ℕ) : beta (k + 1) = (beta k + 1) / 2 := by
  unfold beta
  rw [amp_succ]
  ring

end
end RiemannGaussian.DerivativePowerExponents
