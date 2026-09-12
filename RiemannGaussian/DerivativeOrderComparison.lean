/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.DirichletPowerParameters

/-!
# Exact comparisons between derivative orders

The scale exponents and balanced-line displacements form a discrete
curve whose adjacent slopes are the exact transition exponents. Their
monotonicity gives a comparison for every pair of orders, allowing both
block powers to be controlled when the derivative order changes.
-/

namespace RiemannGaussian.DerivativeOrderComparison
noncomputable section
open DerivativePowerExponents DirichletPowerParameters

/-- The exact displacement of the balanced line from real part one. -/
def delta (k : ℕ) : ℝ := ((k : ℝ) + 2) * alpha k

/-- The displacement is exactly one minus the balanced line. -/
theorem delta_eq_one_sub_line (k : ℕ) : delta k = 1 - line k := by
  unfold delta line
  ring

/-- Every finite balanced line has positive displacement. -/
theorem delta_pos (k : ℕ) : 0 < delta k :=
  mul_pos (by positivity) (alpha_pos k)

/-- One differencing step decreases the scale exponent by at least a
factor of two. -/
theorem alpha_succ_le_half (k : ℕ) : alpha (k + 1) ≤ alpha k / 2 := by
  rw [alpha_succ]
  exact div_le_div_of_nonneg_left (alpha_pos k).le (by norm_num)
    (by linarith [alpha_pos k])

/-- The balanced-line displacements decrease with every order step. -/
theorem delta_succ_le (k : ℕ) : delta (k + 1) ≤ delta k := by
  have h := mul_le_mul_of_nonneg_left (alpha_succ_le_half k)
    (show 0 ≤ (k : ℝ) + 3 by positivity)
  have hp : 0 ≤ ((k : ℝ) + 1) * alpha k := mul_nonneg (by positivity) (alpha_pos k).le
  unfold delta
  push_cast
  nlinarith

/-- The balanced-line displacement is antitone over all derivative orders. -/
theorem delta_antitone : Antitone delta := antitone_nat_of_succ_le delta_succ_le

/-- The transition exponents decrease at each order step. -/
theorem transition_succ_le (k : ℕ) : transition (k + 1) ≤ transition k := by
  unfold transition
  rw [amp_succ]
  push_cast
  apply one_div_le_one_div_of_le
    (show 0 < (k : ℝ) + amp k by have h := amp_pos k; positivity)
  linarith [amp_le_one k]

/-- The exact transition exponent is antitone over all orders. -/
theorem transition_antitone : Antitone transition :=
  antitone_nat_of_succ_le transition_succ_le

/-- The second-derivative transition reaches the height itself. -/
theorem transition_zero : transition 0 = 1 := by norm_num [transition, amp]

/-- The adjacent secant of scale exponent against line displacement
is exactly the next transition exponent. -/
theorem adjacent_identity (k : ℕ) : alpha k - alpha (k + 1) =
    transition (k + 1) * (delta k - delta (k + 1)) := by
  have ha := alpha_pos k
  have hrec : alpha (k + 1) * (2 + 2 * alpha k) = alpha k := by
    rw [alpha_succ]
    field_simp
  have hp := amp_alpha_identity k
  have hd : (((k + 1 : ℕ) : ℝ) + amp (k + 1)) ≠ 0 := by
    have h := amp_pos (k + 1)
    positivity
  rw [show transition (k + 1) * (delta k - delta (k + 1)) =
    (delta k - delta (k + 1)) / (((k + 1 : ℕ) : ℝ) + amp (k + 1)) by
      unfold transition; ring]
  apply (eq_div_iff hd).mpr
  unfold delta
  rw [amp_succ]
  push_cast
  linear_combination (1 - amp k / 2) * hrec + (alpha (k + 1) / 2) * hp

/-- Every earlier-order transition chord lies below every later point
of the exact exponent curve. This is the common height-power comparison. -/
theorem order_comparison (j k : ℕ) (hjk : j ≤ k) :
    alpha j + transition (j + 1) * (delta k - delta j) ≤ alpha k := by
  induction k, hjk using Nat.le_induction with
  | base => simp
  | succ k hjk ih =>
    have ht := transition_antitone (Nat.succ_le_succ hjk)
    have hd : 0 ≤ delta k - delta (k + 1) := sub_nonneg.mpr (delta_succ_le k)
    have hm := mul_le_mul_of_nonneg_right ht hd
    have hi := adjacent_identity k
    nlinarith

/-- The displacement at each order dominates its amplitude exponent;
this keeps the complementary block power nonnegative. -/
theorem amp_le_delta (k : ℕ) : amp k ≤ delta k := by
  by_cases hk : 2 ≤ k
  · have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have h1 : 0 ≤ ((k : ℝ) - 2) * alpha k := mul_nonneg (by linarith) (alpha_pos k).le
    have h2 : 0 ≤ amp k * alpha k := mul_nonneg (amp_pos k).le (alpha_pos k).le
    have h := amp_alpha_identity k
    unfold delta
    nlinarith
  · have hklt : k < 2 := Nat.lt_of_not_ge hk
    interval_cases k <;> norm_num [delta, alpha, amp]

/-- Every positive derivative index gives a balanced line in the closed
right half of the critical strip. -/
theorem half_le_line (k : ℕ) (hk : 1 ≤ k) : 1 / 2 ≤ line k := by
  cases k with
  | zero => omega
  | succ k => exact half_le_line_succ k

end
end RiemannGaussian.DerivativeOrderComparison
