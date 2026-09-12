/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.DerivativePowerExponents

/-!
# Near-one lines and exact derivative transition scales

The leading term of the derivative estimate is independent of block size
on the line `1-(k+2)*alpha k`. The complementary term determines an exact
transition exponent. These identities retain the derivative order and
both powers before any block range is selected.
-/

namespace RiemannGaussian.DirichletPowerParameters
noncomputable section
open DerivativePowerExponents

/-- The real coordinate balancing the leading block power at order `k+2`. -/
def line (k : ℕ) : ℝ := 1 - ((k : ℝ) + 2) * alpha k

/-- The complementary block exponent on the balanced line. -/
def slope (k : ℕ) : ℝ := 2 * ((k : ℝ) + 2) * alpha k - amp k

/-- The exact height exponent where the complementary term reaches the
same size as the leading term. -/
def transition (k : ℕ) : ℝ := 1 / ((k : ℝ) + amp k)

/-- The derivative-scale denominator dominates the order itself. -/
theorem denominator_ge_order (k : ℕ) : (k : ℝ) + 2 ≤ (2 : ℝ) ^ (k + 2) - 2 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by omega, pow_succ]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- The order times its shrinking scale exponent never exceeds one. -/
theorem order_mul_alpha_le_one (k : ℕ) : ((k : ℝ) + 2) * alpha k ≤ 1 := by
  have hd := denominator_ge_two k
  unfold alpha
  rw [mul_one_div]
  apply (div_le_one (by linarith)).mpr
  exact denominator_ge_order k

/-- Every balanced line is in the closed nonnegative half-plane. -/
theorem line_nonneg (k : ℕ) : 0 ≤ line k := by
  unfold line
  linarith [order_mul_alpha_le_one k]

/-- Every finite balanced line remains strictly left of one. -/
theorem line_lt_one (k : ℕ) : line k < 1 := by
  unfold line
  have hp : 0 < ((k : ℝ) + 2) * alpha k := mul_pos (by positivity) (alpha_pos k)
  linarith

/-- At every order at least three, the balanced line lies on or to the
right of the critical line. -/
theorem half_le_line_succ (k : ℕ) : 1 / 2 ≤ line (k + 1) := by
  have hb : ∀ j : ℕ, 2 * ((j : ℝ) + 3) + 2 ≤ (2 : ℝ) ^ (j + 3) := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      rw [show j + 1 + 3 = (j + 3) + 1 by omega, pow_succ]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hd := denominator_ge_two (k + 1)
  have h : ((k : ℝ) + 3) * alpha (k + 1) ≤ 1 / 2 := by
    unfold alpha
    rw [mul_one_div]
    apply (div_le_iff₀ (by linarith)).mpr
    have h := hb k
    rw [show k + 1 + 2 = k + 3 by omega]
    linarith
  unfold line
  push_cast
  linarith

/-- The amplitude and scale exponents obey an exact common-denominator
identity needed to balance the complementary term. -/
theorem amp_alpha_identity (k : ℕ) : amp k * (1 + 2 * alpha k) = 4 * alpha k := by
  have hp : (2 : ℝ) ^ k ≠ 0 := by positivity
  have hd := denominator_ge_two k
  have hP : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hD : -2 + (2 : ℝ) ^ k * 4 ≠ 0 := by nlinarith
  unfold amp alpha
  rw [pow_add]
  norm_num
  field_simp
  ring_nf
  field_simp
  ring

/-- The complementary exponent retains its exact positive factorization. -/
theorem slope_eq (k : ℕ) : slope k = 2 * alpha k * ((k : ℝ) + amp k) := by
  unfold slope
  nlinarith [amp_alpha_identity k]

/-- The complementary block exponent is strictly positive at every order. -/
theorem slope_pos (k : ℕ) : 0 < slope k := by
  rw [slope_eq]
  have hp := amp_pos k
  have ha := alpha_pos k
  positivity

/-- The transition exponent is positive. -/
theorem transition_pos (k : ℕ) : 0 < transition k := by
  unfold transition
  have hp := amp_pos k
  positivity

/-- At the transition scale the complementary height power is exactly
twice the scale exponent, before removing its reciprocal-height factor. -/
theorem transition_balance (k : ℕ) : transition k * slope k = 2 * alpha k := by
  rw [transition, slope_eq]
  have hp : (k : ℝ) + amp k ≠ 0 := ne_of_gt (by have h := amp_pos k; positivity)
  field_simp

end
end RiemannGaussian.DirichletPowerParameters
