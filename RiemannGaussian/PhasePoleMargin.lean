/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaAngularPhaseAllowance

/-!
# Exact optimization of the selected source against the real pole

For any nonnegative constant and selected-phase coefficients, the entire
loss from a chosen center shift is one explicit square. When the selected
coefficient exceeds the positive constant coefficient, the unique best
shift and the exact source margin follow symbolically.
-/

namespace RiemannGaussian.PhasePoleMargin
noncomputable section

/-- The selected reciprocal-distance source minus the real pole,
at a center displaced by r times the proposed zero margin. -/
def margin (w₀ w₁ r : ℝ) : ℝ := w₁ / (r + 1) - w₀ / r

/-- The exact largest available source margin when w₁ exceeds w₀. -/
def optimum (w₀ w₁ : ℝ) : ℝ := (Real.sqrt w₁ - Real.sqrt w₀) ^ 2

/-- The exact center shift at which the pole-source margin is largest. -/
def optimalShift (w₀ w₁ : ℝ) : ℝ :=
  Real.sqrt w₀ / (Real.sqrt w₁ - Real.sqrt w₀)

/-- Every shift loss is exactly a nonnegative square over its true
positive denominator, before any inequality is taken. -/
theorem loss_identity {w₀ w₁ r : ℝ} (h₀ : 0 ≤ w₀) (h₁ : 0 ≤ w₁) (hr : 0 < r) :
    optimum w₀ w₁ - margin w₀ w₁ r =
      ((Real.sqrt w₁ - Real.sqrt w₀) * r - Real.sqrt w₀) ^ 2 / (r * (r + 1)) := by
  have he (p q : ℝ) : (q - p) ^ 2 - (q ^ 2 / (r + 1) - p ^ 2 / r) =
      ((q - p) * r - p) ^ 2 / (r * (r + 1)) := by
    field_simp
    ring
  simpa only [optimum, margin, Real.sq_sqrt h₀, Real.sq_sqrt h₁] using
    he (Real.sqrt w₀) (Real.sqrt w₁)

/-- The exact square identity bounds every positive center shift. -/
theorem margin_le_optimum {w₀ w₁ r : ℝ} (h₀ : 0 ≤ w₀) (h₁ : 0 ≤ w₁) (hr : 0 < r) :
    margin w₀ w₁ r ≤ optimum w₀ w₁ := by
  have he := loss_identity h₀ h₁ hr
  have hn : 0 ≤ ((Real.sqrt w₁ - Real.sqrt w₀) * r - Real.sqrt w₀) ^ 2 /
      (r * (r + 1)) := by positivity
  linarith

/-- A strictly larger selected coefficient gives a positive exact
optimizing shift whenever the constant coefficient is positive. -/
theorem optimalShift_pos {w₀ w₁ : ℝ} (h₀ : 0 < w₀) (h₁ : w₀ < w₁) :
    0 < optimalShift w₀ w₁ := by
  exact div_pos (Real.sqrt_pos.mpr h₀) (sub_pos.mpr (Real.sqrt_lt_sqrt h₀.le h₁))

/-- The symbolic shift attains the exact largest source margin. -/
theorem margin_optimalShift {w₀ w₁ : ℝ} (h₀ : 0 < w₀) (h₁ : w₀ < w₁) :
    margin w₀ w₁ (optimalShift w₀ w₁) = optimum w₀ w₁ := by
  have hp : 0 < Real.sqrt w₁ - Real.sqrt w₀ :=
    sub_pos.mpr (Real.sqrt_lt_sqrt h₀.le h₁)
  have he := loss_identity h₀.le (h₀.trans h₁).le (optimalShift_pos h₀ h₁)
  have hz : (Real.sqrt w₁ - Real.sqrt w₀) * optimalShift w₀ w₁ - Real.sqrt w₀ = 0 := by
    unfold optimalShift
    field_simp
    ring
  rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div] at he
  linarith

/-- Equality at a positive shift forces the unique symbolic optimizer. -/
theorem margin_eq_optimum_iff {w₀ w₁ r : ℝ}
    (h₀ : 0 < w₀) (h₁ : w₀ < w₁) (hr : 0 < r) :
    margin w₀ w₁ r = optimum w₀ w₁ ↔ r = optimalShift w₀ w₁ := by
  constructor
  · intro h
    have hp : 0 < Real.sqrt w₁ - Real.sqrt w₀ :=
      sub_pos.mpr (Real.sqrt_lt_sqrt h₀.le h₁)
    have he := loss_identity h₀.le (h₀.trans h₁).le hr
    rw [h, sub_self] at he
    have hden : r * (r + 1) ≠ 0 := by positivity
    have hz := (div_eq_zero_iff.mp he.symm).resolve_right hden
    have hlin := sq_eq_zero_iff.mp hz
    apply (eq_div_iff hp.ne').mpr
    nlinarith only [hlin]
  · rintro rfl
    exact margin_optimalShift h₀ h₁

end
end RiemannGaussian.PhasePoleMargin
