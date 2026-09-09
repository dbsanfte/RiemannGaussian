/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseExactFamily

/-!
# Eliminating the shift parameter from the signed phase source

For a fixed coefficient family, the selected-zero source minus the real
pole has an exact square deficit. When the first coefficient exceeds the
positive constant coefficient, this identifies the unique best positive
shift symbolically. Higher frequencies still constrain the feasibility
and height cost of the family; they are not discarded from those objects.
-/

namespace RiemannGaussian

noncomputable section

/-- The signed selected-zero source at an arbitrary positive shift ratio. -/
def phaseShiftSource (a₀ a₁ κ : ℝ) : ℝ := a₁ / (κ + 1) - a₀ / κ

/-- The existing fixed-shift source is this same signed pole expression. -/
theorem phaseShiftSource_fixed (a : ℕ → ℝ) :
    phaseShiftSource (a 0) (a 1) (13 / 4) = phaseContactSource a := by
  unfold phaseShiftSource phaseContactSource
  ring

private theorem shift_square_identity (u v κ : ℝ) (hκ : 0 < κ) :
    (v - u) ^ 2 - phaseShiftSource (u ^ 2) (v ^ 2) κ =
      ((v - u) * κ - u) ^ 2 / (κ * (κ + 1)) := by
  have h0 : κ ≠ 0 := ne_of_gt hκ
  have h1 : κ + 1 ≠ 0 := by linarith
  unfold phaseShiftSource
  field_simp
  ring

/-- The exact deficit from the best possible fixed-family source is a
nonnegative square, retaining the selected-zero and real-pole signs. -/
theorem phaseShiftSource_square_deficit {a₀ a₁ κ : ℝ} (h₀ : 0 ≤ a₀) (h₁ : 0 ≤ a₁) (hκ : 0 < κ) :
    (Real.sqrt a₁ - Real.sqrt a₀) ^ 2 - phaseShiftSource a₀ a₁ κ =
      ((Real.sqrt a₁ - Real.sqrt a₀) * κ - Real.sqrt a₀) ^ 2 / (κ * (κ + 1)) := by
  simpa only [Real.sq_sqrt h₀, Real.sq_sqrt h₁] using
    shift_square_identity (Real.sqrt a₀) (Real.sqrt a₁) κ hκ

/-- No positive shift can exceed the symbolic source envelope of a
fixed coefficient family. -/
theorem phaseShiftSource_le_envelope {a₀ a₁ κ : ℝ} (h₀ : 0 ≤ a₀) (h₁ : 0 ≤ a₁) (hκ : 0 < κ) :
    phaseShiftSource a₀ a₁ κ ≤ (Real.sqrt a₁ - Real.sqrt a₀) ^ 2 := by
  have hs := phaseShiftSource_square_deficit h₀ h₁ hκ
  have hnonneg : 0 ≤ ((Real.sqrt a₁ - Real.sqrt a₀) * κ - Real.sqrt a₀) ^ 2 / (κ * (κ + 1)) := by
    positivity
  linarith

/-- The positive shift attaining the fixed-family source envelope. -/
def phaseSourceOptimalShift (a₀ a₁ : ℝ) : ℝ := Real.sqrt a₀ / (Real.sqrt a₁ - Real.sqrt a₀)

/-- The symbolic optimum is a legitimate positive shift when the first
coefficient is larger than the positive constant coefficient. -/
theorem phaseSourceOptimalShift_pos {a₀ a₁ : ℝ} (h₀ : 0 < a₀) (h₁ : a₀ < a₁) :
    0 < phaseSourceOptimalShift a₀ a₁ := by
  unfold phaseSourceOptimalShift
  exact div_pos (Real.sqrt_pos.mpr h₀) (sub_pos.mpr (Real.sqrt_lt_sqrt h₀.le h₁))

/-- The symbolic shift actually attains the envelope; this is an exact
formula, not a numerical stationarity test. -/
theorem phaseShiftSource_optimalShift {a₀ a₁ : ℝ} (h₀ : 0 < a₀) (h₁ : a₀ < a₁) :
    phaseShiftSource a₀ a₁ (phaseSourceOptimalShift a₀ a₁) =
      (Real.sqrt a₁ - Real.sqrt a₀) ^ 2 := by
  have hd : Real.sqrt a₁ - Real.sqrt a₀ ≠ 0 := ne_of_gt (sub_pos.mpr (Real.sqrt_lt_sqrt h₀.le h₁))
  have h := phaseShiftSource_square_deficit h₀.le (h₀.trans h₁).le (phaseSourceOptimalShift_pos h₀ h₁)
  simp only [phaseSourceOptimalShift, mul_div_cancel₀ _ hd, sub_self, zero_pow (by decide : 2 ≠ 0), zero_div] at h
  unfold phaseSourceOptimalShift
  linarith

/-- Equality in the source envelope identifies a unique positive shift.
Thus a joint phase/shift optimizer can eliminate the shift variable using
the constant and first coefficients, while retaining the full kernel. -/
theorem phaseShiftSource_eq_envelope_iff {a₀ a₁ κ : ℝ}
    (h₀ : 0 < a₀) (h₁ : a₀ < a₁) (hκ : 0 < κ) :
    phaseShiftSource a₀ a₁ κ = (Real.sqrt a₁ - Real.sqrt a₀) ^ 2 ↔ κ = phaseSourceOptimalShift a₀ a₁ := by
  constructor
  · intro he
    have hd : Real.sqrt a₁ - Real.sqrt a₀ ≠ 0 := ne_of_gt (sub_pos.mpr (Real.sqrt_lt_sqrt h₀.le h₁))
    have h := phaseShiftSource_square_deficit h₀.le (h₀.trans h₁).le hκ
    rw [he, sub_self, eq_comm, div_eq_zero_iff] at h
    have hp : κ * (κ + 1) ≠ 0 := by positivity
    have hs := sq_eq_zero_iff.mp (h.resolve_right hp)
    unfold phaseSourceOptimalShift
    apply (eq_div_iff hd).mpr
    linarith
  · rintro rfl
    exact phaseShiftSource_optimalShift h₀ h₁

end

end RiemannGaussian
