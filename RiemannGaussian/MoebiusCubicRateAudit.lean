/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MoebiusFiniteMellinRate

/-!
# Power limitation of the existing cubic contour envelope

The quantitative Möbius bounds save an exponential in the heat parameter,
but their arithmetic remainder grows exponentially in its cube. Optimizing
that parameter cannot turn these envelopes into a smaller fixed cutoff
power. The comparison is uniform over every nonnegative heat parameter,
including parameters for which the additive remainder has not been absorbed.

These are lower bounds for the proved upper-bound expressions, not lower
bounds for the actual signed Möbius sums. Stronger cancellation in those sums
is not excluded. Relative savings at the same cutoff power are also retained.
-/

open Filter
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- A finite-scale obstruction with the actual contour constant and minimum
heat parameter. When the coefficient and exponent comparisons hold, no
admissible cutoff can make this envelope beat the smaller source power. -/
theorem moebiusCubic_rateEnvelope_ge_lower_power_of_gap {a b C B X h : ℝ}
    (hBC : B ≤ C) (hC : 0 ≤ C) (hh : 22 ≤ h)
    (hgap : 1 / 968000000000000000 ≤ b - a)
    (hcut : Real.exp (moebiusFiniteContourCenter h) ≤ X) :
    B * X ^ a ≤ C * X ^ b * Real.exp (-h / 2) := by
  have hXp : 0 < X := (Real.exp_pos _).trans_le hcut
  have hδ : 0 ≤ b - a := by linarith
  have hs : (484 : ℝ) ≤ h ^ 2 := by nlinarith
  have hp := mul_le_mul_of_nonneg_left hs hδ
  have hunit : 1 ≤ 2 * 1000000000000000 * (b - a) * h ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hunit (by linarith : 0 ≤ h)
  have hheat : h / 2 ≤ (b - a) * moebiusFiniteContourCenter h := by
    unfold moebiusFiniteContourCenter
    nlinarith [hm]
  have hlog := (Real.le_log_iff_exp_le hXp).mpr hcut
  have hg := mul_le_mul_of_nonneg_left hlog hδ
  have hpow : X ^ a ≤ X ^ b * Real.exp (-h / 2) := by
    simp only [Real.rpow_def_of_pos hXp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ C * X ^ a := mul_le_mul_of_nonneg_right hBC (Real.rpow_nonneg hXp.le a)
    _ ≤ C * (X ^ b * Real.exp (-h / 2)) := mul_le_mul_of_nonneg_left hpow hC
    _ = _ := by ring

/-- A cubic admissibility cutoff forces every allowed heat parameter below
any fixed positive multiple of the logarithmic arithmetic scale eventually.
The threshold is independent of the choice of parameter. -/
theorem moebiusCubic_admissible_height_le_log {e X h : ℝ} (he : 0 < e)
    (hX : Real.exp ((1 + 1 / e) / e) ≤ X) (hh : 0 ≤ h)
    (hcut : Real.exp (moebiusFiniteContourCenter h) ≤ X) :
    h ≤ e * Real.log X := by
  have hXp : 0 < X := (Real.exp_pos _).trans_le hX
  have hl := (Real.le_log_iff_exp_le hXp).mpr hX
  have hc := (Real.le_log_iff_exp_le hXp).mpr hcut
  by_cases hs : h ≤ 1 + 1 / e
  · have hbound := (div_le_iff₀ he).mp hl
    exact hs.trans (by simpa only [mul_comm] using hbound)
  · have hh1 : 1 ≤ h := by have := one_div_pos.mpr he; linarith
    have hlarge : 1 / e ≤ h := by linarith
    have hunit : 1 ≤ e * h := by
      have ht := (div_le_iff₀ he).mp hlarge
      simpa only [mul_comm] using ht
    have hsquare : h ≤ 1000000000000000 * h ^ 2 := by
      nlinarith [sq_nonneg (h - 1)]
    have hcoeff := mul_le_mul_of_nonneg_left hsquare he.le
    have hmul := mul_le_mul_of_nonneg_right (hunit.trans hcoeff) hh
    have hhcenter : h ≤ e * moebiusFiniteContourCenter h := by
      unfold moebiusFiniteContourCenter
      nlinarith [hmul]
    exact hhcenter.trans (mul_le_mul_of_nonneg_left hc he.le)

/-- Even after choosing the best admissible heat parameter, the cubic-rate
envelope eventually exceeds every fixed multiple of each strictly smaller
cutoff power. The arithmetic sum itself may be much smaller. -/
theorem moebiusCubic_rateEnvelope_dominates_lower_power {a b C B : ℝ}
    (hab : a < b) (hC : 0 < C) :
    ∀ᶠ X : ℝ in atTop, ∀ h : ℝ, 0 ≤ h →
      Real.exp (moebiusFiniteContourCenter h) ≤ X →
      B * X ^ a < C * X ^ b * Real.exp (-h / 2) := by
  have he : 0 < b - a := sub_pos.mpr hab
  have hr : Tendsto (fun X : ℝ ↦ C * X ^ ((b - a) / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < (b - a) / 2)).const_mul_atTop hC
  filter_upwards [hr.eventually (eventually_gt_atTop B),
    eventually_ge_atTop (Real.exp ((1 + 1 / (b - a)) / (b - a)))] with X hB hX
  intro h hh hcut
  have hXp : 0 < X := (Real.exp_pos _).trans_le hX
  have hhlog := moebiusCubic_admissible_height_le_log he hX hh hcut
  have hpow : X ^ ((b - a) / 2) * X ^ a ≤ X ^ b * Real.exp (-h / 2) := by
    simp only [Real.rpow_def_of_pos hXp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ < (C * X ^ ((b - a) / 2)) * X ^ a :=
      mul_lt_mul_of_pos_right hB (Real.rpow_pos_of_pos hXp a)
    _ ≤ C * (X ^ b * Real.exp (-h / 2)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hpow hC.le
    _ = _ := by ring

/-- The unabsorbed cubic remainder prevents escaping the power limitation
by choosing a heat parameter beyond its admissible arithmetic cutoff.
This comparison is uniform over all nonnegative parameters. -/
theorem moebiusCubic_fullEnvelope_dominates_lower_power {a b C B : ℝ}
    (hab : a < b) (hb : b ≤ 1) (hC : 0 < C) :
    ∀ᶠ X : ℝ in atTop, ∀ h : ℝ, 0 ≤ h →
      B * X ^ a < C * X ^ b * Real.exp (-h / 2) +
        Real.exp (moebiusFiniteContourCenter h) := by
  have hr : Tendsto (fun X : ℝ ↦ X ^ (1 - a)) atTop atTop :=
    tendsto_rpow_atTop (by linarith)
  filter_upwards [moebiusCubic_rateEnvelope_dominates_lower_power hab hC (B := B),
    hr.eventually (eventually_gt_atTop B), eventually_gt_atTop (0 : ℝ)] with X hsmall hB hXp
  intro h hh
  by_cases hcut : Real.exp (moebiusFiniteContourCenter h) ≤ X
  · exact (hsmall h hh hcut).trans_le (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have hBX : B * X ^ a < X := by
      calc
        _ < X ^ (1 - a) * X ^ a :=
          mul_lt_mul_of_pos_right hB (Real.rpow_pos_of_pos hXp a)
        _ = X := by rw [← Real.rpow_add hXp]; norm_num
    exact (hBX.trans (lt_of_not_ge hcut)).trans_le
      (le_add_of_nonneg_left (by positivity))

/-- The literal all-cutoff Mellin majorant already proved in this repository
cannot yield any fixed power improvement by heat-parameter optimization
alone. Both coefficients and the complete additive remainder are unchanged. -/
theorem moebiusFiniteMellin_cubic_majorant_dominates_lower_power {s : ℂ}
    (hs : 0 < s.re) (hsone : s.re < 1) {a B : ℝ} (ha : a < 1 - s.re) :
    ∀ᶠ X : ℝ in atTop, ∀ h : ℝ, 0 ≤ h →
      B * X ^ a <
        (moebiusFiniteCancellationConstant * (1 + ‖s‖ / (1 - s.re))) *
          Real.exp (-h / 2) * X ^ (1 - s.re) +
        Real.exp (moebiusFiniteContourCenter h) * (1 + ‖s‖ * moebiusMellinDerivativeMass s) := by
  have hC : 0 < moebiusFiniteCancellationConstant * (1 + ‖s‖ / (1 - s.re)) := by
    have := moebiusFiniteCancellationConstant_pos
    have hp : 0 < 1 - s.re := by linarith
    positivity
  have htail : 1 ≤ 1 + ‖s‖ * moebiusMellinDerivativeMass s := by
    exact le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) (moebiusMellinDerivativeMass_nonneg s))
  filter_upwards [moebiusCubic_fullEnvelope_dominates_lower_power ha (by linarith) hC
    (B := B)] with X hX
  intro h hh
  have ht := mul_le_mul_of_nonneg_left htail (Real.exp_pos (moebiusFiniteContourCenter h)).le
  have hx := hX h hh
  nlinarith

/-- A square-root-scale envelope with the existing cubic contour gain still
exceeds every fixed multiple of a smaller source power, uniformly over
admissible heat choices. This is a rate audit, not a work estimate. -/
theorem moebiusCubic_sqrtEnvelope_dominates_source_power {a C B : ℝ}
    (ha : a < 1 / 2) (hC : 0 < C) :
    ∀ᶠ X : ℝ in atTop, ∀ h : ℝ, 0 ≤ h →
      Real.exp (moebiusFiniteContourCenter h) ≤ X →
      B * X ^ a < C * Real.sqrt X * Real.exp (-h / 2) := by
  simpa only [Real.sqrt_eq_rpow] using
    moebiusCubic_rateEnvelope_dominates_lower_power ha hC (B := B)

end

end RiemannGaussian
