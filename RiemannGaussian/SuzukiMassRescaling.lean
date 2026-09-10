/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierMassVariation
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Exact rescaling of the actual mass and carrier

Every smoothing scale is obtained from the unit-scale fields by the
same positive real denominator. This preserves their complex phase,
coupling and common-zero values. Differentiating the genuine identity
gives decay of the scaled horizontal mass derivative at every point.
-/

open Complex Filter Set Topology
namespace RiemannGaussian
noncomputable section

/-- The actual smooth mass and carrier lie on one exact quadratic
surface, including genuine carrier poles and common zeros. -/
theorem normSq_suzukiXiSmoothCarrier_eq_mass {r : ℝ} (hr : 0 < r) (z : ℂ) :
    normSq (suzukiXiSmoothCarrier r z) =
      suzukiXiNormalizedMass r z - r ^ 2 * suzukiXiNormalizedMass r z ^ 2 := by
  by_cases hA : riemannXiSpectral z = 0
  · simp [suzukiXiSmoothCarrier_eq_zero_of_xi_zero r hA, suzukiXiNormalizedMass_eq_zero r hA]
  have hp := complexSmoothQuotient_denominator_pos hr (b := suzukiXiEValue z) (Or.inl hA)
  change normSq (complexSmoothQuotient r (I * riemannXiSpectral z) (suzukiXiEValue z)) =
    normSq (riemannXiSpectral z) / (normSq (suzukiXiEValue z) + r ^ 2 * normSq (riemannXiSpectral z)) -
      r ^ 2 * (normSq (riemannXiSpectral z) / (normSq (suzukiXiEValue z) + r ^ 2 * normSq (riemannXiSpectral z))) ^ 2
  rw [complexSmoothQuotient, complexSmoothQuotient_denominator]
  simp only [map_div₀, map_mul, normSq_I, one_mul, normSq_conj, normSq_ofReal]
  field_simp
  ring

private lemma rescaling_pos {r u : ℝ} (hr : 1 ≤ r) (hu : 0 ≤ u) :
    0 < 1 + (r ^ 2 - 1) * u := by
  have h : 0 ≤ r ^ 2 - 1 := by nlinarith
  nlinarith [mul_nonneg h hu]

/-- All actual masses are recovered from the unit smoothing mass by
one positive real rescaling, including the entire zero divisor. -/
theorem suzukiXiNormalizedMass_eq_unit_rescaling {r : ℝ} (hr : 1 ≤ r) (z : ℂ) :
    suzukiXiNormalizedMass r z = suzukiXiNormalizedMass 1 z /
      (1 + (r ^ 2 - 1) * suzukiXiNormalizedMass 1 z) := by
  by_cases hA : riemannXiSpectral z = 0
  · simp [suzukiXiNormalizedMass_eq_zero r hA, suzukiXiNormalizedMass_eq_zero 1 hA]
  have hp := complexSmoothQuotient_denominator_pos (lt_of_lt_of_le zero_lt_one hr)
    (b := suzukiXiEValue z) (Or.inl hA)
  have h1 := complexSmoothQuotient_denominator_pos (by norm_num : (0 : ℝ) < 1)
    (b := suzukiXiEValue z) (Or.inl hA)
  have hR := rescaling_pos hr (suzukiXiNormalizedMass_nonneg 1 z)
  change normSq (riemannXiSpectral z) / (normSq (suzukiXiEValue z) + r ^ 2 * normSq (riemannXiSpectral z)) =
    (normSq (riemannXiSpectral z) / (normSq (suzukiXiEValue z) + 1 ^ 2 * normSq (riemannXiSpectral z))) /
      (1 + (r ^ 2 - 1) * (normSq (riemannXiSpectral z) / (normSq (suzukiXiEValue z) + 1 ^ 2 * normSq (riemannXiSpectral z))))
  change 0 < 1 + (r ^ 2 - 1) * (normSq (riemannXiSpectral z) /
    (normSq (suzukiXiEValue z) + 1 ^ 2 * normSq (riemannXiSpectral z))) at hR
  simp only [one_pow, one_mul] at h1 ⊢
  field_simp [hp.ne', h1.ne']
  ring

/-- The full complex carrier has exactly the same positive rescaling
as the mass. No phase is lost in passing between smoothing parameters. -/
theorem suzukiXiSmoothCarrier_eq_unit_rescaling {r : ℝ} (hr : 1 ≤ r) (z : ℂ) :
    suzukiXiSmoothCarrier r z = suzukiXiSmoothCarrier 1 z /
      ((1 + (r ^ 2 - 1) * suzukiXiNormalizedMass 1 z : ℝ) : ℂ) := by
  by_cases hA : riemannXiSpectral z = 0
  · simp [suzukiXiSmoothCarrier_eq_zero_of_xi_zero r hA, suzukiXiSmoothCarrier_eq_zero_of_xi_zero 1 hA]
  have hp := complexSmoothQuotient_denominator_pos (lt_of_lt_of_le zero_lt_one hr)
    (b := suzukiXiEValue z) (Or.inl hA)
  have h1 := complexSmoothQuotient_denominator_pos (by norm_num : (0 : ℝ) < 1)
    (b := suzukiXiEValue z) (Or.inl hA)
  have hR := rescaling_pos hr (suzukiXiNormalizedMass_nonneg 1 z)
  unfold suzukiXiSmoothCarrier complexSmoothQuotient
  rw [complexSmoothQuotient_denominator, complexSmoothQuotient_denominator]
  simp only [map_mul, normSq_I, one_mul]
  change _ = _ / ((1 + (r ^ 2 - 1) * (normSq (riemannXiSpectral z) /
    (normSq (suzukiXiEValue z) + 1 ^ 2 * normSq (riemannXiSpectral z))) : ℝ) : ℂ)
  have hpC : ((normSq (suzukiXiEValue z) + r ^ 2 * normSq (riemannXiSpectral z) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have h1C : ((normSq (suzukiXiEValue z) + 1 ^ 2 * normSq (riemannXiSpectral z) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1.ne'
  simp only [ofReal_add, ofReal_mul, ofReal_sub, ofReal_div, ofReal_pow, ofReal_one, one_pow, one_mul] at hpC h1C ⊢
  field_simp [hpC, h1C]
  ring_nf
  field_simp [hpC, h1C]

/-- The derivative at any smoothing scale is the unit mass derivative
divided by the square of the same genuine rescaling denominator. -/
theorem deriv_suzukiXiHorizontalMass_unit_rescaling {r : ℝ} (hr : 1 ≤ r) (y x : ℝ) :
    deriv (suzukiXiHorizontalMass r y) x = deriv (suzukiXiHorizontalMass 1 y) x /
      (1 + (r ^ 2 - 1) * suzukiXiHorizontalMass 1 y x) ^ 2 := by
  have hU := ((contDiff_suzukiXiHorizontalMass (by norm_num : (0 : ℝ) < 1) y).differentiable (by simp) x).hasDerivAt
  have hp := rescaling_pos hr (suzukiXiNormalizedMass_nonneg 1 ((x : ℂ) + (y : ℂ) * I))
  have hd := (hU.div ((hU.const_mul (r ^ 2 - 1)).const_add 1) hp.ne').deriv
  change deriv (fun u => suzukiXiHorizontalMass 1 y u /
    (1 + (r ^ 2 - 1) * suzukiXiHorizontalMass 1 y u)) x = _ at hd
  have he : suzukiXiHorizontalMass r y = fun u => suzukiXiHorizontalMass 1 y u /
      (1 + (r ^ 2 - 1) * suzukiXiHorizontalMass 1 y u) :=
    funext (fun u => suzukiXiNormalizedMass_eq_unit_rescaling hr _)
  rw [he, hd]
  ring

/-- The scaled actual mass is bounded by the reciprocal smoothing
parameter on the entire spectral plane, including all common zeros. -/
theorem suzukiXiNormalizedMass_scaled_le {r : ℝ} (hr : 0 < r) (z : ℂ) :
    r * suzukiXiNormalizedMass r z ≤ 1 / r := by
  calc
    _ ≤ r * (1 / r ^ 2) := mul_le_mul_of_nonneg_left (suzukiXiNormalizedMass_le hr z) hr.le
    _ = _ := by field_simp

/-- The scaled actual mass tends to zero at every fixed spectral
point, with no zero avoidance hypothesis. -/
theorem tendsto_suzukiXiNormalizedMass_scaled (z : ℂ) :
    Tendsto (fun r : ℝ => r * suzukiXiNormalizedMass r z) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (tendsto_const_nhds.div_atTop tendsto_id :
    Tendsto (fun r : ℝ => 1 / r) atTop (𝓝 0))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact mul_nonneg hr.le (suzukiXiNormalizedMass_nonneg r z)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact suzukiXiNormalizedMass_scaled_le hr z

private lemma half_sq_mass_le {r u : ℝ} (hr : 2 ≤ r) (hu : 0 ≤ u) :
    r ^ 2 / 2 * u ≤ 1 + (r ^ 2 - 1) * u := by
  have h : 0 ≤ r ^ 2 / 2 - 1 := by nlinarith
  nlinarith [mul_nonneg h hu]

/-- The scaled actual carrier tends to zero at every fixed point.
The global `1/(2*r)` bound alone would not establish this stronger limit. -/
theorem tendsto_suzukiXiSmoothCarrier_scaled (z : ℂ) :
    Tendsto (fun r : ℝ => (r : ℂ) * suzukiXiSmoothCarrier r z) atTop (𝓝 0) := by
  by_cases hA : riemannXiSpectral z = 0
  · simpa only [suzukiXiSmoothCarrier_eq_zero_of_xi_zero _ hA, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))
  have hU : 0 < suzukiXiNormalizedMass 1 z := by
    change 0 < normSq (riemannXiSpectral z) /
      (normSq (suzukiXiEValue z) + 1 ^ 2 * normSq (riemannXiSpectral z))
    exact div_pos (normSq_pos.mpr hA) (complexSmoothQuotient_denominator_pos (by norm_num) (Or.inl hA))
  have hb : Tendsto (fun r : ℝ => (2 * ‖suzukiXiSmoothCarrier 1 z‖ / suzukiXiNormalizedMass 1 z) / r)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  apply squeeze_zero_norm' _ hb
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
  have hr0 : 0 < r := by linarith
  rw [suzukiXiSmoothCarrier_eq_unit_rescaling (by linarith) z, norm_mul, norm_div,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hr0, abs_of_pos (rescaling_pos (by linarith) hU.le)]
  calc
    _ ≤ r * (‖suzukiXiSmoothCarrier 1 z‖ / (r ^ 2 / 2 * suzukiXiNormalizedMass 1 z)) := by
      gcongr
      exact half_sq_mass_le hr hU.le
    _ = _ := by field_simp

/-- The scaled horizontal derivative of the actual normalized mass
tends to zero at every point, including every repeated xi zero. -/
theorem tendsto_deriv_suzukiXiHorizontalMass_scaled (y x : ℝ) :
    Tendsto (fun r : ℝ => r * deriv (suzukiXiHorizontalMass r y) x) atTop (𝓝 0) := by
  by_cases hU : suzukiXiHorizontalMass 1 y x = 0
  · have hmin : IsLocalMin (suzukiXiHorizontalMass 1 y) x := by
      apply Eventually.of_forall
      intro u
      rw [hU]
      exact suzukiXiNormalizedMass_nonneg 1 _
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    simp [deriv_suzukiXiHorizontalMass_unit_rescaling hr, hmin.deriv_eq_zero]
  have hUpos : 0 < suzukiXiHorizontalMass 1 y x :=
    (suzukiXiNormalizedMass_nonneg 1 _).lt_of_ne' hU
  have hb : Tendsto (fun r : ℝ =>
      (4 * |deriv (suzukiXiHorizontalMass 1 y) x| / suzukiXiHorizontalMass 1 y x ^ 2) / r ^ 3)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0))
  apply squeeze_zero_norm' _ hb
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
  have hr0 : 0 < r := by linarith
  rw [deriv_suzukiXiHorizontalMass_unit_rescaling (by linarith), Real.norm_eq_abs,
    abs_mul, abs_of_pos hr0, abs_div, abs_sq]
  calc
    _ ≤ r * (|deriv (suzukiXiHorizontalMass 1 y) x| / (r ^ 2 / 2 * suzukiXiHorizontalMass 1 y x) ^ 2) := by
      gcongr
      exact half_sq_mass_le hr hUpos.le
    _ = _ := by field_simp; ring

end
end RiemannGaussian
