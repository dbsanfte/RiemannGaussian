/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiGammaNormalizedGaussian
import RiemannGaussian.SuzukiMassDerivativeEnergy

/-!
# Decay of the actual normalized Gaussian drift on compact intervals

The full denominator drift is expressed through the coupled smooth xi
fields. Their unit-scale derivative budget supplies an integrable
majorant on every fixed compact interval, including the entire zero
divisor. The resulting finite-interval arithmetic ceiling tends to zero.
This does not assert a uniform limit for moving intervals or the singular
complex reflection weight.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Interval
namespace RiemannGaussian
noncomputable section

/-- The exact real coefficient left after combining the Gaussian
derivative with the first Gamma correction in the denominator drift. -/
def suzukiGammaGaussianDriftCoefficient (tau c y x : ℝ) : ℝ :=
  tau * (x - c) - 2 * (suzukiGammaShiftCorrection (suzukiGammaHorizontalArgument y x)).im

/-- The scaled allowance is exactly a square of the coupled carrier,
mass derivative and corrected mass. All denominator drift is retained. -/
theorem suzukiGammaGaussianDriftAllowance_scaled_eq (r tau c y x : ℝ) :
    r ^ 2 * suzukiGammaGaussianDriftAllowance r tau c y x =
      translatedGaussian tau c x *
        (2 * ((r : ℂ) * suzukiXiHorizontalCarrier r y x).re -
          r * deriv (suzukiXiHorizontalMass r y) x +
            suzukiGammaGaussianDriftCoefficient tau c y x * (r * suzukiXiHorizontalMass r y x)) ^ 2 := by
  unfold suzukiGammaGaussianDriftAllowance suzukiGammaNormalizationDrift
    suzukiGammaNormalizedSlope suzukiGammaGaussianDriftCoefficient
  simp only [sub_im, mul_im, neg_re, neg_im, I_re, I_im, add_re, add_im,
    ofReal_re, ofReal_im, conj_re, conj_im, one_re, one_im, mul_re]
  ring

private lemma coefficient_continuous {y : ℝ} (hy : 0 ≤ y) (tau c : ℝ) :
    Continuous (suzukiGammaGaussianDriftCoefficient tau c y) := by
  have hQ : Continuous (fun x => suzukiGammaShiftCorrection (suzukiGammaHorizontalArgument y x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (analyticAt_suzukiGammaShiftCorrection (suzukiGammaHorizontalArgument_re_pos hy x)).continuousAt.comp
      (hasDerivAt_suzukiGammaHorizontalArgument y x).continuousAt
  exact (continuous_const.mul (continuous_id.sub continuous_const)).sub
    (continuous_const.mul (Complex.continuous_im.comp hQ))

private lemma gaussian_continuous (tau c : ℝ) : Continuous (translatedGaussian tau c) := by
  unfold translatedGaussian
  fun_prop

private lemma allowance_continuous {r y : ℝ} (hr : 0 < r) (hy : 0 ≤ y) (tau c : ℝ) :
    Continuous (suzukiGammaGaussianDriftAllowance r tau c y) :=
  (gaussian_continuous tau c).mul
    (((contDiff_suzukiGammaNormalizationDrift hr hy).continuous.add
      ((continuous_const.mul (continuous_id.sub continuous_const)).mul
        (contDiff_suzukiXiHorizontalMass hr y).continuous)).pow 2)

private lemma scaled_carrier_real_sq_le {r : ℝ} (hr : 0 < r) (y x : ℝ) :
    (2 * ((r : ℂ) * suzukiXiHorizontalCarrier r y x).re) ^ 2 ≤ 1 := by
  have hb : |((r : ℂ) * suzukiXiHorizontalCarrier r y x).re| ≤ 1 / 2 := by
    calc
      _ ≤ ‖(r : ℂ) * suzukiXiHorizontalCarrier r y x‖ := abs_re_le_norm _
      _ = r * ‖suzukiXiHorizontalCarrier r y x‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      _ ≤ r * (1 / (2 * r)) := mul_le_mul_of_nonneg_left (norm_suzukiXiSmoothCarrier_le hr _) hr.le
      _ = _ := by field_simp
  have h := abs_le.mp hb
  nlinarith [sq_nonneg (((r : ℂ) * suzukiXiHorizontalCarrier r y x).re)]

private lemma scaled_mass_sq_le {r : ℝ} (hr : 1 ≤ r) (y x : ℝ) :
    (r * suzukiXiHorizontalMass r y x) ^ 2 ≤ 1 := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hl : 0 ≤ r * suzukiXiHorizontalMass r y x :=
    mul_nonneg hr0.le (suzukiXiNormalizedMass_nonneg r _)
  have hb : r * suzukiXiHorizontalMass r y x ≤ 1 :=
    (suzukiXiNormalizedMass_scaled_le hr0 _).trans ((div_le_one hr0).mpr hr)
  nlinarith

private lemma scaled_allowance_le {r : ℝ} (hr : 2 ≤ r) (tau c y x : ℝ) :
    r ^ 2 * suzukiGammaGaussianDriftAllowance r tau c y x ≤
      3 * translatedGaussian tau c x *
        (1 + 32 * (‖deriv (suzukiXiHorizontalCarrier 1 y) x‖ ^ 2 +
          deriv (suzukiXiHorizontalMass 1 y) x ^ 2) +
            suzukiGammaGaussianDriftCoefficient tau c y x ^ 2) := by
  rw [suzukiGammaGaussianDriftAllowance_scaled_eq]
  have hS := scaled_carrier_real_sq_le (by linarith : 0 < r) y x
  have hU := scaled_mass_sq_le (by linarith : 1 ≤ r) y x
  have hD := suzukiXiHorizontalMass_scaled_derivative_sq_le hr y x
  have hK := mul_le_mul_of_nonneg_left hU (sq_nonneg (suzukiGammaGaussianDriftCoefficient tau c y x))
  have hsquare : (2 * ((r : ℂ) * suzukiXiHorizontalCarrier r y x).re -
      r * deriv (suzukiXiHorizontalMass r y) x +
        suzukiGammaGaussianDriftCoefficient tau c y x * (r * suzukiXiHorizontalMass r y x)) ^ 2 ≤
      3 * (1 + 32 * (‖deriv (suzukiXiHorizontalCarrier 1 y) x‖ ^ 2 +
        deriv (suzukiXiHorizontalMass 1 y) x ^ 2) +
          suzukiGammaGaussianDriftCoefficient tau c y x ^ 2) := by
    nlinarith [sq_nonneg (2 * ((r : ℂ) * suzukiXiHorizontalCarrier r y x).re +
        r * deriv (suzukiXiHorizontalMass r y) x),
      sq_nonneg (r * deriv (suzukiXiHorizontalMass r y) x +
        suzukiGammaGaussianDriftCoefficient tau c y x * (r * suzukiXiHorizontalMass r y x)),
      sq_nonneg (2 * ((r : ℂ) * suzukiXiHorizontalCarrier r y x).re -
        suzukiGammaGaussianDriftCoefficient tau c y x * (r * suzukiXiHorizontalMass r y x))]
  have hw : 0 ≤ translatedGaussian tau c x := (Real.exp_pos _).le
  nlinarith [mul_le_mul_of_nonneg_left hsquare hw]

/-- The scaled full drift allowance tends to zero at every point,
including repeated zeros. This uses the exact mass--carrier coupling. -/
theorem tendsto_suzukiGammaGaussianDriftAllowance_scaled (tau c y x : ℝ) :
    Tendsto (fun r : ℝ => r ^ 2 * suzukiGammaGaussianDriftAllowance r tau c y x) atTop (𝓝 0) := by
  have hS := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_suzukiXiSmoothCarrier_scaled ((x : ℂ) + (y : ℂ) * I))
  have hD := tendsto_deriv_suzukiXiHorizontalMass_scaled y x
  have hU := tendsto_suzukiXiNormalizedMass_scaled ((x : ℂ) + (y : ℂ) * I)
  have ht := (((hS.const_mul 2).sub hD).add
    (hU.const_mul (suzukiGammaGaussianDriftCoefficient tau c y x))).pow 2
  have hw := ht.const_mul (translatedGaussian tau c x)
  simpa only [Function.comp_def, suzukiGammaGaussianDriftAllowance_scaled_eq, suzukiXiHorizontalCarrier,
    suzukiXiHorizontalMass, zero_re, mul_zero, sub_zero, add_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hw

/-- On any fixed compact subset of an upper horizontal line, the
entire scaled denominator-drift allowance has integral tending to zero.
The continuous unit-field majorant discharges convergence across zeros. -/
theorem tendsto_integral_suzukiGammaGaussianDriftAllowance_scaled {y : ℝ}
    (hy : 0 ≤ y) (tau c : ℝ) {K : Set ℝ} (hK : IsCompact K) :
    Tendsto (fun r : ℝ => ∫ x in K, r ^ 2 * suzukiGammaGaussianDriftAllowance r tau c y x)
      atTop (𝓝 0) := by
  let C : ℝ → ℝ := fun x => 3 * translatedGaussian tau c x *
    (1 + 32 * (‖deriv (suzukiXiHorizontalCarrier 1 y) x‖ ^ 2 +
      deriv (suzukiXiHorizontalMass 1 y) x ^ 2) + suzukiGammaGaussianDriftCoefficient tau c y x ^ 2)
  have hc : Continuous C :=
    (continuous_const.mul (gaussian_continuous tau c)).mul
      ((continuous_const.add (continuous_const.mul
        ((((contDiff_suzukiXiHorizontalCarrier (by norm_num : (0 : ℝ) < 1) y).continuous_deriv (by simp)).norm.pow 2).add
          (((contDiff_suzukiXiHorizontalMass (by norm_num : (0 : ℝ) < 1) y).continuous_deriv (by simp)).pow 2)))).add
            ((coefficient_continuous hy tau c).pow 2))
  have ht := tendsto_integral_filter_of_dominated_convergence
    (l := (atTop : Filter ℝ)) (μ := volume.restrict K)
    (F := fun r : ℝ => fun x => r ^ 2 * suzukiGammaGaussianDriftAllowance r tau c y x)
    (f := fun _ => (0 : ℝ)) C ?_ ?_ (hc.continuousOn.integrableOn_compact hK) ?_
  · simpa only [integral_zero] using ht
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact (continuous_const.mul (allowance_continuous hr hy tau c)).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by unfold suzukiGammaGaussianDriftAllowance translatedGaussian; positivity)]
      exact scaled_allowance_le hr tau c y x
  · exact ae_of_all _ fun x => tendsto_suzukiGammaGaussianDriftAllowance_scaled tau c y x

/-- The same actual allowance decays with the full squared smoothing
factor outside any fixed finite interval integral. -/
theorem tendsto_intervalIntegral_suzukiGammaGaussianDriftAllowance_scaled {y a b : ℝ}
    (hy : 0 ≤ y) (hab : a ≤ b) (tau c : ℝ) :
    Tendsto (fun r : ℝ => r ^ 2 * ∫ x in a..b, suzukiGammaGaussianDriftAllowance r tau c y x)
      atTop (𝓝 0) := by
  have ht := tendsto_integral_suzukiGammaGaussianDriftAllowance_scaled hy tau c
    (K := Icc a b) isCompact_Icc
  simpa only [integral_const_mul, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab] using ht

/-- The normalized arithmetic slope retains pointwise decay after
multiplication by the smoothing parameter, through its exact coupling. -/
theorem tendsto_suzukiGammaNormalizedSlope_scaled (y x : ℝ) :
    Tendsto (fun r : ℝ => (r : ℂ) * suzukiGammaNormalizedSlope r y x) atTop (𝓝 0) := by
  have hS := tendsto_suzukiXiSmoothCarrier_scaled ((x : ℂ) + (y : ℂ) * I)
  have hU := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_suzukiXiNormalizedMass_scaled ((x : ℂ) + (y : ℂ) * I))
  have ht := (hS.const_mul (-I)).sub
    (hU.const_mul (1 + starRingEnd ℂ (suzukiGammaShiftCorrection (suzukiGammaHorizontalArgument y x))))
  simp only [mul_zero, ofReal_zero, sub_zero] at ht
  convert ht using 1
  funext r
  unfold suzukiGammaNormalizedSlope suzukiXiHorizontalCarrier suzukiXiHorizontalMass
  dsimp only [Function.comp_def]
  push_cast
  ring

/-- Every fixed endpoint of the actual Gaussian current vanishes
even after multiplication by the full squared smoothing parameter. -/
theorem tendsto_suzukiGammaGaussianCurrent_scaled (tau c y x : ℝ) :
    Tendsto (fun r : ℝ => (r : ℂ) ^ 2 * suzukiGammaGaussianCurrent r tau c y x) atTop (𝓝 0) := by
  have hU := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_suzukiXiNormalizedMass_scaled ((x : ℂ) + (y : ℂ) * I))
  have ht := (hU.mul (tendsto_suzukiGammaNormalizedSlope_scaled y x)).const_mul
    (translatedGaussian tau c x : ℂ)
  simp only [ofReal_zero, mul_zero] at ht
  convert ht using 1
  funext r
  unfold suzukiGammaGaussianCurrent suzukiXiHorizontalMass
  dsimp only [Function.comp_def]
  push_cast
  ring

/-- For every fixed finite interval, the actual normalized arithmetic
Gaussian integral is eventually below any prescribed positive ceiling.
All drift and endpoint limits are proved; no arithmetic decay premise
is assumed. The singular reflection weight is outside this statement. -/
theorem eventually_integral_suzukiGammaShiftArithmeticSource_gaussian_le
    {y a b : ℝ} (hy : 0 ≤ y) (hab : a ≤ b) (tau c : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ r : ℝ in atTop,
      (∫ x : ℝ in a..b, translatedGaussian tau c x *
        (suzukiGammaShiftArithmeticSource r (suzukiGammaHorizontalArgument y x)).im) ≤ epsilon := by
  have hJ := Complex.continuous_im.continuousAt.tendsto.comp
    ((tendsto_suzukiGammaGaussianCurrent_scaled tau c y b).sub
      (tendsto_suzukiGammaGaussianCurrent_scaled tau c y a))
  have hA := tendsto_intervalIntegral_suzukiGammaGaussianDriftAllowance_scaled hy hab tau c
  have ht := (hJ.const_mul (-2)).add (hA.div_const 2)
  have hlim : Tendsto (fun r : ℝ =>
      -2 * r ^ 2 * (suzukiGammaGaussianCurrent r tau c y b - suzukiGammaGaussianCurrent r tau c y a).im +
        (r ^ 2 / 2) * ∫ x in a..b, suzukiGammaGaussianDriftAllowance r tau c y x) atTop (𝓝 0) := by
    convert ht using 1
    · funext r
      simp only [Function.comp_def, sub_im, mul_im, pow_two, mul_re, ofReal_im, ofReal_re]
      ring
    · simp
  filter_upwards [eventually_gt_atTop (0 : ℝ), hlim.eventually (gt_mem_nhds hepsilon)] with r hr hb
  exact (integral_suzukiGammaShiftArithmeticSource_gaussian_le_drift hr hy hab tau c).trans hb.le

end
end RiemannGaussian
