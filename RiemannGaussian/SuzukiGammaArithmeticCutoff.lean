/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiGammaArithmeticReduction

/-!
# Uniform spatial cutoffs for the remaining arithmetic source

The actual Gaussian boundary has a bound independent of the rectangle
size. Spatial cutoffs may therefore move with smoothing without an
exchange of iterated limits. The full original source remains in the
normalized arithmetic term after both proved errors are removed.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Interval
namespace RiemannGaussian
noncomputable section

private lemma gaussian_radius_bound {tau : ℝ} (htau : 0 < tau) (R : ℝ) :
    R ^ 2 * Real.exp (-tau * R ^ 2 / 4) ≤ 4 / tau := by
  have h := (Real.mul_exp_neg_le_exp_neg_one (tau * R ^ 2 / 4)).trans
    (Real.exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0))
  rw [show -(tau * R ^ 2 / 4) = -tau * R ^ 2 / 4 by ring] at h
  apply (le_div_iff₀ htau).mpr
  nlinarith

/-- The full reflection boundary is bounded uniformly in every eligible
spatial radius. Only the smoothing and Gaussian time appear in the rate. -/
theorem norm_suzukiXiSmoothReflectionField_boundary_le_uniform
    (rho : NontrivialZetaZero) {r tau R : ℝ} (hr : 0 < r) (htau : 0 < tau)
    (hR : 1 ≤ R) (c : ℝ) (hc : 2 * |c| ≤ R)
    (hRe : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R) :
    ‖rectangularBoundaryIntegral (-R) R 0 R
      (suzukiXiSmoothReflectionField rho r c tau)‖ ≤
        (1536 * (zetaSpectralCoordinate rho.1).im ^ 2 / tau) / r := by
  calc
    _ ≤ 384 * (zetaSpectralCoordinate rho.1).im ^ 2 * R ^ 2 / r *
        Real.exp (-tau * R ^ 2 / 4) :=
      norm_suzukiXiSmoothReflectionField_boundary_le rho hr htau hR c hc hRe
    _ = (384 * (zetaSpectralCoordinate rho.1).im ^ 2 / r) *
        (R ^ 2 * Real.exp (-tau * R ^ 2 / 4)) := by ring
    _ ≤ (384 * (zetaSpectralCoordinate rho.1).im ^ 2 / r) * (4 / tau) :=
      mul_le_mul_of_nonneg_left (gaussian_radius_bound htau R) (by positivity)
    _ = _ := by ring

/-- The complete actual source differs from its reflected-node mass by
an explicit error independent of the eligible spatial cutoff. -/
theorem norm_suzukiXiSmoothReflectionSource_rectangle_sub_mass_le
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) {r tau R : ℝ}
    (hr : 0 < r) (htau : 0 < tau) (hR : 1 ≤ R) (c : ℝ)
    (hc : 2 * |c| ≤ R) (hRe : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R) :
    ‖(∫ z in [[-R,R]] ×ℂ [[0,R]], suzukiXiSmoothReflectionSource rho r c tau z) -
      (2 * Real.pi * I) * ((analyticZetaZeroMultiplicity rho : ℂ)⁻¹ *
        suzukiSmoothSpectralBoundaryHeat c tau (starRingEnd ℂ (zetaSpectralCoordinate rho.1)))‖ ≤
      (1536 * (zetaSpectralCoordinate rho.1).im ^ 2 / tau) / r := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have him := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  have he := rectangularAreaIntegral_suzukiXiSmoothReflectionSource_eq_boundary_add_mass
    rho hzero hr c tau (-R) R 0 R le_rfl
    (by rw [conj_re]; nlinarith [neg_le_abs (zetaSpectralCoordinate rho.1).re])
    (by rw [conj_re]; nlinarith [le_abs_self (zetaSpectralCoordinate rho.1).re])
    (by rw [conj_im, zetaSpectralCoordinate_im]; linarith)
    (by rw [conj_im]; linarith [neg_le_abs (zetaSpectralCoordinate rho.1).im])
  rw [rectangularAreaIntegral_eq_setIntegral (by linarith) hR0.le _
    ((locallyIntegrable_suzukiXiSmoothReflectionSource rho hr c tau).integrableOn_isCompact
      (isCompact_uIcc.reProdIm isCompact_uIcc))] at he
  rw [he, add_sub_cancel_right]
  exact norm_suzukiXiSmoothReflectionField_boundary_le_uniform rho hr htau hR c hc hRe

/-- The full source limit is unchanged for arbitrary simultaneous
smoothing and eligible rectangle growth, without a relation between
their rates. Gaussian time and center remain fixed. -/
theorem tendsto_suzukiXiSmoothReflectionSource_moving_rectangle
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) {tau : ℝ}
    (htau : 0 < tau) (c : ℝ) (R : ℝ → ℝ) (hR : ∀ r, 1 ≤ R r)
    (hc : ∀ r, 2 * |c| ≤ R r)
    (hRe : ∀ r, 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R r) :
    Tendsto (fun r : ℝ => ∫ z in [[-R r,R r]] ×ℂ [[0,R r]],
      suzukiXiSmoothReflectionSource rho r c tau z) atTop
      (𝓝 ((2 * Real.pi * I) * ((analyticZetaZeroMultiplicity rho : ℂ)⁻¹ *
        suzukiSmoothSpectralBoundaryHeat c tau (starRingEnd ℂ (zetaSpectralCoordinate rho.1))))) := by
  have hb : Tendsto (fun r : ℝ =>
      (1536 * (zetaSpectralCoordinate rho.1).im ^ 2 / tau) / r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hb
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact norm_suzukiXiSmoothReflectionSource_rectangle_sub_mass_le
    rho hzero hr htau (hR r) c (hc r) (hRe r)

/-- The single remaining arithmetic quartic retains the full source on
arbitrary eligible moving rectangles. Global L1 control of both errors
makes this a simultaneous limit rather than an iterated-limit claim. -/
theorem tendsto_suzukiGammaShiftWeightedArithmeticSource_moving_rectangle
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) {tau : ℝ}
    (htau : 0 < tau) (c : ℝ) (R : ℝ → ℝ) (hR : ∀ r, 1 ≤ R r)
    (hc : ∀ r, 2 * |c| ≤ R r)
    (hRe : ∀ r, 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R r) :
    Tendsto (fun r : ℝ => ∫ z in [[-R r,R r]] ×ℂ [[0,R r]],
      suzukiGammaShiftWeightedArithmeticSource rho r c tau z) atTop
      (𝓝 ((2 * Real.pi * I) * ((analyticZetaZeroMultiplicity rho : ℂ)⁻¹ *
        suzukiSmoothSpectralBoundaryHeat c tau (starRingEnd ℂ (zetaSpectralCoordinate rho.1))))) := by
  let K : ℝ → Set ℂ := fun r => [[-R r,R r]] ×ℂ [[0,R r]]
  have hupper (r : ℝ) : K r ⊆ {z : ℂ | 0 ≤ z.im} := by
    intro z hz
    have hy := hz.2
    rw [uIcc_of_le (show 0 ≤ R r by linarith [hR r])] at hy
    exact hy.1
  have hG := tendsto_suzukiXiSmoothReflectionSource_moving_rectangle rho hzero htau c R hR hc hRe
  have hE := tendsto_setIntegral_suzukiGammaShiftSourceError rho htau c K hupper
  have h := hG.sub hE
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hA := integrableOn_suzukiGammaShiftWeightedArithmeticSource rho hr htau c
    (show IsCompact (K r) from isCompact_uIcc.reProdIm isCompact_uIcc) (hupper r)
  have hEint := (integrableOn_suzukiGammaShiftSourceError rho hr htau c).mono_set (hupper r)
  change (∫ z in K r, suzukiXiSmoothReflectionSource rho r c tau z) -
      (∫ z in K r, suzukiGammaShiftSourceError rho r c tau z) = _
  simp_rw [suzukiXiSmoothReflectionSource_eq_weightedArithmetic_add_error]
  rw [integral_add hA hEint, add_sub_cancel_right]

end
end RiemannGaussian
