/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RiemannXiGlobalLogDerivative
import RiemannGaussian.SuzukiCarrierLocalCancellation

/-!
# Unconditional bounds for Suzuki's carriers outside the zero strip

The newly constructed global xi logarithmic-derivative expansion retains a
signed Poisson sum. The known zeta strip makes its sign definite in the
closed safe half-planes. In spectral coordinates this proves that the
entire denominator `A + i eta A'` has no zeros for `Im z >= 1/2`, for every
nonnegative `eta`, and bounds the actual unit-parameter carrier by one.
The reflected channel has the corresponding lower-half-plane bound.

These are genuine global carrier estimates, not a zero-free claim inside
the critical strip. The remaining strip poles must still be retained in
any boundary contour argument.
-/

open Complex Filter Set Topology
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The spectral logarithmic derivative includes the exact affine
Jacobian `i`; its sign follows from the completed-coordinate expansion. -/
theorem logDeriv_riemannXiSpectral_eq_I_mul_completed (z : ℂ) :
    logDeriv riemannXiSpectral z =
      I * logDeriv riemannXi (completedSpectralCoordinate z) := by
  rw [logDeriv_apply, deriv_riemannXiSpectral, logDeriv_apply]
  change I * deriv riemannXi (completedSpectralCoordinate z) /
      riemannXi (completedSpectralCoordinate z) = _
  ring

/-- The genuine spectral logarithmic derivative has nonpositive imaginary
part throughout the upper closed safe half-plane. -/
theorem im_logDeriv_riemannXiSpectral_nonpos_of_half_le_im {z : ℂ}
    (hz : 1 / 2 ≤ z.im) : (logDeriv riemannXiSpectral z).im ≤ 0 := by
  rw [logDeriv_riemannXiSpectral_eq_I_mul_completed]
  simp only [mul_im, I_re, I_im, zero_mul, one_mul, zero_add]
  apply re_logDeriv_riemannXi_nonpos_of_re_nonpos
  simp only [completedSpectralCoordinate, add_re, div_re, mul_re, I_re, I_im,
    zero_mul, one_mul, zero_sub]
  norm_num
  linarith

/-- Factoring out the nonzero xi value retains the exact signed
logarithmic derivative in every homotopy denominator. -/
theorem analyticEValue_riemannXiSpectral_eq_mul_logDeriv {z : ℂ}
    (hz : riemannXiSpectral z ≠ 0) (eta : ℝ) :
    analyticEValue riemannXiSpectral eta z =
      riemannXiSpectral z * (1 + I * (eta : ℂ) * logDeriv riemannXiSpectral z) := by
  simp only [analyticEValue, logDeriv_apply]
  field_simp

/-- Every nonnegative homotopy parameter has a quantitative denominator
floor in the upper safe half-plane. -/
theorem norm_riemannXiSpectral_le_norm_analyticEValue_of_half_le_im
    {eta : ℝ} (heta : 0 ≤ eta) {z : ℂ} (hz : 1 / 2 ≤ z.im) :
    ‖riemannXiSpectral z‖ ≤ ‖analyticEValue riemannXiSpectral eta z‖ := by
  have hxi : riemannXiSpectral z ≠ 0 :=
    riemannXiSpectral_ne_zero_of_half_le_abs_im (hz.trans (le_abs_self _))
  rw [analyticEValue_riemannXiSpectral_eq_mul_logDeriv hxi, norm_mul]
  have hq := im_logDeriv_riemannXiSpectral_nonpos_of_half_le_im hz
  have hre : 1 ≤ (1 + I * (eta : ℂ) * logDeriv riemannXiSpectral z).re := by
    simp only [add_re, one_re, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im,
      zero_mul, mul_zero, sub_zero, zero_add, one_mul, zero_sub]
    nlinarith
  exact le_mul_of_one_le_right (norm_nonneg _) (hre.trans (Complex.re_le_norm _))

/-- The actual entire homotopy denominator is zero-free in the upper
closed safe half-plane, for every nonnegative parameter. -/
theorem analyticEValue_riemannXiSpectral_ne_zero_of_half_le_im
    {eta : ℝ} (heta : 0 ≤ eta) {z : ℂ} (hz : 1 / 2 ≤ z.im) :
    analyticEValue riemannXiSpectral eta z ≠ 0 := by
  have hxi := riemannXiSpectral_ne_zero_of_half_le_abs_im (hz.trans (le_abs_self _))
  exact norm_pos_iff.mp ((norm_pos_iff.mpr hxi).trans_le
    (norm_riemannXiSpectral_le_norm_analyticEValue_of_half_le_im heta hz))

/-- In particular Suzuki's actual unit-parameter denominator has no pole
in the upper safe half-plane. -/
theorem suzukiXiEValue_ne_zero_of_half_le_im {z : ℂ} (hz : 1 / 2 ≤ z.im) :
    suzukiXiEValue z ≠ 0 :=
  analyticEValue_riemannXiSpectral_ne_zero_of_half_le_im (by norm_num) hz

/-- The literal Suzuki carrier is bounded by one on the entire closed
upper safe half-plane, with its denominator nonvanishing proved above. -/
theorem norm_suzukiXiZeroCarrier_le_one_of_half_le_im {z : ℂ} (hz : 1 / 2 ≤ z.im) :
    ‖suzukiXiZeroCarrier z‖ ≤ 1 := by
  have hE := suzukiXiEValue_ne_zero_of_half_le_im hz
  rw [suzukiXiZeroCarrier_eq_i_mul_xi_div_E hE, norm_div, norm_mul, norm_I, one_mul]
  apply (div_le_one (norm_pos_iff.mpr hE)).mpr
  exact norm_riemannXiSpectral_le_norm_analyticEValue_of_half_le_im (by norm_num) hz

/-- The sharp denominator is nonvanishing on the reflected lower safe
half-plane, with the orientation fixed by conjugation. -/
theorem suzukiXiESharpValue_ne_zero_of_im_le_neg_half {z : ℂ} (hz : z.im ≤ -(1 / 2)) :
    suzukiXiESharpValue z ≠ 0 := by
  rw [suzukiXiESharpValue_eq_conj_E_conj, map_ne_zero]
  apply suzukiXiEValue_ne_zero_of_half_le_im
  simp only [conj_im]
  linarith

/-- The full reflected carrier is bounded by one on the entire lower
closed safe half-plane. -/
theorem norm_suzukiXiSharpCarrier_le_one_of_im_le_neg_half {z : ℂ} (hz : z.im ≤ -(1 / 2)) :
    ‖suzukiXiSharpCarrier z‖ ≤ 1 := by
  rw [suzukiXiSharpCarrier, norm_conj]
  apply norm_suzukiXiZeroCarrier_le_one_of_half_le_im
  simp only [conj_im]
  linarith

/-- The genuine carrier is the Cayley resolvent of the full spectral
logarithmic derivative, wherever both original denominators are nonzero. -/
theorem suzukiXiZeroCarrier_eq_I_div_one_add_logDeriv {z : ℂ}
    (hxi : riemannXiSpectral z ≠ 0) (hE : suzukiXiEValue z ≠ 0) :
    suzukiXiZeroCarrier z = I / (1 + I * logDeriv riemannXiSpectral z) := by
  rw [suzukiXiZeroCarrier_eq_i_mul_xi_div_E hE]
  have heq := analyticEValue_riemannXiSpectral_eq_mul_logDeriv hxi 1
  change suzukiXiEValue z = _ at heq
  simp only [ofReal_one, mul_one] at heq
  rw [heq]
  field_simp

/-- Exact phase-energy law away from the divisor, before taking any
half-plane sign. The imaginary logarithmic derivative is retained as the
full signed defect from the boundary carrier circle. -/
theorem suzukiXiZeroCarrier_im_sub_norm_sq {z : ℂ}
    (hxi : riemannXiSpectral z ≠ 0) (hE : suzukiXiEValue z ≠ 0) :
    (suzukiXiZeroCarrier z).im - ‖suzukiXiZeroCarrier z‖ ^ 2 =
      -(logDeriv riemannXiSpectral z).im /
        Complex.normSq (1 + I * logDeriv riemannXiSpectral z) := by
  rw [suzukiXiZeroCarrier_eq_I_div_one_add_logDeriv hxi hE]
  rw [norm_div, norm_I, div_pow, one_pow, Complex.sq_norm]
  simp only [Complex.div_im, I_re, I_im, one_mul, zero_mul,
    add_re, one_re, mul_re, zero_sub]
  ring

/-- In the upper closed safe half-plane the signed carrier phase dominates
its energy. This is stronger than the absolute bound by one. -/
theorem norm_suzukiXiZeroCarrier_sq_le_im_of_half_le_im {z : ℂ} (hz : 1 / 2 ≤ z.im) :
    ‖suzukiXiZeroCarrier z‖ ^ 2 ≤ (suzukiXiZeroCarrier z).im := by
  have hxi := riemannXiSpectral_ne_zero_of_half_le_abs_im (hz.trans (le_abs_self _))
  have heq := suzukiXiZeroCarrier_im_sub_norm_sq hxi (suzukiXiEValue_ne_zero_of_half_le_im hz)
  have hsign := im_logDeriv_riemannXiSpectral_nonpos_of_half_le_im hz
  have hnonneg : 0 ≤ -(logDeriv riemannXiSpectral z).im /
      Complex.normSq (1 + I * logDeriv riemannXiSpectral z) :=
    div_nonneg (neg_nonneg.mpr hsign) (Complex.normSq_nonneg _)
  linarith

/-- The reflected signed phase dominates the reflected energy in the
lower closed safe half-plane. -/
theorem norm_suzukiXiSharpCarrier_sq_le_neg_im_of_im_le_neg_half {z : ℂ}
    (hz : z.im ≤ -(1 / 2)) :
    ‖suzukiXiSharpCarrier z‖ ^ 2 ≤ -(suzukiXiSharpCarrier z).im := by
  have h := norm_suzukiXiZeroCarrier_sq_le_im_of_half_le_im
    (z := starRingEnd ℂ z) (by simp only [conj_im]; linarith)
  simpa only [suzukiXiSharpCarrier, norm_conj, conj_im, neg_neg] using h

/-- The literal carrier is analytic at every point of the closed upper
safe half-plane; the needed denominator hypothesis has been discharged. -/
theorem analyticAt_suzukiXiZeroCarrier_of_half_le_im {z : ℂ} (hz : 1 / 2 ≤ z.im) :
    AnalyticAt ℂ suzukiXiZeroCarrier z := by
  have hA := analyticAt_riemannXiSpectral z
  have hEA : AnalyticAt ℂ suzukiXiEValue z := hA.add (analyticAt_const.mul hA.deriv)
  have hEsA : AnalyticAt ℂ suzukiXiESharpValue z := hA.sub (analyticAt_const.mul hA.deriv)
  unfold suzukiXiZeroCarrier suzukiXiThetaValue
  exact (analyticAt_const.mul (analyticAt_const.add
    (hEsA.div hEA (suzukiXiEValue_ne_zero_of_half_le_im hz)))).div_const

end

end RiemannGaussian
