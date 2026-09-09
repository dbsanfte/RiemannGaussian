/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierPoleResidues
import RiemannGaussian.RiemannXiSuzukiSpectralHardyProjection

/-!
# The full xi logarithmic derivative and its off-axis Blaschke contribution

The constructed paired expansion now reaches the existing literal
symmetric spectral windows: their full Cauchy sums converge to `A'/A`.
Consequently the analytic window remainder actually tends to zero.
The exact upper/critical/lower decomposition separates the signed
Blaschke contribution from a term with nonpositive imaginary part.
This supplies a quantitative criterion for carrier poles throughout
the upper half-plane, while retaining the complete off-axis divisor.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

/-- Exact transport of one completed reflected pair to the two spectral
principal parts, including the affine Jacobian. -/
theorem I_mul_zetaLogDerivDifferenceSummand_eq_spectral_pair (z : ℂ) (rho : NontrivialZetaZero) :
    I * zetaLogDerivDifferenceSummand (completedSpectralCoordinate z)
        (1 - completedSpectralCoordinate z) rho =
      zetaSpectralLogDerivativePrincipalPart rho z +
        zetaSpectralLogDerivativePrincipalPart (NontrivialZetaZero.functionalPartner rho) z := by
  have hs : completedSpectralCoordinate z - rho.1 = I * (z - zetaSpectralCoordinate rho.1) := by
    unfold completedSpectralCoordinate zetaSpectralCoordinate
    push_cast
    ring_nf
    simp only [I_sq]
    ring
  have hw : 1 - completedSpectralCoordinate z - rho.1 =
      -I * (z + zetaSpectralCoordinate rho.1) := by
    unfold completedSpectralCoordinate zetaSpectralCoordinate
    push_cast
    ring_nf
    simp only [I_sq]
    ring
  rw [zetaLogDerivDifferenceSummand, hs, hw]
  simp only [zetaSpectralLogDerivativePrincipalPart, analyticZetaZeroMultiplicity_functionalPartner,
    NontrivialZetaZero.spectralCoordinate_functionalPartner, sub_neg_eq_add,
    div_eq_mul_inv, mul_inv, inv_neg, inv_I]
  ring_nf
  simp only [I_sq]
  ring

/-- Every literal symmetric spectral window is exactly half of the
transported paired Cauchy window. -/
theorem two_mul_riemannXiSpectralWindowCauchySum_eq_paired {T : ℝ} (hT : 0 ≤ T) (z : ℂ) :
    I * (∑ rho ∈ spectralZetaZeroWindow T,
        zetaLogDerivDifferenceSummand (completedSpectralCoordinate z)
          (1 - completedSpectralCoordinate z) rho) =
      2 * riemannXiSpectralWindowCauchySum T z := by
  rw [Finset.mul_sum]
  simp_rw [I_mul_zetaLogDerivDifferenceSummand_eq_spectral_pair]
  rw [Finset.sum_add_distrib, sum_spectralZetaZeroWindow_comp_functionalPartner hT
    (fun rho => zetaSpectralLogDerivativePrincipalPart rho z)]
  unfold riemannXiSpectralWindowCauchySum
  ring

/-- The actual full symmetric spectral Cauchy windows converge to the
genuine spectral xi logarithmic derivative. The individual unpaired
complex series is not asserted to be absolutely summable. -/
theorem tendsto_riemannXiSpectralWindowCauchySum {z : ℂ} (hz : riemannXiSpectral z ≠ 0) :
    Tendsto (fun T => riemannXiSpectralWindowCauchySum T z) atTop
      (𝓝 (logDeriv riemannXiSpectral z)) := by
  have hs : riemannXi (completedSpectralCoordinate z) ≠ 0 := hz
  have hp := ((hasSum_zetaLogDeriv_reflection hs).comp tendsto_spectralZetaZeroWindow_atTop).const_mul I
  have ht := hp.div_const 2
  have hval : I * (2 * logDeriv riemannXi (completedSpectralCoordinate z)) / 2 =
      logDeriv riemannXiSpectral z := by
    rw [logDeriv_riemannXiSpectral_eq_I_mul_completed]
    ring
  rw [hval] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  simp only [Function.comp_def]
  rw [two_mul_riemannXiSpectralWindowCauchySum_eq_paired hT]
  ring

/-- The existing actual spectral-window analytic remainder now tends to
zero. This is a proved limit of that literal remainder, not a replacement
by a newly defined error. -/
theorem tendsto_riemannXiSpectralWindowLogDerivativeRawRemainder {z : ℂ}
    (hz : riemannXiSpectral z ≠ 0) :
    Tendsto (fun T => riemannXiSpectralWindowLogDerivativeRawRemainder T z) atTop (𝓝 0) := by
  have ht := (tendsto_const_nhds (x := logDeriv riemannXiSpectral z)).sub
    (tendsto_riemannXiSpectralWindowCauchySum hz)
  simpa only [riemannXiSpectralWindowLogDerivativeRawRemainder, sub_self] using ht

/-- Before taking a limit or an imaginary part, the exact finite
Blaschke subtraction leaves the critical divisor plus twice the lower
divisor, with every phase and multiplicity still present. -/
theorem riemannXiSpectralWindowCauchySum_sub_blaschke_eq {T : ℝ} (hT : 0 ≤ T) (z : ℂ) :
    riemannXiSpectralWindowCauchySum T z - riemannXiUpperBlaschkeLogDerivativeWindow z T =
      riemannXiSpectralCriticalCauchyWindow z T + 2 * riemannXiSpectralLowerCauchyWindow z T := by
  rw [riemannXiSpectralWindowCauchySum_eq_upper_add_critical_add_lower,
    riemannXiUpperBlaschkeLogDerivativeWindow_eq_upper_sub_reflected,
    riemannXiSpectralLowerCauchyWindow_eq_upper_conjugatePartner_sum hT]
  ring

/-- The full reflected Cauchy windows converge to the actual logarithmic
derivative minus its complete signed off-axis Blaschke contribution. -/
theorem tendsto_riemannXiSpectral_reflectedCauchyWindow {z : ℂ}
    (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    Tendsto (fun T => riemannXiSpectralCriticalCauchyWindow z T +
      2 * riemannXiSpectralLowerCauchyWindow z T) atTop
        (𝓝 (logDeriv riemannXiSpectral z - riemannXiUpperBlaschkeCompleteLogDerivative z)) := by
  apply ((tendsto_riemannXiSpectralWindowCauchySum hxi).sub
    (tendsto_riemannXiUpperBlaschkeLogDerivativeWindow hz hxi)).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact riemannXiSpectralWindowCauchySum_sub_blaschke_eq hT z

private lemma principalPart_im_nonpos (rho : NontrivialZetaZero) {z : ℂ}
    (h : (zetaSpectralCoordinate rho.1).im ≤ z.im) :
    (zetaSpectralLogDerivativePrincipalPart rho z).im ≤ 0 := by
  simp only [zetaSpectralLogDerivativePrincipalPart, Complex.div_im, natCast_re, natCast_im,
    zero_mul, zero_div, zero_sub, sub_im]
  exact neg_nonpos.mpr (div_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr h)) (Complex.normSq_nonneg _))

private lemma criticalWindow_im_nonpos {z : ℂ} (hz : 0 < z.im) (T : ℝ) :
    (riemannXiSpectralCriticalCauchyWindow z T).im ≤ 0 := by
  unfold riemannXiSpectralCriticalCauchyWindow
  rw [Complex.im_sum]
  apply Finset.sum_nonpos
  intro rho hrho
  apply principalPart_im_nonpos
  rw [(mem_spectralCriticalZetaZeroWindow.mp hrho).2]
  exact hz.le

private lemma lowerWindow_im_nonpos {z : ℂ} (hz : 0 < z.im) (T : ℝ) :
    (riemannXiSpectralLowerCauchyWindow z T).im ≤ 0 := by
  unfold riemannXiSpectralLowerCauchyWindow
  rw [Complex.im_sum]
  apply Finset.sum_nonpos
  intro rho hrho
  exact principalPart_im_nonpos rho ((mem_spectralLowerZetaZeroWindow.mp hrho).2.trans hz).le

/-- The complete logarithmic derivative minus its off-axis Blaschke term
has nonpositive imaginary part everywhere above the real axis away from
the xi divisor. This sign is inherited from actual reflected zero sums. -/
theorem im_logDeriv_riemannXiSpectral_sub_blaschke_nonpos {z : ℂ}
    (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    (logDeriv riemannXiSpectral z - riemannXiUpperBlaschkeCompleteLogDerivative z).im ≤ 0 := by
  have ht := Complex.continuous_im.continuousAt.tendsto.comp
    (tendsto_riemannXiSpectral_reflectedCauchyWindow hz hxi)
  apply le_of_tendsto ht
  filter_upwards with T
  have hcritical := criticalWindow_im_nonpos hz T
  have hlower := lowerWindow_im_nonpos hz T
  change (riemannXiSpectralCriticalCauchyWindow z T +
    2 * riemannXiSpectralLowerCauchyWindow z T).im ≤ 0
  simp only [add_im, mul_im]
  norm_num
  linarith

/-- All possible positive imaginary part of the full xi logarithmic
derivative is supplied by the genuine off-axis Blaschke contribution. -/
theorem im_logDeriv_riemannXiSpectral_le_blaschke {z : ℂ}
    (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    (logDeriv riemannXiSpectral z).im ≤ (riemannXiUpperBlaschkeCompleteLogDerivative z).im := by
  have h := im_logDeriv_riemannXiSpectral_sub_blaschke_nonpos hz hxi
  simpa only [sub_im, sub_nonpos] using h

/-- At a genuine carrier pole, the full spectral logarithmic derivative
is exactly `i`, retaining the complete complex level-set equation. -/
theorem logDeriv_riemannXiSpectral_eq_I_at_carrier_pole {z : ℂ}
    (hE : suzukiXiEValue z = 0) (hxi : riemannXiSpectral z ≠ 0) :
    logDeriv riemannXiSpectral z = I := by
  have hsum : riemannXiSpectral z + I * deriv riemannXiSpectral z = 0 := by
    simpa only [suzukiXiEValue_eq] using hE
  have h : I * deriv riemannXiSpectral z = -riemannXiSpectral z := by
    linear_combination hsum
  have hd : deriv riemannXiSpectral z = I * riemannXiSpectral z := by
    calc
      deriv riemannXiSpectral z = -I * (I * deriv riemannXiSpectral z) := by
        rw [← mul_assoc]
        simp
      _ = -I * -riemannXiSpectral z := by rw [h]
      _ = _ := by ring
  rw [logDeriv_apply, hd, mul_div_cancel_right₀ _ hxi]

/-- Every actual upper carrier pole forces a unit lower bound on the
imaginary part of the complete signed Blaschke logarithmic derivative.
This is a necessary pole source, not a proved upper bound for it. -/
theorem one_le_im_blaschke_at_suzukiXiE_pole {z : ℂ}
    (hz : 0 < z.im) (hE : suzukiXiEValue z = 0) (hxi : riemannXiSpectral z ≠ 0) :
    1 ≤ (riemannXiUpperBlaschkeCompleteLogDerivative z).im := by
  have h := im_logDeriv_riemannXiSpectral_le_blaschke hz hxi
  simpa only [logDeriv_riemannXiSpectral_eq_I_at_carrier_pole hE hxi, I_im] using h

/-- An explicit strict upper budget on the complete Blaschke contribution
excludes an actual carrier pole anywhere in the upper half-plane. -/
theorem suzukiXiEValue_ne_zero_of_blaschke_im_lt_one {z : ℂ}
    (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    (hB : (riemannXiUpperBlaschkeCompleteLogDerivative z).im < 1) :
    suzukiXiEValue z ≠ 0 := by
  intro hE
  exact (not_lt_of_ge (one_le_im_blaschke_at_suzukiXiE_pole hz hE hxi)) hB

/-- The same strict signed Blaschke budget bounds the actual carrier
quantitatively. The estimate applies inside the strip as well as outside
it; the budget is stated explicitly and is not presumed globally. -/
theorem norm_suzukiXiZeroCarrier_le_of_blaschke_budget {z : ℂ}
    (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    (hB : (riemannXiUpperBlaschkeCompleteLogDerivative z).im < 1) :
    ‖suzukiXiZeroCarrier z‖ ≤
      1 / (1 - (riemannXiUpperBlaschkeCompleteLogDerivative z).im) := by
  have hE := suzukiXiEValue_ne_zero_of_blaschke_im_lt_one hz hxi hB
  rw [suzukiXiZeroCarrier_eq_I_div_one_add_logDeriv hxi hE, norm_div, norm_I]
  apply one_div_le_one_div_of_le (sub_pos.mpr hB)
  calc
    1 - (riemannXiUpperBlaschkeCompleteLogDerivative z).im
      ≤ 1 - (logDeriv riemannXiSpectral z).im := by
        linarith [im_logDeriv_riemannXiSpectral_le_blaschke hz hxi]
    _ = (1 + I * logDeriv riemannXiSpectral z).re := by simp [sub_eq_add_neg]
    _ ≤ ‖1 + I * logDeriv riemannXiSpectral z‖ := Complex.re_le_norm _

end
end RiemannGaussian
