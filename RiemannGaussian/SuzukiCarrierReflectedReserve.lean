/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RiemannXiGlobalBlaschkeSplit

/-!
# Retaining the reflected divisor in carrier pole bounds

The reflected critical and lower divisor supplies a positive Poisson
reserve. Its actual finite spectral windows increase to the full reserve
in the constructed xi expansion. Keeping any such window raises the
necessary Blaschke threshold at a carrier pole and improves the quantitative
carrier bound. The complex identity remains available upstream; no upper
bound on the complete signed Blaschke contribution is assumed silently.
-/

open Complex Filter Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

/-- The multiplicity-weighted signed Poisson contribution of a genuine
spectral zero. It is positive when the observation point lies above it. -/
def zetaSpectralPoissonContribution (z : ℂ) (rho : NontrivialZetaZero) : ℝ :=
  (analyticZetaZeroMultiplicity rho : ℝ) *
    (z.im - (zetaSpectralCoordinate rho.1).im) /
      Complex.normSq (z - zetaSpectralCoordinate rho.1)

/-- The Poisson contribution is exactly the negative imaginary part of
the original complex principal part, including its multiplicity. -/
theorem zetaSpectralPoissonContribution_eq_neg_im (z : ℂ) (rho : NontrivialZetaZero) :
    zetaSpectralPoissonContribution z rho =
      -(zetaSpectralLogDerivativePrincipalPart rho z).im := by
  simp only [zetaSpectralPoissonContribution, zetaSpectralLogDerivativePrincipalPart,
    Complex.div_im, natCast_re, natCast_im, zero_mul, zero_div, zero_sub, neg_neg, sub_im]

/-- A zero at or below the observation height has a nonnegative Poisson
contribution. No simplicity or separation hypothesis is needed here. -/
theorem zetaSpectralPoissonContribution_nonneg {z : ℂ} (rho : NontrivialZetaZero)
    (h : (zetaSpectralCoordinate rho.1).im ≤ z.im) :
    0 ≤ zetaSpectralPoissonContribution z rho :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr h)) (Complex.normSq_nonneg _)

/-- The retained reflected reserve in an actual symmetric zero window:
one copy of the critical divisor and two copies of the lower divisor. -/
def riemannXiReflectedPoissonReserve (z : ℂ) (T : ℝ) : ℝ :=
  (∑ rho ∈ spectralCriticalZetaZeroWindow T, zetaSpectralPoissonContribution z rho) +
    2 * ∑ rho ∈ spectralLowerZetaZeroWindow T, zetaSpectralPoissonContribution z rho

/-- The finite reserve is the exact imaginary projection of the complex
reflected Cauchy window, before any sign or size estimate. -/
theorem riemannXiReflectedPoissonReserve_eq_neg_im (z : ℂ) (T : ℝ) :
    riemannXiReflectedPoissonReserve z T =
      -(riemannXiSpectralCriticalCauchyWindow z T +
        2 * riemannXiSpectralLowerCauchyWindow z T).im := by
  simp only [riemannXiReflectedPoissonReserve,
    zetaSpectralPoissonContribution_eq_neg_im, Finset.sum_neg_distrib,
    riemannXiSpectralCriticalCauchyWindow, riemannXiSpectralLowerCauchyWindow,
    add_im, mul_im, Complex.im_sum]
  norm_num
  ring

/-- Every retained reflected window contributes a nonnegative reserve
throughout the upper half-plane. -/
theorem riemannXiReflectedPoissonReserve_nonneg {z : ℂ} (hz : 0 < z.im) (T : ℝ) :
    0 ≤ riemannXiReflectedPoissonReserve z T := by
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro rho hrho
    apply zetaSpectralPoissonContribution_nonneg
    rw [(mem_spectralCriticalZetaZeroWindow.mp hrho).2]
    exact hz.le
  · apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro rho hrho
    exact zetaSpectralPoissonContribution_nonneg rho
      ((mem_spectralLowerZetaZeroWindow.mp hrho).2.trans hz).le

private lemma window_subset {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T) :
    spectralZetaZeroWindow S ⊆ spectralZetaZeroWindow T := by
  intro rho hrho
  exact (mem_spectralZetaZeroWindow (hS.trans hST) rho).mpr
    (((mem_spectralZetaZeroWindow hS rho).mp hrho).trans hST)

/-- Retaining a larger genuine spectral window can only increase the
positive reflected reserve. This is monotonicity in the actual cutoff. -/
theorem riemannXiReflectedPoissonReserve_mono {z : ℂ} (hz : 0 < z.im)
    {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T) :
    riemannXiReflectedPoissonReserve z S ≤ riemannXiReflectedPoissonReserve z T := by
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset_filter _ (window_subset hS hST))
    intro rho hrho _hnot
    apply zetaSpectralPoissonContribution_nonneg
    rw [(mem_spectralCriticalZetaZeroWindow.mp hrho).2]
    exact hz.le
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset_filter _ (window_subset hS hST))
    intro rho hrho _hnot
    exact zetaSpectralPoissonContribution_nonneg rho
      ((mem_spectralLowerZetaZeroWindow.mp hrho).2.trans hz).le

/-- The increasing actual reserves converge to precisely the amount
subtracted from the complete Blaschke imaginary part by the full xi
logarithmic derivative. The tail is a proved limit, not a new assumption. -/
theorem tendsto_riemannXiReflectedPoissonReserve {z : ℂ}
    (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    Tendsto (riemannXiReflectedPoissonReserve z) atTop
      (𝓝 ((riemannXiUpperBlaschkeCompleteLogDerivative z).im -
        (logDeriv riemannXiSpectral z).im)) := by
  have ht := (Complex.continuous_im.continuousAt.tendsto.comp
    (tendsto_riemannXiSpectral_reflectedCauchyWindow hz hxi)).neg
  simpa only [Function.comp_def, ← riemannXiReflectedPoissonReserve_eq_neg_im,
    sub_im, neg_sub] using ht

/-- Every finite retained reserve is bounded by the full reserve. Thus
finite zero data can be used without dropping the remaining positive tail. -/
theorem riemannXiReflectedPoissonReserve_le_complete {z : ℂ}
    (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) {T : ℝ} (hT : 0 ≤ T) :
    riemannXiReflectedPoissonReserve z T ≤
      (riemannXiUpperBlaschkeCompleteLogDerivative z).im -
        (logDeriv riemannXiSpectral z).im := by
  apply ge_of_tendsto (tendsto_riemannXiReflectedPoissonReserve hz hxi)
  filter_upwards [eventually_ge_atTop T] with U hTU
  exact riemannXiReflectedPoissonReserve_mono hz hT hTU

/-- A finite reflected reserve sharpens the independent signed upper
bound on the actual xi logarithmic derivative. -/
theorem im_logDeriv_riemannXiSpectral_le_blaschke_sub_reserve {z : ℂ}
    (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) {T : ℝ} (hT : 0 ≤ T) :
    (logDeriv riemannXiSpectral z).im ≤
      (riemannXiUpperBlaschkeCompleteLogDerivative z).im -
        riemannXiReflectedPoissonReserve z T := by
  linarith [riemannXiReflectedPoissonReserve_le_complete hz hxi hT]

/-- Every genuine upper carrier pole must pay for one unit plus every
retained reflected window, with no loss of the negative baseline. -/
theorem one_add_reserve_le_im_blaschke_at_suzukiXiE_pole {z : ℂ}
    (hz : 0 < z.im) (hE : suzukiXiEValue z = 0) (hxi : riemannXiSpectral z ≠ 0)
    {T : ℝ} (hT : 0 ≤ T) :
    1 + riemannXiReflectedPoissonReserve z T ≤
      (riemannXiUpperBlaschkeCompleteLogDerivative z).im := by
  have h := im_logDeriv_riemannXiSpectral_le_blaschke_sub_reserve hz hxi hT
  rw [logDeriv_riemannXiSpectral_eq_I_at_carrier_pole hE hxi, I_im] at h
  linarith

/-- Beating the unit threshold plus any retained reflected reserve
excludes an actual carrier pole, including inside the zero strip. -/
theorem suzukiXiEValue_ne_zero_of_blaschke_reserve_budget {z : ℂ}
    (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) {T : ℝ} (hT : 0 ≤ T)
    (hB : (riemannXiUpperBlaschkeCompleteLogDerivative z).im <
      1 + riemannXiReflectedPoissonReserve z T) :
    suzukiXiEValue z ≠ 0 := by
  intro hE
  exact (not_lt_of_ge (one_add_reserve_le_im_blaschke_at_suzukiXiE_pole hz hE hxi hT)) hB

/-- The same retained reserve improves the quantitative carrier bound.
The complete signed Blaschke budget is explicit; it remains to be proved
where a global contour argument requires it. -/
theorem norm_suzukiXiZeroCarrier_le_of_blaschke_reserve_budget {z : ℂ}
    (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) {T : ℝ} (hT : 0 ≤ T)
    (hB : (riemannXiUpperBlaschkeCompleteLogDerivative z).im <
      1 + riemannXiReflectedPoissonReserve z T) :
    ‖suzukiXiZeroCarrier z‖ ≤
      1 / (1 + riemannXiReflectedPoissonReserve z T -
        (riemannXiUpperBlaschkeCompleteLogDerivative z).im) := by
  have hE := suzukiXiEValue_ne_zero_of_blaschke_reserve_budget hz hxi hT hB
  rw [suzukiXiZeroCarrier_eq_I_div_one_add_logDeriv hxi hE, norm_div, norm_I]
  apply one_div_le_one_div_of_le (sub_pos.mpr hB)
  calc
    1 + riemannXiReflectedPoissonReserve z T -
        (riemannXiUpperBlaschkeCompleteLogDerivative z).im
      ≤ 1 - (logDeriv riemannXiSpectral z).im := by
        linarith [im_logDeriv_riemannXiSpectral_le_blaschke_sub_reserve hz hxi hT]
    _ = (1 + I * logDeriv riemannXiSpectral z).re := by simp [sub_eq_add_neg]
    _ ≤ ‖1 + I * logDeriv riemannXiSpectral z‖ := Complex.re_le_norm _

end
end RiemannGaussian
