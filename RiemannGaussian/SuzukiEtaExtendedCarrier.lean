/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.PairedEtaCompletionDomain
import RiemannGaussian.SuzukiEtaCarrier

/-!
# The arithmetic Suzuki carrier on the full completion domain

The same finite eta coefficients and completion correction approximate
xi plus its derivative throughout the positive half-plane where the
completion factor is analytic and nonzero. The actual denominator is
retained, including at xi zeros. Compact approximation can consequently
cross the upper spectral strip boundary away from the explicit dyadic
exceptions; no RH or zero-free-strip premise is used.
-/

open Complex Filter Metric Set Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

/-- The full arithmetic carrier denominator retains exactly xi plus its
derivative after multiplication by the explicit nonvanishing completion. -/
theorem pairedEtaXiCompletionFactor_mul_suzukiEtaCarrierDenominator_on_completionDomain
    {s : ℂ} (hs : s ∈ pairedEtaCompletionDomain) :
    pairedEtaXiCompletionFactor s * suzukiEtaCarrierDenominator s =
      riemannXi s + deriv riemannXi s := by
  have hH := (analyticAt_pairedEtaXiCompletionFactor_on_completionDomain hs).differentiableAt
  have hEta := hasDerivAt_pairedEtaCore_arithmeticDerivativeValue hs.1
  have hprod := (hH.hasDerivAt.mul hEta).deriv
  have hnear := (pairedEtaCompletedXi_eventuallyEq_riemannXi_on_completionDomain hs).deriv_eq
  change deriv (fun w => pairedEtaXiCompletionFactor w * pairedEtaCore w) s = _ at hnear
  have hd : deriv riemannXi s =
      deriv pairedEtaXiCompletionFactor s * pairedEtaCore s +
        pairedEtaXiCompletionFactor s * pairedEtaArithmeticDerivativeValue s :=
    hnear.symm.trans hprod
  have hxi : pairedEtaXiCompletionFactor s * pairedEtaCore s = riemannXi s :=
    pairedEtaCompletedXi_eq_riemannXi_on_completionDomain hs
  have hL : pairedEtaXiCompletionFactor s * pairedEtaArithmeticXiRegularCorrection s =
      deriv pairedEtaXiCompletionFactor s := by
    rw [← logDeriv_pairedEtaXiCompletionFactor_on_completionDomain hs, logDeriv_apply]
    exact mul_div_cancel₀ _ (pairedEtaXiCompletionFactor_ne_zero_on_completionDomain hs)
  unfold suzukiEtaCarrierDenominator
  rw [hd, ← hxi, ← hL]
  ring

/-- Every actual and finite arithmetic denominator is analytic in the
full completion domain, with no nonvanishing assumption on eta or on the denominator. -/
theorem analyticAt_suzukiEtaCarrierDenominator_on_completionDomain {s : ℂ} (hs : s ∈ pairedEtaCompletionDomain) :
    AnalyticAt ℂ suzukiEtaCarrierDenominator s := by
  have hEta := analyticOnNhd_pairedEtaCore s hs.1
  have heq : pairedEtaArithmeticDerivativeValue =ᶠ[𝓝 s] deriv pairedEtaCore := by
    filter_upwards [(Complex.isOpen_re_gt 0).mem_nhds hs.1] with w hw
    exact (hasDerivAt_pairedEtaCore_arithmeticDerivativeValue hw).deriv.symm
  exact (hEta.deriv.congr heq.symm).add
    ((analyticAt_const.add (analyticAt_pairedEtaArithmeticXiRegularCorrection_on_completionDomain hs)).mul hEta)

/-- Each finite arithmetic denominator is analytic even through its
zeros, so contour groups can contain arbitrary analytic pole orders. -/
theorem analyticAt_suzukiEtaFiniteCarrierDenominator_on_completionDomain (N : ℕ) {s : ℂ}
    (hs : s ∈ pairedEtaCompletionDomain) : AnalyticAt ℂ (suzukiEtaFiniteCarrierDenominator N) s := by
  have hEta := (differentiable_pairedEtaCorePartialSum N).analyticAt s
  have hder : pairedEtaCoreDerivativePartialSum N = deriv (pairedEtaCorePartialSum N) := by
    funext w
    exact (deriv_pairedEtaCorePartialSum N w).symm
  unfold suzukiEtaFiniteCarrierDenominator
  rw [hder]
  exact hEta.deriv.add
    ((analyticAt_const.add (analyticAt_pairedEtaArithmeticXiRegularCorrection_on_completionDomain hs)).mul hEta)

/-- The actual spectral denominator is exactly the reflected arithmetic
denominator times its nonzero completion factor, including at xi zeros. -/
theorem suzukiXiEValue_eq_etaCarrierDenominator_on_completionDomain {z : ℂ}
    (hz : suzukiArithmeticZetaArgument z ∈ pairedEtaCompletionDomain) :
    suzukiXiEValue z = pairedEtaXiCompletionFactor (suzukiArithmeticZetaArgument z) *
      suzukiEtaCarrierDenominator (suzukiArithmeticZetaArgument z) := by
  rw [pairedEtaXiCompletionFactor_mul_suzukiEtaCarrierDenominator_on_completionDomain hz,
    suzukiArithmeticZetaArgument_eq_one_sub_completedSpectralCoordinate,
    riemannXi_one_sub, deriv_riemannXi_one_sub, suzukiXiEValue_eq, deriv_riemannXiSpectral]
  change riemannXi (completedSpectralCoordinate z) + I *
    (I * deriv riemannXi (completedSpectralCoordinate z)) = _
  rw [← mul_assoc, I_mul_I]
  ring

/-- Genuine nonvanishing of the original denominator transports exactly
to the arithmetic denominator; eta itself is allowed to vanish. -/
theorem suzukiEtaCarrierDenominator_ne_zero_iff_on_completionDomain {z : ℂ}
    (hz : suzukiArithmeticZetaArgument z ∈ pairedEtaCompletionDomain) :
    suzukiEtaCarrierDenominator (suzukiArithmeticZetaArgument z) ≠ 0 ↔ suzukiXiEValue z ≠ 0 := by
  rw [suzukiXiEValue_eq_etaCarrierDenominator_on_completionDomain hz, mul_ne_zero_iff]
  exact ⟨fun h => ⟨pairedEtaXiCompletionFactor_ne_zero_on_completionDomain hz, h⟩, And.right⟩

/-- The original complex carrier equals its arithmetic eta quotient on
the true denominator-nonzero domain, including simple xi-node values. -/
theorem suzukiXiZeroCarrier_eq_etaCarrier_on_completionDomain {z : ℂ}
    (hz : suzukiArithmeticZetaArgument z ∈ pairedEtaCompletionDomain) (hE : suzukiXiEValue z ≠ 0) :
    suzukiXiZeroCarrier z = suzukiEtaCarrier (suzukiArithmeticZetaArgument z) := by
  have hxi : riemannXiSpectral z = pairedEtaXiCompletionFactor (suzukiArithmeticZetaArgument z) *
      pairedEtaCore (suzukiArithmeticZetaArgument z) := by
    rw [show pairedEtaXiCompletionFactor (suzukiArithmeticZetaArgument z) *
        pairedEtaCore (suzukiArithmeticZetaArgument z) =
        riemannXi (suzukiArithmeticZetaArgument z) from pairedEtaCompletedXi_eq_riemannXi_on_completionDomain hz,
      suzukiArithmeticZetaArgument_eq_one_sub_completedSpectralCoordinate, riemannXi_one_sub]
    rfl
  rw [suzukiXiZeroCarrier_eq_i_mul_xi_div_E hE, hxi, suzukiXiEValue_eq_etaCarrierDenominator_on_completionDomain hz]
  unfold suzukiEtaCarrier
  have hn := pairedEtaXiCompletionFactor_ne_zero_on_completionDomain hz
  field_simp

/-- The complete finite eta denominators converge locally uniformly,
without removing their zeros or imposing simplicity. -/
theorem tendstoLocallyUniformlyOn_suzukiEtaFiniteCarrierDenominator_on_completionDomain :
    TendstoLocallyUniformlyOn suzukiEtaFiniteCarrierDenominator suzukiEtaCarrierDenominator
      atTop pairedEtaCompletionDomain := by
  have hsub : pairedEtaCompletionDomain ⊆ {s : ℂ | 0 < s.re} := fun _ hs => hs.1
  have hc : ContinuousOn (fun s => 1 + pairedEtaArithmeticXiRegularCorrection s) pairedEtaCompletionDomain :=
    fun s hs => (analyticAt_const.add
      (analyticAt_pairedEtaArithmeticXiRegularCorrection_on_completionDomain hs)).continuousAt.continuousWithinAt
  have hEta := tendstoLocallyUniformlyOn_pairedEtaCorePartialSum.mono hsub
  have hD := tendstoLocallyUniformlyOn_pairedEtaCoreDerivativePartialSum.mono hsub
  have hcst : TendstoLocallyUniformlyOn (fun _ : ℕ => fun s =>
      1 + pairedEtaArithmeticXiRegularCorrection s)
      (fun s => 1 + pairedEtaArithmeticXiRegularCorrection s) atTop pairedEtaCompletionDomain :=
    tendstoLocallyUniformlyOn_const_index _
  have hmul := hcst.fun_mul₀ hEta hc (analyticOnNhd_pairedEtaCore.mono hsub).continuousOn
  exact hD.fun_add hmul

/-- The carrier's arithmetic nonzero domain removes only the true
denominator, not every xi or eta zero. -/
def suzukiEtaExtendedCarrierDomain : Set ℂ :=
  {s | s ∈ pairedEtaCompletionDomain ∧ suzukiEtaCarrierDenominator s ≠ 0}

/-- Finite arithmetic carriers converge locally uniformly on the true
denominator-nonzero domain. Interior pole orders play no role here. -/
theorem tendstoLocallyUniformlyOn_suzukiEtaFiniteCarrier_on_completionDomain :
    TendstoLocallyUniformlyOn suzukiEtaFiniteCarrier suzukiEtaCarrier
      atTop suzukiEtaExtendedCarrierDomain := by
  have hsub : suzukiEtaExtendedCarrierDomain ⊆ {s : ℂ | 0 < s.re} := fun _ hs => hs.1.1
  have hEta := tendstoLocallyUniformlyOn_pairedEtaCorePartialSum.mono hsub
  have hD := tendstoLocallyUniformlyOn_suzukiEtaFiniteCarrierDenominator_on_completionDomain.mono
    (show suzukiEtaExtendedCarrierDomain ⊆ pairedEtaCompletionDomain from fun _ hs => hs.1)
  have hnum : ContinuousOn (fun s => I * pairedEtaCore s) suzukiEtaExtendedCarrierDomain :=
    continuousOn_const.mul (analyticOnNhd_pairedEtaCore.mono hsub).continuousOn
  have hden : ContinuousOn suzukiEtaCarrierDenominator suzukiEtaExtendedCarrierDomain :=
    fun s hs => (analyticAt_suzukiEtaCarrierDenominator_on_completionDomain hs.1).continuousAt.continuousWithinAt
  have hI : TendstoLocallyUniformlyOn (fun _ : ℕ => fun _ : ℂ => I)
      (fun _ => I) atTop suzukiEtaExtendedCarrierDomain :=
    tendstoLocallyUniformlyOn_const_index _
  have hn := hI.fun_mul₀ hEta continuousOn_const (analyticOnNhd_pairedEtaCore.mono hsub).continuousOn
  exact hn.fun_div₀ hD hnum hden (fun _ hs => hs.2)


end
end RiemannGaussian
