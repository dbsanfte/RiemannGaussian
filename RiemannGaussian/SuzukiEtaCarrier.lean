/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaCompletedSymmetry
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteRouche
import RiemannGaussian.SuzukiCarrierFiniteContour
import RiemannGaussian.FiniteToEntireRootPinning

/-!
# An arithmetic eta denominator for the full Suzuki carrier

At the reflected coordinate `s=1/2-i*z`, the genuine carrier denominator
is xi plus its derivative. The nonvanishing completion factor cancels,
leaving `i*eta/(eta' + (1+L)*eta)`, where `L` is the explicit completion
logarithmic derivative. This identity remains valid at xi zeros whenever
the original carrier denominator is nonzero.

Finite paired eta sums and their explicit finite derivatives approximate
this new denominator locally uniformly. Its zeros, including multiple
ones, are retained; nonvanishing is required only on the observation set.
-/

open Complex Filter Metric Set Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

/-- The open strip where the paired eta completion is analytic and nonzero. -/
def suzukiEtaStrip : Set ℂ := {s | 0 < s.re ∧ s.re < 1}

/-- The literal arithmetic denominator for the reflected Suzuki carrier. -/
def suzukiEtaCarrierDenominator (s : ℂ) : ℂ :=
  pairedEtaArithmeticDerivativeValue s +
    (1 + pairedEtaArithmeticXiRegularCorrection s) * pairedEtaCore s

/-- The finite arithmetic denominator with the same exact completion
correction and the original odd/even eta coefficients. -/
def suzukiEtaFiniteCarrierDenominator (N : ℕ) (s : ℂ) : ℂ :=
  pairedEtaCoreDerivativePartialSum N s +
    (1 + pairedEtaArithmeticXiRegularCorrection s) * pairedEtaCorePartialSum N s

/-- The arithmetic carrier with its full complex denominator retained. -/
def suzukiEtaCarrier (s : ℂ) : ℂ := I * pairedEtaCore s / suzukiEtaCarrierDenominator s

/-- A finite paired-eta approximation of the full carrier. -/
def suzukiEtaFiniteCarrier (N : ℕ) (s : ℂ) : ℂ :=
  I * pairedEtaCorePartialSum N s / suzukiEtaFiniteCarrierDenominator N s

/-- The finite carrier denominator is the original odd/even eta family
with exact logarithmic weights `1+L(s)-log(n)`. Both phases and the common
completion correction remain inside the finite sum. -/
theorem suzukiEtaFiniteCarrierDenominator_eq_log_weighted_sum (N : ℕ) (s : ℂ) :
    suzukiEtaFiniteCarrierDenominator N s =
      ∑ n ∈ Finset.range N,
        ((1 + pairedEtaArithmeticXiRegularCorrection s -
          Complex.log ((((2 * n + 1 : ℕ) : ℝ) : ℂ))) *
          ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) -
        (1 + pairedEtaArithmeticXiRegularCorrection s -
          Complex.log ((((2 * n + 2 : ℕ) : ℝ) : ℂ))) *
          ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ^ (-s)) := by
  unfold suzukiEtaFiniteCarrierDenominator pairedEtaCorePartialSum pairedEtaCoreDerivativePartialSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  unfold pairedEtaCoreSummand pairedEtaCoreDerivativeSummand
  ring

/-- A full complex test sees a signed arithmetic numerator, with the
eta sum and conjugated logarithmically weighted sum still coupled.
This exact formula also respects totalized zero denominators. -/
theorem im_mul_suzukiEtaFiniteCarrier (b : ℂ) (N : ℕ) (s : ℂ) :
    (b * suzukiEtaFiniteCarrier N s).im =
      (b * pairedEtaCorePartialSum N s *
        starRingEnd ℂ (suzukiEtaFiniteCarrierDenominator N s)).re /
          normSq (suzukiEtaFiniteCarrierDenominator N s) := by
  have he : b * suzukiEtaFiniteCarrier N s =
      I * (b * pairedEtaCorePartialSum N s / suzukiEtaFiniteCarrierDenominator N s) := by
    unfold suzukiEtaFiniteCarrier
    ring
  rw [he]
  simp only [Complex.mul_im, I_re, I_im, zero_mul, one_mul, zero_add,
    Complex.div_re, Complex.mul_re, conj_re, conj_im]
  ring

/-- The open-strip completion correction is analytic, including at eta
zeros; its only denominator here is the nonvanishing completion factor. -/
theorem analyticAt_pairedEtaArithmeticXiRegularCorrection {s : ℂ} (hs : s ∈ suzukiEtaStrip) :
    AnalyticAt ℂ pairedEtaArithmeticXiRegularCorrection s := by
  have hH := analyticAt_pairedEtaXiCompletionFactor hs.1 hs.2
  have hn := pairedEtaXiCompletionFactor_ne_zero hs.1 hs.2
  have heq : pairedEtaArithmeticXiRegularCorrection =ᶠ[𝓝 s]
      logDeriv pairedEtaXiCompletionFactor := by
    filter_upwards [(Complex.isOpen_re_gt 0).mem_nhds hs.1,
      (Complex.isOpen_re_lt 1).mem_nhds hs.2] with w hw0 hw1
    exact (logDeriv_pairedEtaXiCompletionFactor hw0 hw1).symm
  exact (hH.deriv.div hH hn).congr heq.symm

/-- The full arithmetic carrier denominator retains exactly xi plus its
derivative after multiplication by the explicit nonvanishing completion. -/
theorem pairedEtaXiCompletionFactor_mul_suzukiEtaCarrierDenominator
    {s : ℂ} (hs : s ∈ suzukiEtaStrip) :
    pairedEtaXiCompletionFactor s * suzukiEtaCarrierDenominator s =
      riemannXi s + deriv riemannXi s := by
  have hH := differentiableAt_pairedEtaXiCompletionFactor hs.1 hs.2
  have hEta := hasDerivAt_pairedEtaCore_arithmeticDerivativeValue hs.1
  have hprod := (hH.hasDerivAt.mul hEta).deriv
  have hnear := (pairedEtaCompletedXi_eventuallyEq_riemannXi hs.1 hs.2).deriv_eq
  change deriv (fun w => pairedEtaXiCompletionFactor w * pairedEtaCore w) s = _ at hnear
  have hd : deriv riemannXi s =
      deriv pairedEtaXiCompletionFactor s * pairedEtaCore s +
        pairedEtaXiCompletionFactor s * pairedEtaArithmeticDerivativeValue s :=
    hnear.symm.trans hprod
  have hxi : pairedEtaXiCompletionFactor s * pairedEtaCore s = riemannXi s :=
    pairedEtaCompletedXi_eq_riemannXi hs.1 hs.2
  have hL : pairedEtaXiCompletionFactor s * pairedEtaArithmeticXiRegularCorrection s =
      deriv pairedEtaXiCompletionFactor s := by
    rw [← logDeriv_pairedEtaXiCompletionFactor hs.1 hs.2, logDeriv_apply]
    exact mul_div_cancel₀ _ (pairedEtaXiCompletionFactor_ne_zero hs.1 hs.2)
  unfold suzukiEtaCarrierDenominator
  rw [hd, ← hxi, ← hL]
  ring

/-- Every actual and finite arithmetic denominator is analytic in the
open strip, with no nonvanishing assumption on eta or on the denominator. -/
theorem analyticAt_suzukiEtaCarrierDenominator {s : ℂ} (hs : s ∈ suzukiEtaStrip) :
    AnalyticAt ℂ suzukiEtaCarrierDenominator s := by
  have hEta := analyticOnNhd_pairedEtaCore s hs.1
  have heq : pairedEtaArithmeticDerivativeValue =ᶠ[𝓝 s] deriv pairedEtaCore := by
    filter_upwards [(Complex.isOpen_re_gt 0).mem_nhds hs.1] with w hw
    exact (hasDerivAt_pairedEtaCore_arithmeticDerivativeValue hw).deriv.symm
  exact (hEta.deriv.congr heq.symm).add
    ((analyticAt_const.add (analyticAt_pairedEtaArithmeticXiRegularCorrection hs)).mul hEta)

/-- Each finite arithmetic denominator is analytic even through its
zeros, so contour groups can contain arbitrary analytic pole orders. -/
theorem analyticAt_suzukiEtaFiniteCarrierDenominator (N : ℕ) {s : ℂ}
    (hs : s ∈ suzukiEtaStrip) : AnalyticAt ℂ (suzukiEtaFiniteCarrierDenominator N) s := by
  have hEta := (differentiable_pairedEtaCorePartialSum N).analyticAt s
  have hder : pairedEtaCoreDerivativePartialSum N = deriv (pairedEtaCorePartialSum N) := by
    funext w
    exact (deriv_pairedEtaCorePartialSum N w).symm
  unfold suzukiEtaFiniteCarrierDenominator
  rw [hder]
  exact hEta.deriv.add
    ((analyticAt_const.add (analyticAt_pairedEtaArithmeticXiRegularCorrection hs)).mul hEta)

/-- The actual spectral denominator is exactly the reflected arithmetic
denominator times its nonzero completion factor, including at xi zeros. -/
theorem suzukiXiEValue_eq_etaCarrierDenominator {z : ℂ}
    (hz : suzukiArithmeticZetaArgument z ∈ suzukiEtaStrip) :
    suzukiXiEValue z = pairedEtaXiCompletionFactor (suzukiArithmeticZetaArgument z) *
      suzukiEtaCarrierDenominator (suzukiArithmeticZetaArgument z) := by
  rw [pairedEtaXiCompletionFactor_mul_suzukiEtaCarrierDenominator hz,
    suzukiArithmeticZetaArgument_eq_one_sub_completedSpectralCoordinate,
    riemannXi_one_sub, deriv_riemannXi_one_sub, suzukiXiEValue_eq, deriv_riemannXiSpectral]
  change riemannXi (completedSpectralCoordinate z) + I *
    (I * deriv riemannXi (completedSpectralCoordinate z)) = _
  rw [← mul_assoc, I_mul_I]
  ring

/-- Genuine nonvanishing of the original denominator transports exactly
to the arithmetic denominator; eta itself is allowed to vanish. -/
theorem suzukiEtaCarrierDenominator_ne_zero_iff {z : ℂ}
    (hz : suzukiArithmeticZetaArgument z ∈ suzukiEtaStrip) :
    suzukiEtaCarrierDenominator (suzukiArithmeticZetaArgument z) ≠ 0 ↔ suzukiXiEValue z ≠ 0 := by
  rw [suzukiXiEValue_eq_etaCarrierDenominator hz, mul_ne_zero_iff]
  exact ⟨fun h => ⟨pairedEtaXiCompletionFactor_ne_zero hz.1 hz.2, h⟩, And.right⟩

/-- The original complex carrier equals its arithmetic eta quotient on
the true denominator-nonzero domain, including simple xi-node values. -/
theorem suzukiXiZeroCarrier_eq_etaCarrier {z : ℂ}
    (hz : suzukiArithmeticZetaArgument z ∈ suzukiEtaStrip) (hE : suzukiXiEValue z ≠ 0) :
    suzukiXiZeroCarrier z = suzukiEtaCarrier (suzukiArithmeticZetaArgument z) := by
  have hxi : riemannXiSpectral z = pairedEtaXiCompletionFactor (suzukiArithmeticZetaArgument z) *
      pairedEtaCore (suzukiArithmeticZetaArgument z) := by
    rw [show pairedEtaXiCompletionFactor (suzukiArithmeticZetaArgument z) *
        pairedEtaCore (suzukiArithmeticZetaArgument z) =
        riemannXi (suzukiArithmeticZetaArgument z) from pairedEtaCompletedXi_eq_riemannXi hz.1 hz.2,
      suzukiArithmeticZetaArgument_eq_one_sub_completedSpectralCoordinate, riemannXi_one_sub]
    rfl
  rw [suzukiXiZeroCarrier_eq_i_mul_xi_div_E hE, hxi, suzukiXiEValue_eq_etaCarrierDenominator hz]
  unfold suzukiEtaCarrier
  have hn := pairedEtaXiCompletionFactor_ne_zero hz.1 hz.2
  field_simp

/-- The complete finite eta denominators converge locally uniformly,
without removing their zeros or imposing simplicity. -/
theorem tendstoLocallyUniformlyOn_suzukiEtaFiniteCarrierDenominator :
    TendstoLocallyUniformlyOn suzukiEtaFiniteCarrierDenominator suzukiEtaCarrierDenominator
      atTop suzukiEtaStrip := by
  have hsub : suzukiEtaStrip ⊆ {s : ℂ | 0 < s.re} := fun _ hs => hs.1
  have hc : ContinuousOn (fun s => 1 + pairedEtaArithmeticXiRegularCorrection s) suzukiEtaStrip :=
    fun s hs => (analyticAt_const.add
      (analyticAt_pairedEtaArithmeticXiRegularCorrection hs)).continuousAt.continuousWithinAt
  have hEta := tendstoLocallyUniformlyOn_pairedEtaCorePartialSum.mono hsub
  have hD := tendstoLocallyUniformlyOn_pairedEtaCoreDerivativePartialSum.mono hsub
  have hcst : TendstoLocallyUniformlyOn (fun _ : ℕ => fun s =>
      1 + pairedEtaArithmeticXiRegularCorrection s)
      (fun s => 1 + pairedEtaArithmeticXiRegularCorrection s) atTop suzukiEtaStrip :=
    tendstoLocallyUniformlyOn_const_index _
  have hmul := hcst.fun_mul₀ hEta hc (analyticOnNhd_pairedEtaCore.mono hsub).continuousOn
  exact hD.fun_add hmul

/-- The carrier's arithmetic nonzero domain removes only the true
denominator, not every xi or eta zero. -/
def suzukiEtaCarrierDomain : Set ℂ :=
  {s | s ∈ suzukiEtaStrip ∧ suzukiEtaCarrierDenominator s ≠ 0}

/-- Finite arithmetic carriers converge locally uniformly on the true
denominator-nonzero domain. Interior pole orders play no role here. -/
theorem tendstoLocallyUniformlyOn_suzukiEtaFiniteCarrier :
    TendstoLocallyUniformlyOn suzukiEtaFiniteCarrier suzukiEtaCarrier
      atTop suzukiEtaCarrierDomain := by
  have hsub : suzukiEtaCarrierDomain ⊆ {s : ℂ | 0 < s.re} := fun _ hs => hs.1.1
  have hEta := tendstoLocallyUniformlyOn_pairedEtaCorePartialSum.mono hsub
  have hD := tendstoLocallyUniformlyOn_suzukiEtaFiniteCarrierDenominator.mono
    (show suzukiEtaCarrierDomain ⊆ suzukiEtaStrip from fun _ hs => hs.1)
  have hnum : ContinuousOn (fun s => I * pairedEtaCore s) suzukiEtaCarrierDomain :=
    continuousOn_const.mul (analyticOnNhd_pairedEtaCore.mono hsub).continuousOn
  have hden : ContinuousOn suzukiEtaCarrierDenominator suzukiEtaCarrierDomain :=
    fun s hs => (analyticAt_suzukiEtaCarrierDenominator hs.1).continuousAt.continuousWithinAt
  have hI : TendstoLocallyUniformlyOn (fun _ : ℕ => fun _ : ℂ => I)
      (fun _ => I) atTop suzukiEtaCarrierDomain :=
    tendstoLocallyUniformlyOn_const_index _
  have hn := hI.fun_mul₀ hEta continuousOn_const (analyticOnNhd_pairedEtaCore.mono hsub).continuousOn
  exact hn.fun_div₀ hD hnum hden (fun _ hs => hs.2)

end
end RiemannGaussian
