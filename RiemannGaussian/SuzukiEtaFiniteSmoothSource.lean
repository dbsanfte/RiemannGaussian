/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaSmoothSource

/-!
# Finite arithmetic recovery of the full smooth signed source

The original finite paired eta sums and their complete denominator recover
the signed source even at genuine carrier poles of arbitrary order.
Only common numerator/denominator zeros are excluded from quotient
convergence; the polynomial curvature convergence includes them too.
These are actual convergence theorems, not independent sign estimates.
No exchange with an area or puncture limit is asserted.
-/

open Complex Filter Set Topology
namespace RiemannGaussian
noncomputable section

/-- Smooth carrier formed from the literal finite eta prefix. -/
def suzukiEtaFiniteSmoothCarrier (r : ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  complexSmoothQuotient r (I * pairedEtaCorePartialSum N s) (suzukiEtaFiniteCarrierDenominator N s)

/-- The full finite arithmetic source in spectral coordinates. -/
def suzukiEtaFiniteSpectralSmoothSource (r : ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  2 * I * (r : ℂ) ^ 2 * pairedEtaCorePartialSum N s ^ 2 *
    starRingEnd ℂ (deriv (pairedEtaCorePartialSum N) s * suzukiEtaFiniteCarrierDenominator N s -
      pairedEtaCorePartialSum N s * deriv (suzukiEtaFiniteCarrierDenominator N) s) /
      ((normSq (suzukiEtaFiniteCarrierDenominator N s) + r ^ 2 * normSq (pairedEtaCorePartialSum N s) : ℝ) : ℂ) ^ 2

/-- The full reflection-weighted finite density retains both original
Gaussian terms, all odd/even eta coefficients and their complex phases. -/
def suzukiEtaFiniteSmoothReflectionSource (rho : NontrivialZetaZero) (r x tau : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  suzukiXiReflectionWeight rho z *
    (suzukiSmoothSpectralBoundaryHeat x tau z * suzukiEtaFiniteSpectralSmoothSource r N (suzukiArithmeticZetaArgument z) -
      I * suzukiEtaFiniteSmoothCarrier r N (suzukiArithmeticZetaArgument z) *
        suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau (I*z))

private lemma eta_derivative_limit {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N => deriv (pairedEtaCorePartialSum N) s) atTop (𝓝 (deriv pairedEtaCore s)) :=
  (tendstoLocallyUniformlyOn_pairedEtaCorePartialSum.deriv
    (Eventually.of_forall fun N => (differentiable_pairedEtaCorePartialSum N).differentiableOn)
    (Complex.isOpen_re_gt 0)).tendsto_at hs

private lemma denominator_derivative_limit {s : ℂ} (hs : s ∈ pairedEtaCompletionDomain) :
    Tendsto (fun N => deriv (suzukiEtaFiniteCarrierDenominator N) s) atTop
      (𝓝 (deriv suzukiEtaCarrierDenominator s)) :=
  (tendstoLocallyUniformlyOn_suzukiEtaFiniteCarrierDenominator_on_completionDomain.deriv
    (Eventually.of_forall fun N _ hs =>
      (analyticAt_suzukiEtaFiniteCarrierDenominator_on_completionDomain N hs).differentiableAt.differentiableWithinAt)
    isOpen_pairedEtaCompletionDomain).tendsto_at hs

/-- Every literal finite prefix has the same cancellation of the first
completion derivative; its entire second derivative remains explicit. -/
theorem suzukiEtaFiniteCarrier_wronskian_eq_curvature (N : ℕ) {s : ℂ}
    (hs : s ∈ pairedEtaCompletionDomain) :
    deriv (pairedEtaCorePartialSum N) s * suzukiEtaFiniteCarrierDenominator N s -
      pairedEtaCorePartialSum N s * deriv (suzukiEtaFiniteCarrierDenominator N) s =
      deriv (pairedEtaCorePartialSum N) s ^ 2 -
        pairedEtaCorePartialSum N s * deriv (deriv (pairedEtaCorePartialSum N)) s -
        deriv pairedEtaArithmeticXiRegularCorrection s * pairedEtaCorePartialSum N s ^ 2 := by
  have hEta := (differentiable_pairedEtaCorePartialSum N).analyticAt s
  have hQ := analyticAt_pairedEtaArithmeticXiRegularCorrection_on_completionDomain hs
  have he : suzukiEtaFiniteCarrierDenominator N = fun w =>
      deriv (pairedEtaCorePartialSum N) w + (1 + pairedEtaArithmeticXiRegularCorrection w) * pairedEtaCorePartialSum N w := by
    funext w
    rw [suzukiEtaFiniteCarrierDenominator, deriv_pairedEtaCorePartialSum]
  have hd := congrArg (fun f : ℂ → ℂ => deriv f s) he
  rw [(hEta.deriv.differentiableAt.hasDerivAt.fun_add
    ((hQ.differentiableAt.hasDerivAt.const_add 1).fun_mul hEta.differentiableAt.hasDerivAt)).deriv] at hd
  rw [hd, he]
  ring

/-- The full finite eta Wronskians converge to the actual eta and
completion curvature, including at all common zeros. -/
theorem tendsto_suzukiEtaFiniteCarrier_wronskian_curvature {s : ℂ}
    (hs : s ∈ pairedEtaCompletionDomain) :
    Tendsto (fun N => deriv (pairedEtaCorePartialSum N) s * suzukiEtaFiniteCarrierDenominator N s -
      pairedEtaCorePartialSum N s * deriv (suzukiEtaFiniteCarrierDenominator N) s) atTop
      (𝓝 (deriv pairedEtaCore s ^ 2 - pairedEtaCore s * deriv (deriv pairedEtaCore) s -
        deriv pairedEtaArithmeticXiRegularCorrection s * pairedEtaCore s ^ 2)) := by
  rw [← suzukiEtaCarrier_wronskian_eq_curvature hs]
  exact ((eta_derivative_limit hs.1).mul
    (tendstoLocallyUniformlyOn_suzukiEtaFiniteCarrierDenominator_on_completionDomain.tendsto_at hs)).sub
      ((tendstoLocallyUniformlyOn_pairedEtaCorePartialSum.tendsto_at hs.1).mul (denominator_derivative_limit hs))

private lemma norm_denominator_limit (r : ℝ) {s : ℂ} (hs : s ∈ pairedEtaCompletionDomain) :
    Tendsto (fun N => ((normSq (suzukiEtaFiniteCarrierDenominator N s) +
      r ^ 2 * normSq (pairedEtaCorePartialSum N s) : ℝ) : ℂ)) atTop
      (𝓝 ((normSq (suzukiEtaCarrierDenominator s) + r ^ 2 * normSq (pairedEtaCore s) : ℝ) : ℂ)) := by
  have hE := tendstoLocallyUniformlyOn_pairedEtaCorePartialSum.tendsto_at hs.1
  have hD := tendstoLocallyUniformlyOn_suzukiEtaFiniteCarrierDenominator_on_completionDomain.tendsto_at hs
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp
    (((Complex.continuous_normSq.continuousAt.tendsto.comp hD)).add
      ((Complex.continuous_normSq.continuousAt.tendsto.comp hE).const_mul (r^2)))

private lemma norm_denominator_ne_zero {r : ℝ} (hr : 0 < r) {s : ℂ}
    (hn : pairedEtaCore s ≠ 0 ∨ suzukiEtaCarrierDenominator s ≠ 0) :
    ((normSq (suzukiEtaCarrierDenominator s) + r ^ 2 * normSq (pairedEtaCore s) : ℝ) : ℂ) ≠ 0 := by
  have hp := complexSmoothQuotient_denominator_pos hr hn
  exact_mod_cast hp.ne'

/-- Genuine carrier poles need no exclusion from finite smooth-carrier
recovery. The only excluded case is a common eta/denominator zero. -/
theorem tendsto_suzukiEtaFiniteSmoothCarrier {r : ℝ} (hr : 0 < r) {s : ℂ}
    (hs : s ∈ pairedEtaCompletionDomain)
    (hn : pairedEtaCore s ≠ 0 ∨ suzukiEtaCarrierDenominator s ≠ 0) :
    Tendsto (fun N => suzukiEtaFiniteSmoothCarrier r N s) atTop (𝓝 (suzukiEtaSmoothCarrier r s)) := by
  have hE := tendstoLocallyUniformlyOn_pairedEtaCorePartialSum.tendsto_at hs.1
  have hD := tendstoLocallyUniformlyOn_suzukiEtaFiniteCarrierDenominator_on_completionDomain.tendsto_at hs
  have hnum := (hE.const_mul I).mul (Complex.continuous_conj.continuousAt.tendsto.comp hD)
  have ht := hnum.div (norm_denominator_limit r hs) (norm_denominator_ne_zero hr hn)
  have he (a b : ℂ) : complexSmoothQuotient r (I*a) b =
      I*a*starRingEnd ℂ b / ((normSq b + r^2*normSq a : ℝ) : ℂ) := by
    rw [complexSmoothQuotient, complexSmoothQuotient_denominator]
    simp only [map_mul, normSq_I, one_mul]
  rw [show suzukiEtaSmoothCarrier r s = I * pairedEtaCore s * starRingEnd ℂ (suzukiEtaCarrierDenominator s) /
    ((normSq (suzukiEtaCarrierDenominator s) + r^2*normSq (pairedEtaCore s) : ℝ) : ℂ) from he _ _]
  apply ht.congr'
  filter_upwards with N
  exact (he _ _).symm

/-- The complete finite signed source converges through every genuine
carrier pole, without any assumption of simplicity or a denominator gap. -/
theorem tendsto_suzukiEtaFiniteSpectralSmoothSource {r : ℝ} (hr : 0 < r) {s : ℂ}
    (hs : s ∈ pairedEtaCompletionDomain)
    (hn : pairedEtaCore s ≠ 0 ∨ suzukiEtaCarrierDenominator s ≠ 0) :
    Tendsto (fun N => suzukiEtaFiniteSpectralSmoothSource r N s) atTop
      (𝓝 (suzukiEtaSpectralSmoothSource r s)) := by
  have hE := tendstoLocallyUniformlyOn_pairedEtaCorePartialSum.tendsto_at hs.1
  have hW := tendsto_suzukiEtaFiniteCarrier_wronskian_curvature hs
  rw [← suzukiEtaCarrier_wronskian_eq_curvature hs] at hW
  have hnum := ((hE.pow 2).const_mul (2*I*(r:ℂ)^2)).mul
    (Complex.continuous_conj.continuousAt.tendsto.comp hW)
  exact hnum.div ((norm_denominator_limit r hs).pow 2) (pow_ne_zero 2 (norm_denominator_ne_zero hr hn))

/-- Both signed terms of the original reflection area density are
recovered by the same literal finite eta prefix, through all genuine
carrier poles. This is pointwise convergence, with no integral exchange. -/
theorem tendsto_suzukiEtaFiniteSmoothReflectionSource (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r)
    (x tau : ℝ) {z : ℂ} (hz : suzukiArithmeticZetaArgument z ∈ pairedEtaCompletionDomain)
    (hn : pairedEtaCore (suzukiArithmeticZetaArgument z) ≠ 0 ∨
      suzukiEtaCarrierDenominator (suzukiArithmeticZetaArgument z) ≠ 0) :
    Tendsto (fun N => suzukiEtaFiniteSmoothReflectionSource rho r x tau N z) atTop
      (𝓝 (suzukiXiSmoothReflectionSource rho r x tau z)) := by
  rw [suzukiXiSmoothReflectionSource_eq_eta rho hr x tau hz]
  exact (((tendsto_suzukiEtaFiniteSpectralSmoothSource hr hz hn).const_mul
    (suzukiSmoothSpectralBoundaryHeat x tau z)).sub
      (((tendsto_suzukiEtaFiniteSmoothCarrier hr hz hn).const_mul I).mul_const
        (suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau (I*z)))).const_mul (suzukiXiReflectionWeight rho z)

/-- Every genuine upper carrier pole of arbitrary order is covered by
finite recovery of the full signed reflection density. The arithmetic
domain and noncommon-zero conditions are derived from the actual pole;
no extra analytic approximation hypothesis is left to the caller. -/
theorem tendsto_suzukiEtaFiniteSmoothReflectionSource_at_upper_pole
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (x tau : ℝ) {z : ℂ}
    (hupper : 0 < z.im) (hE : suzukiXiEValue z = 0) (hA : riemannXiSpectral z ≠ 0) :
    Tendsto (fun N => suzukiEtaFiniteSmoothReflectionSource rho r x tau N z) atTop
      (𝓝 (suzukiXiSmoothReflectionSource rho r x tau z)) := by
  have hhalf : z.im < 1/2 := by
    by_contra! h
    exact suzukiXiEValue_ne_zero_of_half_le_im h hE
  have hs : suzukiArithmeticZetaArgument z ∈ pairedEtaCompletionDomain :=
    mem_pairedEtaCompletionDomain_of_re_lt_one
      (by rw [suzukiArithmeticZetaArgument_re]; linarith)
      (by rw [suzukiArithmeticZetaArgument_re]; linarith)
  apply tendsto_suzukiEtaFiniteSmoothReflectionSource rho hr x tau hs
  left
  intro he
  apply hA
  have hxi : pairedEtaXiCompletionFactor (suzukiArithmeticZetaArgument z) *
      pairedEtaCore (suzukiArithmeticZetaArgument z) = riemannXiSpectral z := by
    rw [show pairedEtaXiCompletionFactor (suzukiArithmeticZetaArgument z) *
        pairedEtaCore (suzukiArithmeticZetaArgument z) = riemannXi (suzukiArithmeticZetaArgument z) from
      pairedEtaCompletedXi_eq_riemannXi_on_completionDomain hs,
      suzukiArithmeticZetaArgument_eq_one_sub_completedSpectralCoordinate, riemannXi_one_sub]
    rfl
  rw [← hxi, he, mul_zero]

end
end RiemannGaussian
