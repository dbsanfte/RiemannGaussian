/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierSmoothExcision
import RiemannGaussian.SuzukiEtaExtendedCarrier

/-!
# The full smooth signed area source in literal eta arithmetic

The common nonzero completion factor cancels homogeneously, without
requiring either eta or the actual carrier denominator to be nonzero.
The spatial source keeps the reflected-coordinate Jacobian. Its eta
Wronskian cancels the first completion derivative exactly, leaving the
eta curvature and the full explicit completion curvature together.
No sign or independent area bound is assumed or concluded.
-/

open Complex Filter Set Topology
namespace RiemannGaussian
noncomputable section

/-- Homogeneous smoothing of the actual eta numerator and denominator.
The zero values at common zeros will be transported from the true carrier. -/
def suzukiEtaSmoothCarrier (r : ℝ) (s : ℂ) : ℂ :=
  complexSmoothQuotient r (I * pairedEtaCore s) (suzukiEtaCarrierDenominator s)

/-- The arithmetic expression for the source in spectral coordinates.
The leading `i` retains the Jacobian of `s=1/2-i*z`. -/
def suzukiEtaSpectralSmoothSource (r : ℝ) (s : ℂ) : ℂ :=
  2 * I * (r : ℂ) ^ 2 * pairedEtaCore s ^ 2 *
    starRingEnd ℂ (deriv pairedEtaCore s * suzukiEtaCarrierDenominator s -
      pairedEtaCore s * deriv suzukiEtaCarrierDenominator s) /
      ((normSq (suzukiEtaCarrierDenominator s) + r ^ 2 * normSq (pairedEtaCore s) : ℝ) : ℂ) ^ 2

private lemma argument_derivative (z : ℂ) :
    HasDerivAt suzukiArithmeticZetaArgument (-I) z := by
  unfold suzukiArithmeticZetaArgument
  simpa only [mul_one, zero_mul, zero_add, zero_sub, id_eq] using
    (hasDerivAt_const z (1/2 : ℂ)).fun_sub ((hasDerivAt_const z I).fun_mul (hasDerivAt_id z))

private lemma spectral_xi_completion {z : ℂ}
    (hz : suzukiArithmeticZetaArgument z ∈ pairedEtaCompletionDomain) :
    riemannXiSpectral z = pairedEtaXiCompletionFactor (suzukiArithmeticZetaArgument z) *
      pairedEtaCore (suzukiArithmeticZetaArgument z) := by
  rw [show pairedEtaXiCompletionFactor (suzukiArithmeticZetaArgument z) *
      pairedEtaCore (suzukiArithmeticZetaArgument z) = riemannXi (suzukiArithmeticZetaArgument z) from
      pairedEtaCompletedXi_eq_riemannXi_on_completionDomain hz,
    suzukiArithmeticZetaArgument_eq_one_sub_completedSpectralCoordinate, riemannXi_one_sub]
  rfl

/-- The complete complex completion factor cancels, including at genuine
carrier poles and common xi zeros. No denominator-zero exclusion is imposed. -/
theorem suzukiXiSmoothCarrier_eq_eta (r : ℝ) {z : ℂ}
    (hz : suzukiArithmeticZetaArgument z ∈ pairedEtaCompletionDomain) :
    suzukiXiSmoothCarrier r z = suzukiEtaSmoothCarrier r (suzukiArithmeticZetaArgument z) := by
  rw [suzukiXiSmoothCarrier, spectral_xi_completion hz,
    suzukiXiEValue_eq_etaCarrierDenominator_on_completionDomain hz]
  rw [show I * (pairedEtaXiCompletionFactor (suzukiArithmeticZetaArgument z) *
      pairedEtaCore (suzukiArithmeticZetaArgument z)) =
      pairedEtaXiCompletionFactor (suzukiArithmeticZetaArgument z) *
        (I * pairedEtaCore (suzukiArithmeticZetaArgument z)) by ring]
  exact complexSmoothQuotient_mul r _ _ (pairedEtaXiCompletionFactor_ne_zero_on_completionDomain hz)

/-- The literal eta smooth carrier has the same global algebraic bound,
with no exception at zeros of its denominator or numerator. -/
theorem norm_suzukiEtaSmoothCarrier_le {r : ℝ} (hr : 0 < r) (s : ℂ) :
    ‖suzukiEtaSmoothCarrier r s‖ ≤ 1/(2*r) := norm_complexSmoothQuotient_le hr _ _

/-- The full actual signed source equals its eta Wronskian expression,
including at all original carrier poles and at common xi zeros. -/
theorem suzukiXiSmoothCarrierSource_eq_eta {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : suzukiArithmeticZetaArgument z ∈ pairedEtaCompletionDomain) :
    suzukiXiSmoothCarrierSource r z = suzukiEtaSpectralSmoothSource r (suzukiArithmeticZetaArgument z) := by
  let s := suzukiArithmeticZetaArgument z
  change suzukiXiSmoothCarrierSource r z = suzukiEtaSpectralSmoothSource r s
  by_cases hEta : pairedEtaCore s = 0
  · have hA : riemannXiSpectral z = 0 :=
      (spectral_xi_completion hz).trans (mul_eq_zero_of_right _ hEta)
    simp [suzukiXiSmoothCarrierSource, suzukiEtaSpectralSmoothSource, hA, hEta]
  · have hf : HasDerivAt (fun w => I * pairedEtaCore (suzukiArithmeticZetaArgument w))
        (I * (deriv pairedEtaCore s * -I)) z :=
      by simpa only [Function.comp_def] using
        (((analyticOnNhd_pairedEtaCore s hz.1).differentiableAt.hasDerivAt.comp z
          (argument_derivative z)).const_mul I)
    have hg : HasDerivAt (fun w => suzukiEtaCarrierDenominator (suzukiArithmeticZetaArgument w))
        (deriv suzukiEtaCarrierDenominator s * -I) z :=
      ((analyticAt_suzukiEtaCarrierDenominator_on_completionDomain hz).differentiableAt.hasDerivAt.comp z
        (argument_derivative z))
    have hnear : suzukiXiSmoothCarrier r =ᶠ[𝓝 z] fun w => suzukiEtaSmoothCarrier r (suzukiArithmeticZetaArgument w) := by
      filter_upwards [(argument_derivative z).continuousAt.preimage_mem_nhds
        (isOpen_pairedEtaCompletionDomain.mem_nhds hz)] with w hw
      exact suzukiXiSmoothCarrier_eq_eta r hw
    have hCG : complexCauchyGreenSource (suzukiXiSmoothCarrier r) z =
        complexCauchyGreenSource (fun w => suzukiEtaSmoothCarrier r (suzukiArithmeticZetaArgument w)) z := by
      unfold complexCauchyGreenSource
      rw [hnear.fderiv_eq]
    rw [← complexCauchyGreenSource_suzukiXiSmoothCarrier hr, hCG]
    unfold suzukiEtaSmoothCarrier
    rw [complexCauchyGreenSource_complexSmoothQuotient hr hf.differentiableAt hg.differentiableAt
      (Or.inl (mul_ne_zero I_ne_zero hEta)), hf.deriv, hg.deriv]
    unfold suzukiEtaSpectralSmoothSource
    dsimp only [s]
    simp only [map_mul, map_sub, map_neg, conj_I, normSq_I, one_mul]
    congr 1
    ring_nf
    simp

/-- The first completion derivative cancels from the exact eta
Wronskian. The remaining completion curvature keeps its full complex sign. -/
theorem suzukiEtaCarrier_wronskian_eq_curvature {s : ℂ} (hs : s ∈ pairedEtaCompletionDomain) :
    deriv pairedEtaCore s * suzukiEtaCarrierDenominator s -
      pairedEtaCore s * deriv suzukiEtaCarrierDenominator s =
    deriv pairedEtaCore s ^ 2 - pairedEtaCore s * deriv (deriv pairedEtaCore) s -
      deriv pairedEtaArithmeticXiRegularCorrection s * pairedEtaCore s ^ 2 := by
  have hEta := analyticOnNhd_pairedEtaCore s hs.1
  have hQ := analyticAt_pairedEtaArithmeticXiRegularCorrection_on_completionDomain hs
  have he : suzukiEtaCarrierDenominator =ᶠ[𝓝 s] fun w =>
      deriv pairedEtaCore w + (1 + pairedEtaArithmeticXiRegularCorrection w) * pairedEtaCore w := by
    filter_upwards [(Complex.isOpen_re_gt 0).mem_nhds hs.1] with w hw
    rw [suzukiEtaCarrierDenominator, ← (hasDerivAt_pairedEtaCore_arithmeticDerivativeValue hw).deriv]
  have hd := he.deriv_eq.trans
    (hEta.deriv.differentiableAt.hasDerivAt.add
      ((hQ.differentiableAt.hasDerivAt.const_add 1).mul hEta.differentiableAt.hasDerivAt)).deriv
  rw [hd, suzukiEtaCarrierDenominator, ← (hasDerivAt_pairedEtaCore_arithmeticDerivativeValue hs.1).deriv]
  ring

/-- The actual arithmetic source after exact cancellation of the
first completion derivative. No separate norm estimates destroy the
eta/completion curvature cancellation. -/
theorem suzukiEtaSpectralSmoothSource_eq_curvature (r : ℝ) {s : ℂ}
    (hs : s ∈ pairedEtaCompletionDomain) :
    suzukiEtaSpectralSmoothSource r s =
      2 * I * (r : ℂ) ^ 2 * pairedEtaCore s ^ 2 *
        starRingEnd ℂ (deriv pairedEtaCore s ^ 2 - pairedEtaCore s * deriv (deriv pairedEtaCore) s -
          deriv pairedEtaArithmeticXiRegularCorrection s * pairedEtaCore s ^ 2) /
        ((normSq (suzukiEtaCarrierDenominator s) + r ^ 2 * normSq (pairedEtaCore s) : ℝ) : ℂ) ^ 2 := by
  unfold suzukiEtaSpectralSmoothSource
  rw [suzukiEtaCarrier_wronskian_eq_curvature hs]

/-- The complete original reflection area density has a literal eta
expression retaining both signed Gaussian terms, throughout the full
completion domain and through every genuine carrier pole there. -/
theorem suzukiXiSmoothReflectionSource_eq_eta (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r)
    (x tau : ℝ) {z : ℂ} (hz : suzukiArithmeticZetaArgument z ∈ pairedEtaCompletionDomain) :
    suzukiXiSmoothReflectionSource rho r x tau z =
      suzukiXiReflectionWeight rho z *
        (suzukiSmoothSpectralBoundaryHeat x tau z * suzukiEtaSpectralSmoothSource r (suzukiArithmeticZetaArgument z) -
          I * suzukiEtaSmoothCarrier r (suzukiArithmeticZetaArgument z) *
            suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau (I * z)) := by
  unfold suzukiXiSmoothReflectionSource suzukiXiSmoothBoundaryHeatBulk
  rw [suzukiXiSmoothCarrierSource_eq_eta hr hz, suzukiXiSmoothCarrier_eq_eta r hz]

end
end RiemannGaussian
