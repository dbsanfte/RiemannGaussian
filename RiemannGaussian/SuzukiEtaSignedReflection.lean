/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaSignedCurrent

/-!
# Signed current bound for the complete reflection density

The complex reflection weight and original Gaussian are substituted into
the actual normalized eta-source inequality. Their differentiability is
proved from the original analytic and smooth functions. The companion
Gaussian term remains signed. No estimate below the global zero source
is asserted for the resulting derivative and phase costs.
-/

open Complex Filter Set Topology
namespace RiemannGaussian
noncomputable section

/-- The spectral point corresponding to the positively oriented
arithmetic vertical line s=sigma+i*t. -/
def suzukiEtaVerticalSpectralPoint (sigma t : ℝ) : ℂ :=
  -(t : ℂ) + ((sigma - 1/2 : ℝ) : ℂ) * I

/-- The affine arithmetic/spectral conversion is exact. -/
theorem suzukiArithmeticZetaArgument_verticalSpectralPoint (sigma t : ℝ) :
    suzukiArithmeticZetaArgument (suzukiEtaVerticalSpectralPoint sigma t) =
      pairedEtaVerticalArgument sigma t := by
  unfold suzukiArithmeticZetaArgument suzukiEtaVerticalSpectralPoint pairedEtaVerticalArgument
  push_cast
  ring_nf
  simp only [I_sq]
  ring

/-- The actual complex reflection and Gaussian weight on that line. -/
def suzukiEtaVerticalReflectionHeatWeight (rho : NontrivialZetaZero) (x tau sigma t : ℝ) : ℂ :=
  suzukiXiReflectionWeight rho (suzukiEtaVerticalSpectralPoint sigma t) *
    suzukiSmoothSpectralBoundaryHeat x tau (suzukiEtaVerticalSpectralPoint sigma t)

/-- The full upper expression is an explicit derivative current, a phase
cost, the completion curvature, and the signed companion Gaussian term.
No one of these terms is presumed negligible. -/
def suzukiEtaReflectionCurrentUpper (rho : NontrivialZetaZero) (r x tau sigma t : ℝ) : ℝ :=
  let z := suzukiEtaVerticalSpectralPoint sigma t
  let s := pairedEtaVerticalArgument sigma t
  let K := suzukiEtaNormalizedCurvatureWeight (suzukiEtaVerticalReflectionHeatWeight rho x tau sigma) r sigma
  let T := pairedEtaVerticalQuarticCurrent sigma
  let J := pairedEtaCore s * starRingEnd ℂ (deriv pairedEtaCore s)
  2 * r ^ 2 *
    ((deriv (fun u => K u * T u) t).im - (deriv K t * T t).im +
      2 * (‖K t‖ - (K t).re) * normSq J -
      normSq (pairedEtaCore s) ^ 2 * (K t * starRingEnd ℂ (deriv pairedEtaArithmeticXiRegularCorrection s)).re) -
    (suzukiXiReflectionWeight rho z * suzukiEtaSmoothCarrier r s *
      suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau (I * z)).re

/-- Every analytic hypothesis for the actual weight is discharged away
from the two original reflection nodes. Carrier poles are included. -/
theorem differentiableAt_suzukiEtaVerticalReflectionHeatWeight
    (rho : NontrivialZetaZero) (x tau : ℝ) {sigma t : ℝ}
    (ha : suzukiEtaVerticalSpectralPoint sigma t ≠ zetaSpectralCoordinate rho.1)
    (hb : suzukiEtaVerticalSpectralPoint sigma t ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1)) :
    DifferentiableAt ℝ (suzukiEtaVerticalReflectionHeatWeight rho x tau sigma) t := by
  have hz : DifferentiableAt ℝ (suzukiEtaVerticalSpectralPoint sigma) t := by
    unfold suzukiEtaVerticalSpectralPoint
    fun_prop
  exact (((analyticAt_suzukiXiReflectionWeight rho ha hb).differentiableAt.restrictScalars ℝ).comp t hz).mul
    ((differentiable_suzukiSmoothSpectralBoundaryHeat x tau _).comp t hz)

/-- The full original reflection density satisfies the signed current
upper bound, with all weight regularity proved for the actual functions.
This pointwise bound still requires an independent estimate of its full
right-hand side to reach a zero exclusion. -/
theorem suzukiXiSmoothReflectionSource_im_le_current
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (x tau : ℝ) {sigma t : ℝ}
    (hs : pairedEtaVerticalArgument sigma t ∈ pairedEtaCompletionDomain)
    (hn : pairedEtaCore (pairedEtaVerticalArgument sigma t) ≠ 0 ∨
      suzukiEtaCarrierDenominator (pairedEtaVerticalArgument sigma t) ≠ 0)
    (ha : suzukiEtaVerticalSpectralPoint sigma t ≠ zetaSpectralCoordinate rho.1)
    (hb : suzukiEtaVerticalSpectralPoint sigma t ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1)) :
    (suzukiXiSmoothReflectionSource rho r x tau (suzukiEtaVerticalSpectralPoint sigma t)).im ≤
      suzukiEtaReflectionCurrentUpper rho r x tau sigma t := by
  have h := suzukiEtaSpectralSmoothSource_weighted_im_le_current hr
    (differentiableAt_suzukiEtaVerticalReflectionHeatWeight rho x tau ha hb) hs hn
  have he : suzukiXiSmoothReflectionSource rho r x tau (suzukiEtaVerticalSpectralPoint sigma t) =
      suzukiEtaVerticalReflectionHeatWeight rho x tau sigma t *
        suzukiEtaSpectralSmoothSource r (pairedEtaVerticalArgument sigma t) -
      I * (suzukiXiReflectionWeight rho (suzukiEtaVerticalSpectralPoint sigma t) *
        suzukiEtaSmoothCarrier r (pairedEtaVerticalArgument sigma t) *
          suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau (I * suzukiEtaVerticalSpectralPoint sigma t)) := by
    rw [suzukiXiSmoothReflectionSource_eq_eta rho hr x tau
      (by rw [suzukiArithmeticZetaArgument_verticalSpectralPoint]; exact hs),
      suzukiArithmeticZetaArgument_verticalSpectralPoint]
    unfold suzukiEtaVerticalReflectionHeatWeight
    ring
  rw [he, Complex.sub_im]
  simp only [Complex.I_mul_im]
  exact sub_le_sub_right h _

/-- Every genuine upper carrier pole lies in the full eta completion
domain with nonzero eta numerator and zero literal eta denominator.
It also avoids both actual reflection nodes. -/
theorem suzukiEtaUpperPole_arithmetic_geometry (rho : NontrivialZetaZero) {z : ℂ}
    (hupper : 0 < z.im) (hE : suzukiXiEValue z = 0) (hA : riemannXiSpectral z ≠ 0) :
    suzukiArithmeticZetaArgument z ∈ pairedEtaCompletionDomain ∧
      pairedEtaCore (suzukiArithmeticZetaArgument z) ≠ 0 ∧
      suzukiEtaCarrierDenominator (suzukiArithmeticZetaArgument z) = 0 ∧
      z ≠ zetaSpectralCoordinate rho.1 ∧ z ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1) := by
  have hhalf : z.im < 1/2 := by
    by_contra! h
    exact suzukiXiEValue_ne_zero_of_half_le_im h hE
  have hs : suzukiArithmeticZetaArgument z ∈ pairedEtaCompletionDomain :=
    mem_pairedEtaCompletionDomain_of_re_lt_one
      (by rw [suzukiArithmeticZetaArgument_re]; linarith)
      (by rw [suzukiArithmeticZetaArgument_re]; linarith)
  have hxi : pairedEtaXiCompletionFactor (suzukiArithmeticZetaArgument z) *
      pairedEtaCore (suzukiArithmeticZetaArgument z) = riemannXiSpectral z := by
    rw [show pairedEtaXiCompletionFactor (suzukiArithmeticZetaArgument z) *
        pairedEtaCore (suzukiArithmeticZetaArgument z) = riemannXi (suzukiArithmeticZetaArgument z) from
      pairedEtaCompletedXi_eq_riemannXi_on_completionDomain hs,
      suzukiArithmeticZetaArgument_eq_one_sub_completedSpectralCoordinate, riemannXi_one_sub]
    rfl
  have he : pairedEtaCore (suzukiArithmeticZetaArgument z) ≠ 0 := by
    intro hz
    exact hA (hxi.symm.trans (by rw [hz, mul_zero]))
  have hzero : riemannXiSpectral (zetaSpectralCoordinate rho.1) = 0 :=
    (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mpr ⟨rho, rfl⟩
  have hD : suzukiEtaCarrierDenominator (suzukiArithmeticZetaArgument z) = 0 := by
    rw [suzukiXiEValue_eq_etaCarrierDenominator_on_completionDomain hs] at hE
    exact (mul_eq_zero.mp hE).resolve_left (pairedEtaXiCompletionFactor_ne_zero_on_completionDomain hs)
  refine ⟨hs, he, hD, ?_, ?_⟩
  · intro hz
    exact hA (hz ▸ hzero)
  · intro hz
    apply hA
    rw [hz, riemannXiSpectral_conj, hzero, map_zero]

/-- Every genuine upper carrier pole, of arbitrary order, satisfies the
full signed bound. The completion domain, noncommon-zero condition and
both reflection-node exclusions follow from the actual pole itself. -/
theorem suzukiXiSmoothReflectionSource_im_le_current_at_upper_pole
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (x tau : ℝ) {z : ℂ}
    (hupper : 0 < z.im) (hE : suzukiXiEValue z = 0) (hA : riemannXiSpectral z ≠ 0) :
    (suzukiXiSmoothReflectionSource rho r x tau z).im ≤
      suzukiEtaReflectionCurrentUpper rho r x tau (1/2 + z.im) (-z.re) := by
  have hz : suzukiEtaVerticalSpectralPoint (1/2 + z.im) (-z.re) = z := by
    apply Complex.ext <;> simp [suzukiEtaVerticalSpectralPoint]
  have hs : pairedEtaVerticalArgument (1/2 + z.im) (-z.re) = suzukiArithmeticZetaArgument z := by
    rw [← suzukiArithmeticZetaArgument_verticalSpectralPoint, hz]
  obtain ⟨hd, hn, _hD, ha, hb⟩ := suzukiEtaUpperPole_arithmetic_geometry rho hupper hE hA
  simpa only [hz] using suzukiXiSmoothReflectionSource_im_le_current rho hr x tau
    (sigma := 1/2 + z.im) (t := -z.re) (hs ▸ hd) (Or.inl (hs ▸ hn))
    (by simpa only [hz] using ha) (by simpa only [hz] using hb)

end
end RiemannGaussian
