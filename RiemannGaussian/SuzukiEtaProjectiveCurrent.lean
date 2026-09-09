/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaNormalizationSlope

/-!
# The complete eta source as coupled variation of bounded fields

The real normalized eta mass and the complex smooth carrier obey an exact
quadratic relation. Their coupled vertical variation is the full complex
source, retaining the completion correction inside the actual denominator.
Bounded values alone do not bound that variation. Derivative statements here
exclude common numerator/denominator zeros; genuine carrier poles are included.
-/

open Complex Filter Set Topology
namespace RiemannGaussian
noncomputable section

/-- The real eta share of the complete homogeneous denominator. -/
def suzukiEtaNormalizedMass (r : ℝ) (s : ℂ) : ℝ :=
  normSq (pairedEtaCore s) /
    (normSq (suzukiEtaCarrierDenominator s) + r ^ 2 * normSq (pairedEtaCore s))

/-- The normalized mass is nonnegative even at common zeros. -/
theorem suzukiEtaNormalizedMass_nonneg (r : ℝ) (s : ℂ) :
    0 ≤ suzukiEtaNormalizedMass r s := by
  unfold suzukiEtaNormalizedMass
  exact div_nonneg (normSq_nonneg _) (add_nonneg (normSq_nonneg _)
    (mul_nonneg (sq_nonneg _) (normSq_nonneg _)))

/-- A global value bound for the mass, without any zero separation. -/
theorem suzukiEtaNormalizedMass_le {r : ℝ} (hr : 0 < r) (s : ℂ) :
    suzukiEtaNormalizedMass r s ≤ 1 / r ^ 2 := by
  by_cases hn : pairedEtaCore s = 0
  · simp only [suzukiEtaNormalizedMass, hn, normSq_zero, zero_div]
    positivity
  have hp := complexSmoothQuotient_denominator_pos hr
    (b := suzukiEtaCarrierDenominator s) (Or.inl hn)
  apply (div_le_div_iff₀ hp (sq_pos_of_pos hr)).mpr
  nlinarith [normSq_nonneg (suzukiEtaCarrierDenominator s)]

private lemma smooth_carrier_formula (r : ℝ) (s : ℂ) :
    suzukiEtaSmoothCarrier r s = I * pairedEtaCore s *
      starRingEnd ℂ (suzukiEtaCarrierDenominator s) /
        ((normSq (suzukiEtaCarrierDenominator s) + r ^ 2 * normSq (pairedEtaCore s) : ℝ) : ℂ) := by
  rw [suzukiEtaSmoothCarrier, complexSmoothQuotient, complexSmoothQuotient_denominator]
  simp only [map_mul, normSq_I, one_mul]

/-- The bounded mass and complex carrier lie on one exact quadratic
surface. Both the zero-mass and maximal-mass branches are retained. -/
theorem normSq_suzukiEtaSmoothCarrier_eq_mass {r : ℝ} (hr : 0 < r) (s : ℂ) :
    normSq (suzukiEtaSmoothCarrier r s) =
      suzukiEtaNormalizedMass r s - r ^ 2 * suzukiEtaNormalizedMass r s ^ 2 := by
  by_cases hn : pairedEtaCore s = 0
  · simp [suzukiEtaNormalizedMass, suzukiEtaSmoothCarrier, hn]
  have hp := complexSmoothQuotient_denominator_pos hr
    (b := suzukiEtaCarrierDenominator s) (Or.inl hn)
  rw [smooth_carrier_formula]
  simp only [map_div₀, map_mul, normSq_I, one_mul, normSq_conj, normSq_ofReal]
  unfold suzukiEtaNormalizedMass
  field_simp
  ring

/-- At a genuine carrier-denominator zero the mass attains its upper
endpoint exactly. Its value is not a small error at such a pole. -/
theorem suzukiEtaNormalizedMass_at_pole {r : ℝ} (hr : 0 < r) {s : ℂ}
    (hD : suzukiEtaCarrierDenominator s = 0) (hEta : pairedEtaCore s ≠ 0) :
    suzukiEtaNormalizedMass r s = 1 / r ^ 2 := by
  have hn := (normSq_pos.mpr hEta).ne'
  simp only [suzukiEtaNormalizedMass, hD, normSq_zero, zero_add]
  field_simp

private lemma mass_differentiable {r sigma t : ℝ} (hr : 0 < r)
    (hs : pairedEtaVerticalArgument sigma t ∈ pairedEtaCompletionDomain)
    (hn : pairedEtaCore (pairedEtaVerticalArgument sigma t) ≠ 0 ∨
      suzukiEtaCarrierDenominator (pairedEtaVerticalArgument sigma t) ≠ 0) :
    DifferentiableAt ℝ (fun u => suzukiEtaNormalizedMass r (pairedEtaVerticalArgument sigma u)) t ∧
    DifferentiableAt ℝ (suzukiEtaVerticalNormDenominator r sigma) t := by
  have hf := (hasDerivAt_pairedEtaVertical_comp
    (analyticOnNhd_pairedEtaCore _ hs.1).differentiableAt.hasDerivAt).differentiableAt
  have hg := (hasDerivAt_pairedEtaVertical_comp
    (analyticAt_suzukiEtaCarrierDenominator_on_completionDomain hs).differentiableAt.hasDerivAt).differentiableAt
  have hfn : DifferentiableAt ℝ (fun u => normSq (pairedEtaCore (pairedEtaVerticalArgument sigma u))) t := by
    simpa only [normSq_eq_norm_sq] using hf.norm_sq (𝕜 := ℂ)
  have hgn : DifferentiableAt ℝ (fun u => normSq (suzukiEtaCarrierDenominator (pairedEtaVerticalArgument sigma u))) t := by
    simpa only [normSq_eq_norm_sq] using hg.norm_sq (𝕜 := ℂ)
  have hd := hgn.fun_add (hfn.const_mul (r ^ 2))
  have hp := complexSmoothQuotient_denominator_pos hr hn
  exact ⟨hfn.div hd hp.ne', hd⟩

private lemma coupled_variation {f g d : ℝ → ℂ} {f' g' : ℂ} {t : ℝ}
    (hf : HasDerivAt f (I * f') t) (hg : HasDerivAt g (I * g') t)
    (hd : DifferentiableAt ℝ d t) (hz : d t ≠ 0) :
    (I * f t * starRingEnd ℂ (g t) / d t) *
        deriv (fun u => f u * starRingEnd ℂ (f u) / d u) t -
      (f t * starRingEnd ℂ (f t) / d t) *
        deriv (fun u => I * f u * starRingEnd ℂ (g u) / d u) t =
      f t ^ 2 * starRingEnd ℂ (f' * g t - f t * g') / d t ^ 2 := by
  have hm := ((hf.fun_mul hf.star).div hd.hasDerivAt hz).deriv
  have hS := (((hf.const_mul I).fun_mul hg.star).div hd.hasDerivAt hz).deriv
  simp only [star_def] at hm hS
  change deriv (fun u => f u * starRingEnd ℂ (f u) / d u) t = _ at hm
  change deriv (fun u => I * f u * starRingEnd ℂ (g u) / d u) t = _ at hS
  rw [hm, hS]
  simp only [map_mul, map_sub, conj_I]
  field_simp
  ring_nf
  simp only [I_sq]
  ring

/-- The full spectral source is exactly the coupled vertical variation
of two bounded fields. The actual completion denominator is differentiated,
and no complex source component is discarded. -/
theorem suzukiEtaSpectralSmoothSource_eq_mass_current {r sigma t : ℝ} (hr : 0 < r)
    (hs : pairedEtaVerticalArgument sigma t ∈ pairedEtaCompletionDomain)
    (hn : pairedEtaCore (pairedEtaVerticalArgument sigma t) ≠ 0 ∨
      suzukiEtaCarrierDenominator (pairedEtaVerticalArgument sigma t) ≠ 0) :
    suzukiEtaSpectralSmoothSource r (pairedEtaVerticalArgument sigma t) =
      2 * I * (r : ℂ) ^ 2 *
        (suzukiEtaSmoothCarrier r (pairedEtaVerticalArgument sigma t) *
            ((deriv (fun u => suzukiEtaNormalizedMass r (pairedEtaVerticalArgument sigma u)) t : ℝ) : ℂ) -
          (suzukiEtaNormalizedMass r (pairedEtaVerticalArgument sigma t) : ℂ) *
            deriv (fun u => suzukiEtaSmoothCarrier r (pairedEtaVerticalArgument sigma u)) t) := by
  obtain ⟨hm, hd⟩ := mass_differentiable hr hs hn
  have hdc := Complex.ofRealCLM.differentiableAt.comp t hd
  have hp := complexSmoothQuotient_denominator_pos hr hn
  have hz : (suzukiEtaVerticalNormDenominator r sigma t : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have h := coupled_variation
    (hasDerivAt_pairedEtaVertical_comp (analyticOnNhd_pairedEtaCore _ hs.1).differentiableAt.hasDerivAt)
    (hasDerivAt_pairedEtaVertical_comp
      (analyticAt_suzukiEtaCarrierDenominator_on_completionDomain hs).differentiableAt.hasDerivAt)
    hdc hz
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at h
  have hmfun : (fun u => pairedEtaCore (pairedEtaVerticalArgument sigma u) *
      starRingEnd ℂ (pairedEtaCore (pairedEtaVerticalArgument sigma u)) /
        (suzukiEtaVerticalNormDenominator r sigma u : ℂ)) =
      fun u => (suzukiEtaNormalizedMass r (pairedEtaVerticalArgument sigma u) : ℂ) := by
    funext u
    rw [mul_conj]
    simp only [suzukiEtaNormalizedMass, suzukiEtaVerticalNormDenominator, ofReal_div]
  have hSfun : (fun u => I * pairedEtaCore (pairedEtaVerticalArgument sigma u) *
      starRingEnd ℂ (suzukiEtaCarrierDenominator (pairedEtaVerticalArgument sigma u)) /
        (suzukiEtaVerticalNormDenominator r sigma u : ℂ)) =
      fun u => suzukiEtaSmoothCarrier r (pairedEtaVerticalArgument sigma u) := by
    funext u
    exact (smooth_carrier_formula r _).symm
  rw [hmfun, hSfun, hm.hasDerivAt.ofReal_comp.deriv] at h
  rw [congrFun hSfun t, congrFun hmfun t] at h
  rw [h]
  unfold suzukiEtaSpectralSmoothSource suzukiEtaVerticalNormDenominator
  ring

/-- At a genuine denominator zero the actual mass is differentiable
with zero vertical derivative, since it attains its global upper bound. -/
theorem hasDerivAt_suzukiEtaNormalizedMass_zero_at_pole {r sigma t : ℝ} (hr : 0 < r)
    (hs : pairedEtaVerticalArgument sigma t ∈ pairedEtaCompletionDomain)
    (hD : suzukiEtaCarrierDenominator (pairedEtaVerticalArgument sigma t) = 0)
    (hEta : pairedEtaCore (pairedEtaVerticalArgument sigma t) ≠ 0) :
    HasDerivAt (fun u => suzukiEtaNormalizedMass r (pairedEtaVerticalArgument sigma u)) 0 t := by
  have hm := (mass_differentiable hr hs (Or.inl hEta)).1.hasDerivAt
  have hmax : IsLocalMax (fun u => suzukiEtaNormalizedMass r (pairedEtaVerticalArgument sigma u)) t := by
    apply Filter.Eventually.of_forall
    intro u
    change suzukiEtaNormalizedMass r (pairedEtaVerticalArgument sigma u) ≤
      suzukiEtaNormalizedMass r (pairedEtaVerticalArgument sigma t)
    rw [suzukiEtaNormalizedMass_at_pole hr hD hEta]
    exact suzukiEtaNormalizedMass_le hr _
  rw [hmax.hasDerivAt_eq_zero hm] at hm
  exact hm

/-- The exact bounded-field identity reaches the complete original
reflection density, including its signed companion heat term. -/
theorem suzukiXiSmoothReflectionSource_eq_mass_current
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (x tau : ℝ) {sigma t : ℝ}
    (hs : pairedEtaVerticalArgument sigma t ∈ pairedEtaCompletionDomain)
    (hn : pairedEtaCore (pairedEtaVerticalArgument sigma t) ≠ 0 ∨
      suzukiEtaCarrierDenominator (pairedEtaVerticalArgument sigma t) ≠ 0) :
    suzukiXiSmoothReflectionSource rho r x tau (suzukiEtaVerticalSpectralPoint sigma t) =
      suzukiXiReflectionWeight rho (suzukiEtaVerticalSpectralPoint sigma t) *
        (suzukiSmoothSpectralBoundaryHeat x tau (suzukiEtaVerticalSpectralPoint sigma t) *
            (2 * I * (r : ℂ) ^ 2 *
              (suzukiEtaSmoothCarrier r (pairedEtaVerticalArgument sigma t) *
                  ((deriv (fun u => suzukiEtaNormalizedMass r (pairedEtaVerticalArgument sigma u)) t : ℝ) : ℂ) -
                (suzukiEtaNormalizedMass r (pairedEtaVerticalArgument sigma t) : ℂ) *
                  deriv (fun u => suzukiEtaSmoothCarrier r (pairedEtaVerticalArgument sigma u)) t)) -
          I * suzukiEtaSmoothCarrier r (pairedEtaVerticalArgument sigma t) *
            suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau (I * suzukiEtaVerticalSpectralPoint sigma t)) := by
  rw [suzukiXiSmoothReflectionSource_eq_eta rho hr x tau
    (by rw [suzukiArithmeticZetaArgument_verticalSpectralPoint]; exact hs),
    suzukiArithmeticZetaArgument_verticalSpectralPoint,
    suzukiEtaSpectralSmoothSource_eq_mass_current hr hs hn]

/-- At every genuine upper pole the full reflection density retains
exactly the complex vertical slope of the smoothed carrier. All eta
domain and numerator conditions follow from the original xi pole. -/
theorem suzukiXiSmoothReflectionSource_eq_slope_at_upper_pole
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (x tau : ℝ) {z : ℂ}
    (hupper : 0 < z.im) (hE : suzukiXiEValue z = 0) (hA : riemannXiSpectral z ≠ 0) :
    suzukiXiSmoothReflectionSource rho r x tau z =
      -2 * I * suzukiXiReflectionWeight rho z * suzukiSmoothSpectralBoundaryHeat x tau z *
        deriv (fun u => suzukiEtaSmoothCarrier r (pairedEtaVerticalArgument (1/2 + z.im) u)) (-z.re) := by
  have hz : suzukiEtaVerticalSpectralPoint (1/2 + z.im) (-z.re) = z := by
    apply Complex.ext <;> simp [suzukiEtaVerticalSpectralPoint]
  have hs : pairedEtaVerticalArgument (1/2 + z.im) (-z.re) = suzukiArithmeticZetaArgument z := by
    rw [← suzukiArithmeticZetaArgument_verticalSpectralPoint, hz]
  obtain ⟨hd, hn, hD, _ha, _hb⟩ := suzukiEtaUpperPole_arithmetic_geometry rho hupper hE hA
  have h := suzukiXiSmoothReflectionSource_eq_mass_current rho hr x tau (hs ▸ hd) (Or.inl (hs ▸ hn))
  rw [hz, hs] at h
  have hS : suzukiEtaSmoothCarrier r (suzukiArithmeticZetaArgument z) = 0 := by
    simp only [suzukiEtaSmoothCarrier, hD, complexSmoothQuotient_zero_right]
  rw [h, hS, suzukiEtaNormalizedMass_at_pole hr hD hn]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp [hrC]
  ring

end
end RiemannGaussian
