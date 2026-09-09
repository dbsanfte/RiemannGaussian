/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaExtendedCarrier
import RiemannGaussian.SuzukiEtaPhaseEnergy
import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourLocalEtaJensen

/-!
# Clearing the elementary dyadic denominator before counting carrier poles

Multiplying the true eta denominator by its dyadic factor gives an
analytic expression across the dyadic exceptions. Its exact completion
identity retains the square of that factor, so the artificial zeros are
visible rather than counted as genuine carrier poles. On the safe
center line the expression has a fixed positive lower bound.
-/

open Complex Filter Set Topology
namespace RiemannGaussian
noncomputable section

/-- The full eta carrier denominator with its dyadic division cleared.
No eta zero or carrier pole is removed from this analytic expression. -/
def suzukiEtaClearedCarrierDenominator (s : ℂ) : ℂ :=
  pairedEtaFactor s * pairedEtaArithmeticDerivativeValue s +
    ((1 + suzukiChebyshevMellinCompletedCorrection s) * pairedEtaFactor s -
      deriv pairedEtaFactor s) * pairedEtaCore s

/-- Away from a dyadic exception, clearing multiplies the actual
denominator by precisely one copy of the elementary factor. -/
theorem suzukiEtaClearedCarrierDenominator_eq_factor_mul {s : ℂ}
    (hF : pairedEtaFactor s ≠ 0) :
    suzukiEtaClearedCarrierDenominator s = pairedEtaFactor s * suzukiEtaCarrierDenominator s := by
  unfold suzukiEtaClearedCarrierDenominator suzukiEtaCarrierDenominator
  rw [pairedEtaArithmeticXiRegularCorrection_eq_completed_sub_dyadic,
    ← logDeriv_pairedEtaFactor, logDeriv_apply]
  field_simp
  ring

/-- The cleared expression retains the full xi-plus-derivative
denominator and exactly two dyadic factors, even at dyadic zeros. -/
theorem pairedEtaXiCompletionNumerator_mul_clearedCarrierDenominator {s : ℂ}
    (hs : 0 < s.re) (h1 : s ≠ 1) :
    pairedEtaXiCompletionNumerator s * suzukiEtaClearedCarrierDenominator s =
      pairedEtaFactor s ^ 2 * (riemannXi s + deriv riemannXi s) := by
  by_cases hF : pairedEtaFactor s = 0
  · have he : pairedEtaCore s = 0 := by
      rw [pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one hs h1]
      change pairedEtaFactor s * riemannZeta s = 0
      rw [hF, zero_mul]
    simp [suzukiEtaClearedCarrierDenominator, hF, he]
  · rw [suzukiEtaClearedCarrierDenominator_eq_factor_mul hF,
      ← pairedEtaXiCompletionFactor_mul_suzukiEtaCarrierDenominator_on_completionDomain ⟨hs, h1, hF⟩]
    unfold pairedEtaXiCompletionFactor
    field_simp

/-- The Archimedean correction is analytic in the positive half-plane
away from its actual pole at one; dyadic exceptions are irrelevant. -/
theorem analyticAt_suzukiChebyshevMellinCompletedCorrection {s : ℂ}
    (hs : 0 < s.re) (h1 : s ≠ 1) :
    AnalyticAt ℂ suzukiChebyshevMellinCompletedCorrection s := by
  have hG : AnalyticAt ℂ pairedEtaXiCompletionNumerator s := by
    apply DifferentiableOn.analyticAt (s := {w : ℂ | 0 < w.re})
    · intro w hw
      exact (differentiableAt_pairedEtaXiCompletionNumerator hw).differentiableWithinAt
    · exact (Complex.isOpen_re_gt 0).mem_nhds hs
  have he : logDeriv pairedEtaXiCompletionNumerator =ᶠ[𝓝 s]
      suzukiChebyshevMellinCompletedCorrection := by
    filter_upwards [(Complex.isOpen_re_gt 0).mem_nhds hs,
      (isOpen_ne_fun continuous_id continuous_const).mem_nhds h1] with w hw hw1
    exact logDeriv_pairedEtaXiCompletionNumerator_of_re_pos hw hw1
  exact (hG.deriv.div hG (pairedEtaXiCompletionNumerator_ne_zero_of_re_pos hs h1)).congr he

/-- The cleared denominator is analytic throughout the positive
half-plane away from one, including the elementary dyadic zeros. -/
theorem analyticAt_suzukiEtaClearedCarrierDenominator {s : ℂ}
    (hs : 0 < s.re) (h1 : s ≠ 1) :
    AnalyticAt ℂ suzukiEtaClearedCarrierDenominator s := by
  have hF : AnalyticAt ℂ pairedEtaFactor s :=
    (show Differentiable ℂ pairedEtaFactor from
      fun w => (hasDerivAt_pairedEtaFactor w).differentiableAt).analyticAt s
  have he := analyticOnNhd_pairedEtaCore s hs
  have hd : AnalyticAt ℂ pairedEtaArithmeticDerivativeValue s := by
    apply he.deriv.congr
    filter_upwards [(Complex.isOpen_re_gt 0).mem_nhds hs] with w hw
    exact (hasDerivAt_pairedEtaCore_arithmeticDerivativeValue hw).deriv
  exact (hF.mul hd).add (((analyticAt_const.add
    (analyticAt_suzukiChebyshevMellinCompletedCorrection hs h1)).mul hF).sub hF.deriv |>.mul he)

/-- The existing safe-half-plane estimate gives a genuine norm floor
for the full arithmetic denominator without a lower bound for xi. -/
theorem norm_pairedEtaCore_le_norm_suzukiEtaCarrierDenominator {s : ℂ}
    (hs : s ∈ pairedEtaCompletionDomain) (hre : 1 ≤ s.re) :
    ‖pairedEtaCore s‖ ≤ ‖suzukiEtaCarrierDenominator s‖ := by
  let z : ℂ := I * (s - 1 / 2)
  have hz : 1 / 2 ≤ z.im := by simp [z]; linarith
  have harg : suzukiArithmeticZetaArgument z = s := by
    unfold suzukiArithmeticZetaArgument z
    simp only [mul_sub, ← mul_assoc, I_mul_I]
    ring
  have hdomain : suzukiArithmeticZetaArgument z ∈ pairedEtaCompletionDomain := by rwa [harg]
  have hE := suzukiXiEValue_ne_zero_of_half_le_im hz
  have hD : suzukiEtaCarrierDenominator s ≠ 0 := by
    simpa only [harg] using (suzukiEtaCarrierDenominator_ne_zero_iff_on_completionDomain hdomain).mpr hE
  have h := norm_suzukiXiZeroCarrier_le_one_of_half_le_im hz
  rw [suzukiXiZeroCarrier_eq_etaCarrier_on_completionDomain hdomain hE, harg,
    suzukiEtaCarrier, norm_div, norm_mul, norm_I, one_mul] at h
  exact (div_le_one (norm_pos_iff.mpr hD)).mp h

/-- A fixed positive floor for the cleared denominator on the safe
line, available at every positive ordinate without a phase restriction. -/
theorem safe_floor_le_norm_suzukiEtaClearedCarrierDenominator {T : ℝ} (hT : 0 < T) :
    staticContourSafeEtaFactorFloor ^ 2 / staticContourSafeZetaDirichletMass ≤
      ‖suzukiEtaClearedCarrierDenominator (staticContourSafeEndpoint T)‖ := by
  let s := staticContourSafeEndpoint T
  have hFbound : staticContourSafeEtaFactorFloor ≤ ‖pairedEtaFactor s‖ := staticContourSafeEtaFactorFloor_le T
  have hF : pairedEtaFactor s ≠ 0 := norm_pos_iff.mp
    (staticContourSafeEtaFactorFloor_pos.trans_le hFbound)
  have hs : s ∈ pairedEtaCompletionDomain := ⟨by simp [s, staticContourSafeEndpoint], by
    intro he
    have := congrArg Complex.re he
    norm_num [s, staticContourSafeEndpoint] at this, hF⟩
  have heta : staticContourSafeEtaFactorFloor / staticContourSafeZetaDirichletMass ≤ ‖pairedEtaCore s‖ := by
    simpa only [staticContourLocalEta, add_zero] using
      staticContourSafeEtaFactorFloor_div_mass_le_norm_localEta_zero hT
  have hD := norm_pairedEtaCore_le_norm_suzukiEtaCarrierDenominator hs (by norm_num [s, staticContourSafeEndpoint])
  rw [suzukiEtaClearedCarrierDenominator_eq_factor_mul hF, norm_mul]
  calc
    _ = staticContourSafeEtaFactorFloor *
        (staticContourSafeEtaFactorFloor / staticContourSafeZetaDirichletMass) := by ring
    _ ≤ _ := mul_le_mul hFbound (heta.trans hD)
      (by positivity [staticContourSafeEtaFactorFloor_pos, one_le_staticContourSafeZetaDirichletMass])
      (norm_nonneg _)

end
end RiemannGaussian
