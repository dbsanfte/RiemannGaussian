/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RiemannXiSignedTailDerivative
import RiemannGaussian.SuzukiCarrierPoleQuadratic

/-!
# Finite signed slope bounds for actual carrier residues

At a genuine upper pole the complete logarithmic derivative equals `i`.
Its finite head's excess imaginary part therefore bounds the entire
omitted derivative. A positive finite margin proves simplicity and bounds
the full reflected bilinear residue of any finite complex test. Every
actual simple pole eventually has such a positive finite margin.

No margin is assumed globally, and multiple poles remain covered by the
existing arbitrary-order residue formulas. These local estimates do not
establish the independent joint source ceiling required by the RH goal.
-/

open Complex Filter Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

private lemma pole_im_lt_half {c : ℂ} (hE : suzukiXiEValue c = 0) : c.im < 1 / 2 := by
  by_contra! h
  exact suzukiXiEValue_ne_zero_of_half_le_im h hE

/-- At a genuine upper carrier pole the full complex slope error has an
explicit finite signed bound; its numerator is the head's excess over one. -/
theorem norm_suzukiXiPole_logDeriv_slope_sub_window_le {c : ℂ}
    (hc : 0 < c.im) (hE : suzukiXiEValue c = 0) (hxi : riemannXiSpectral c ≠ 0)
    {T : ℝ} (hT : |c.re| + 1 ≤ T) :
    ‖deriv (logDeriv riemannXiSpectral) c - deriv (riemannXiSpectralWindowCauchySum T) c‖ ≤
      4 * ((riemannXiSpectralWindowCauchySum T c).im - 1) / c.im := by
  have h := norm_deriv_logDeriv_riemannXiSpectral_sub_window_le hc (pole_im_lt_half hE) hxi hT
  simpa only [logDeriv_riemannXiSpectral_eq_I_at_carrier_pole hE hxi, I_im] using h

/-- The finite Cauchy-head slope minus the full signed tail allowance.
Both terms use the same genuine fixed zero window and observation point. -/
def suzukiXiFinitePoleSlopeMargin (T : ℝ) (c : ℂ) : ℝ :=
  ‖deriv (riemannXiSpectralWindowCauchySum T) c‖ -
    4 * ((riemannXiSpectralWindowCauchySum T c).im - 1) / c.im

/-- The finite margin is an independent lower bound for the actual
logarithmic-derivative slope norm at every genuine upper carrier pole. -/
theorem suzukiXiFinitePoleSlopeMargin_le_norm {c : ℂ}
    (hc : 0 < c.im) (hE : suzukiXiEValue c = 0) (hxi : riemannXiSpectral c ≠ 0)
    {T : ℝ} (hT : |c.re| + 1 ≤ T) :
    suzukiXiFinitePoleSlopeMargin T c ≤ ‖deriv (logDeriv riemannXiSpectral) c‖ := by
  have hb := norm_suzukiXiPole_logDeriv_slope_sub_window_le hc hE hxi hT
  have hn : ‖deriv (riemannXiSpectralWindowCauchySum T) c‖ ≤
      ‖deriv (logDeriv riemannXiSpectral) c‖ +
        ‖deriv (logDeriv riemannXiSpectral) c - deriv (riemannXiSpectralWindowCauchySum T) c‖ := by
    calc
      _ = ‖deriv (logDeriv riemannXiSpectral) c +
          (deriv (riemannXiSpectralWindowCauchySum T) c - deriv (logDeriv riemannXiSpectral) c)‖ := by
        congr 1
        ring
      _ ≤ _ := by
        simpa only [norm_sub_rev] using norm_add_le
          (deriv (logDeriv riemannXiSpectral) c)
          (deriv (riemannXiSpectralWindowCauchySum T) c - deriv (logDeriv riemannXiSpectral) c)
  unfold suzukiXiFinitePoleSlopeMargin
  linarith

/-- A positive finite signed margin proves that the actual carrier pole
is simple. Simplicity is concluded from the bound and is not assumed. -/
theorem analyticOrderNatAt_suzukiXiEValue_eq_one_of_finite_margin {c : ℂ}
    (hc : 0 < c.im) (hE : suzukiXiEValue c = 0) (hxi : riemannXiSpectral c ≠ 0)
    {T : ℝ} (hT : |c.re| + 1 ≤ T) (hmargin : 0 < suzukiXiFinitePoleSlopeMargin T c) :
    analyticOrderNatAt suzukiXiEValue c = 1 := by
  have hq : deriv (logDeriv riemannXiSpectral) c ≠ 0 :=
    norm_pos_iff.mp (hmargin.trans_le (suzukiXiFinitePoleSlopeMargin_le_norm hc hE hxi hT))
  have hd : deriv suzukiXiEValue c ≠ 0 := by
    rw [deriv_suzukiXiEValue_at_pole hE hxi]
    exact mul_ne_zero (mul_ne_zero I_ne_zero hxi) hq
  have ho := (analyticAt_suzukiXiEValue c).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hE hd
  simp only [analyticOrderNatAt, ho, ENat.toNat_one]

/-- Every finite complex test has a quantitative residue bound from a
positive finite margin. Both reflected test values and all mixed terms
are combined before taking norms. No pointwise norm-square substitution
is made at the nonreal carrier pole. -/
theorem norm_suzukiXiPole_quadratic_residue_le_of_finite_margin
    (S : Finset NontrivialZetaZero) (w : NontrivialZetaZero → ℂ) {c : ℂ}
    (hc : 0 < c.im) (hE : suzukiXiEValue c = 0) (hxi : riemannXiSpectral c ≠ 0)
    {T : ℝ} (hT : |c.re| + 1 ≤ T) (hmargin : 0 < suzukiXiFinitePoleSlopeMargin T c) :
    ‖∑ rho ∈ S, ∑ sigma ∈ S,
      starRingEnd ℂ (w rho) * w sigma * suzukiXiMixedCarrierPoleResidue rho sigma c‖ ≤
        ‖suzukiXiFiniteCauchyTest S w (starRingEnd ℂ c)‖ * ‖suzukiXiFiniteCauchyTest S w c‖ /
          suzukiXiFinitePoleSlopeMargin T c := by
  have hm := analyticOrderNatAt_suzukiXiEValue_eq_one_of_finite_margin hc hE hxi hT hmargin
  rw [suzukiXiMixedCarrierPoleResidue_quadratic_eq_reflected_test S w hE hxi hm,
    norm_div, norm_mul, norm_conj]
  exact div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hmargin
    (suzukiXiFinitePoleSlopeMargin_le_norm hc hE hxi hT)

/-- The finite margins converge to the actual slope norm at every
genuine upper pole. At a multiple pole that limit is zero, so no positive
margin or uniform pole separation is silently imposed. -/
theorem tendsto_suzukiXiFinitePoleSlopeMargin {c : ℂ}
    (hc : 0 < c.im) (hE : suzukiXiEValue c = 0) (hxi : riemannXiSpectral c ≠ 0) :
    Tendsto (fun T => suzukiXiFinitePoleSlopeMargin T c) atTop
      (𝓝 ‖deriv (logDeriv riemannXiSpectral) c‖) := by
  have hhead := (tendsto_deriv_riemannXiSpectralWindowCauchySum hc (pole_im_lt_half hE) hxi).norm
  have hm := ((Complex.continuous_im.continuousAt.tendsto.comp
    (tendsto_riemannXiSpectralWindowCauchySum hxi)).sub_const 1).const_mul 4
  have he : Tendsto (fun T => 4 * ((riemannXiSpectralWindowCauchySum T c).im - 1) / c.im)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, logDeriv_riemannXiSpectral_eq_I_at_carrier_pole hE hxi,
      I_im, sub_self, mul_zero, zero_div] using hm.div_const c.im
  simpa only [suzukiXiFinitePoleSlopeMargin, sub_zero] using hhead.sub he

/-- Every actual simple upper carrier pole eventually admits a positive
finite signed margin. This certifies the local residue bound for every
such pole, without presuming a uniform margin across different poles. -/
theorem eventually_suzukiXiFinitePoleSlopeMargin_pos_at_simple_pole {c : ℂ}
    (hc : 0 < c.im) (hE : suzukiXiEValue c = 0) (hxi : riemannXiSpectral c ≠ 0)
    (hm : analyticOrderNatAt suzukiXiEValue c = 1) :
    ∀ᶠ T in atTop, |c.re| + 1 ≤ T ∧ 0 < suzukiXiFinitePoleSlopeMargin T c := by
  have hp : 0 < ‖deriv (logDeriv riemannXiSpectral) c‖ := norm_pos_iff.mpr
    (deriv_logDeriv_riemannXiSpectral_ne_zero_at_simple_carrier_pole hE hxi hm)
  filter_upwards [eventually_ge_atTop (|c.re| + 1),
    (tendsto_suzukiXiFinitePoleSlopeMargin hc hE hxi).eventually (lt_mem_nhds hp)] with T hT hpos
  exact ⟨hT, hpos⟩

end
end RiemannGaussian
