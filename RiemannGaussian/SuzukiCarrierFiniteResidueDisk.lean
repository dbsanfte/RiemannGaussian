/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ComplexInverseDisk
import RiemannGaussian.SuzukiCarrierFiniteSlopeBound

/-!
# Signed finite enclosures of full weighted carrier residues

The signed tail derivative estimate puts the actual slope in a finite
complex disk. Inverting that disk gives a quantitative enclosure for the
full weighted residue. Its center retains every complex weight, mixed
term, and reflected phase. The real-part bound can therefore retain
cancellation between different poles instead of replacing each residue
by a nonnegative size estimate.

At every actual simple upper pole the centers converge to the exact
weighted residue and their radii tend to zero. This does not establish
a uniform estimate across the full carrier divisor, handle higher-order
poles by a simple-pole formula, or bound the joint pole/strip correction.
-/

open Complex Filter Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

/-- The finite center of the full reflected weighted carrier residue.
The input window is fixed; its derivative is a literal finite inverse-square sum. -/
def suzukiXiFinitePoleResidueCenter (S : Finset NontrivialZetaZero)
    (w : NontrivialZetaZero → ℂ) (T : ℝ) (c : ℂ) : ℂ :=
  let a := deriv (riemannXiSpectralWindowCauchySum T) c
  let e := 4 * ((riemannXiSpectralWindowCauchySum T c).im - 1) / c.im
  let b := starRingEnd ℂ (suzukiXiFiniteCauchyTest S w (starRingEnd ℂ c)) *
    suzukiXiFiniteCauchyTest S w c
  b * starRingEnd ℂ a / ((normSq a - e ^ 2 : ℝ) : ℂ)

/-- The radius corresponding to the full weighted residue center.
Nonnegativity and denominator nonvanishing follow at actual upper poles
from a positive finite slope margin. -/
def suzukiXiFinitePoleResidueRadius (S : Finset NontrivialZetaZero)
    (w : NontrivialZetaZero → ℂ) (T : ℝ) (c : ℂ) : ℝ :=
  let a := deriv (riemannXiSpectralWindowCauchySum T) c
  let e := 4 * ((riemannXiSpectralWindowCauchySum T c).im - 1) / c.im
  let b := starRingEnd ℂ (suzukiXiFiniteCauchyTest S w (starRingEnd ℂ c)) *
    suzukiXiFiniteCauchyTest S w c
  ‖b‖ * e / (normSq a - e ^ 2)

/-- A positive finite margin proves an enclosure of the complete weighted
residue. The finite center retains its complex phase and all cross terms. -/
theorem norm_suzukiXiPole_quadratic_residue_sub_finite_center_le
    (S : Finset NontrivialZetaZero) (w : NontrivialZetaZero → ℂ) {c : ℂ}
    (hc : 0 < c.im) (hE : suzukiXiEValue c = 0) (hxi : riemannXiSpectral c ≠ 0)
    {T : ℝ} (hT : |c.re| + 1 ≤ T) (hmargin : 0 < suzukiXiFinitePoleSlopeMargin T c) :
    ‖(∑ rho ∈ S, ∑ sigma ∈ S,
      starRingEnd ℂ (w rho) * w sigma * suzukiXiMixedCarrierPoleResidue rho sigma c) -
        suzukiXiFinitePoleResidueCenter S w T c‖ ≤ suzukiXiFinitePoleResidueRadius S w T c := by
  have hb := norm_suzukiXiPole_logDeriv_slope_sub_window_le hc hE hxi hT
  have he := (norm_nonneg _).trans hb
  have ha := sub_pos.mp hmargin
  have hm := analyticOrderNatAt_suzukiXiEValue_eq_one_of_finite_margin hc hE hxi hT hmargin
  rw [suzukiXiMixedCarrierPoleResidue_quadratic_eq_reflected_test S w hE hxi hm]
  exact norm_div_sub_inverse_disk_center_le _ he ha hb

/-- The real weighted residue is enclosed around its signed finite
center; the numerator phase is not replaced by its norm. -/
theorem abs_re_suzukiXiPole_quadratic_residue_sub_finite_center_le
    (S : Finset NontrivialZetaZero) (w : NontrivialZetaZero → ℂ) {c : ℂ}
    (hc : 0 < c.im) (hE : suzukiXiEValue c = 0) (hxi : riemannXiSpectral c ≠ 0)
    {T : ℝ} (hT : |c.re| + 1 ≤ T) (hmargin : 0 < suzukiXiFinitePoleSlopeMargin T c) :
    |(∑ rho ∈ S, ∑ sigma ∈ S,
      starRingEnd ℂ (w rho) * w sigma * suzukiXiMixedCarrierPoleResidue rho sigma c).re -
        (suzukiXiFinitePoleResidueCenter S w T c).re| ≤ suzukiXiFinitePoleResidueRadius S w T c := by
  exact (Complex.abs_re_le_norm _).trans
    (norm_suzukiXiPole_quadratic_residue_sub_finite_center_le S w hc hE hxi hT hmargin)

private lemma slope_error_tendsto_zero {c : ℂ}
    (hE : suzukiXiEValue c = 0) (hxi : riemannXiSpectral c ≠ 0) :
    Tendsto (fun T => 4 * ((riemannXiSpectralWindowCauchySum T c).im - 1) / c.im)
      atTop (𝓝 0) := by
  have h := ((Complex.continuous_im.continuousAt.tendsto.comp
    (tendsto_riemannXiSpectralWindowCauchySum hxi)).sub_const 1).const_mul 4
  simpa only [Function.comp_def, logDeriv_riemannXiSpectral_eq_I_at_carrier_pole hE hxi,
    I_im, sub_self, mul_zero, zero_div] using h.div_const c.im

/-- At every genuine simple upper pole the entire disk radius tends to
zero for every finite complex test. No uniformity over different poles
is assumed or concluded. -/
theorem tendsto_suzukiXiFinitePoleResidueRadius_zero
    (S : Finset NontrivialZetaZero) (w : NontrivialZetaZero → ℂ) {c : ℂ}
    (hc : 0 < c.im) (hE : suzukiXiEValue c = 0) (hxi : riemannXiSpectral c ≠ 0)
    (hm : analyticOrderNatAt suzukiXiEValue c = 1) :
    Tendsto (fun T => suzukiXiFinitePoleResidueRadius S w T c) atTop (𝓝 0) := by
  have hc1 : c.im < 1 / 2 := by
    by_contra! h
    exact suzukiXiEValue_ne_zero_of_half_le_im h hE
  have hs := tendsto_deriv_riemannXiSpectralWindowCauchySum hc hc1 hxi
  have he := slope_error_tendsto_zero hE hxi
  have hq := deriv_logDeriv_riemannXiSpectral_ne_zero_at_simple_carrier_pole hE hxi hm
  have hd := ((Complex.continuous_normSq.tendsto _).comp hs).sub (he.pow 2)
  have hn := he.const_mul
    ‖starRingEnd ℂ (suzukiXiFiniteCauchyTest S w (starRingEnd ℂ c)) * suzukiXiFiniteCauchyTest S w c‖
  have hd0 : normSq (deriv (logDeriv riemannXiSpectral) c) - (0 : ℝ) ^ 2 ≠ 0 := by
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using (normSq_pos.mpr hq).ne'
  simpa only [suzukiXiFinitePoleResidueRadius, Function.comp_def, div_eq_mul_inv,
    mul_zero, zero_mul] using hn.mul (hd.inv₀ hd0)

/-- Every actual simple upper pole's finite complex centers converge to
the exact full weighted residue. This follows from the proved enclosure,
the vanishing signed tail, and eventual positivity of the finite margin. -/
theorem tendsto_suzukiXiFinitePoleResidueCenter
    (S : Finset NontrivialZetaZero) (w : NontrivialZetaZero → ℂ) {c : ℂ}
    (hc : 0 < c.im) (hE : suzukiXiEValue c = 0) (hxi : riemannXiSpectral c ≠ 0)
    (hm : analyticOrderNatAt suzukiXiEValue c = 1) :
    Tendsto (fun T => suzukiXiFinitePoleResidueCenter S w T c) atTop
      (𝓝 (∑ rho ∈ S, ∑ sigma ∈ S,
        starRingEnd ℂ (w rho) * w sigma * suzukiXiMixedCarrierPoleResidue rho sigma c)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (tendsto_suzukiXiFinitePoleResidueRadius_zero S w hc hE hxi hm)
  filter_upwards [eventually_suzukiXiFinitePoleSlopeMargin_pos_at_simple_pole hc hE hxi hm]
    with T hT
  rw [norm_sub_rev]
  exact norm_suzukiXiPole_quadratic_residue_sub_finite_center_le S w hc hE hxi hT.1 hT.2

/-- The complete mixed matrix of a finite set of actual poles lies in
one signed complex enclosure. Pole centers and every mixed term are
summed before taking the norm; only the error radii are added. -/
theorem norm_suzukiXiPole_matrix_sub_finite_centers_le
    (C : Finset ℂ) (S : Finset NontrivialZetaZero) (w : NontrivialZetaZero → ℂ)
    (hpoles : ∀ c ∈ C, 0 < c.im ∧ suzukiXiEValue c = 0 ∧ riemannXiSpectral c ≠ 0)
    {T : ℝ} (hT : ∀ c ∈ C, |c.re| + 1 ≤ T ∧ 0 < suzukiXiFinitePoleSlopeMargin T c) :
    ‖(∑ rho ∈ S, ∑ sigma ∈ S, starRingEnd ℂ (w rho) * w sigma *
        ∑ c ∈ C, suzukiXiMixedCarrierPoleResidue rho sigma c) -
      ∑ c ∈ C, suzukiXiFinitePoleResidueCenter S w T c‖ ≤
        ∑ c ∈ C, suzukiXiFinitePoleResidueRadius S w T c := by
  have hswap : (∑ rho ∈ S, ∑ sigma ∈ S, starRingEnd ℂ (w rho) * w sigma *
      ∑ c ∈ C, suzukiXiMixedCarrierPoleResidue rho sigma c) =
        ∑ c ∈ C, ∑ rho ∈ S, ∑ sigma ∈ S,
          starRingEnd ℂ (w rho) * w sigma * suzukiXiMixedCarrierPoleResidue rho sigma c := by
    simp_rw [Finset.mul_sum]
    calc
      _ = ∑ rho ∈ S, ∑ c ∈ C, ∑ sigma ∈ S,
          starRingEnd ℂ (w rho) * w sigma * suzukiXiMixedCarrierPoleResidue rho sigma c := by
        apply Finset.sum_congr rfl
        intro rho _hrho
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hswap, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro c hc
  exact norm_suzukiXiPole_quadratic_residue_sub_finite_center_le S w
    (hpoles c hc).1 (hpoles c hc).2.1 (hpoles c hc).2.2 (hT c hc).1 (hT c hc).2

/-- A signed upper bound for the full finite residue matrix. The real
parts of the complex centers can cancel across poles and across weights;
only the proved approximation errors enter as positive allowances. -/
theorem re_suzukiXiPole_matrix_le_finite_centers
    (C : Finset ℂ) (S : Finset NontrivialZetaZero) (w : NontrivialZetaZero → ℂ)
    (hpoles : ∀ c ∈ C, 0 < c.im ∧ suzukiXiEValue c = 0 ∧ riemannXiSpectral c ≠ 0)
    {T : ℝ} (hT : ∀ c ∈ C, |c.re| + 1 ≤ T ∧ 0 < suzukiXiFinitePoleSlopeMargin T c) :
    (∑ rho ∈ S, ∑ sigma ∈ S, starRingEnd ℂ (w rho) * w sigma *
        ∑ c ∈ C, suzukiXiMixedCarrierPoleResidue rho sigma c).re ≤
      (∑ c ∈ C, suzukiXiFinitePoleResidueCenter S w T c).re +
        ∑ c ∈ C, suzukiXiFinitePoleResidueRadius S w T c := by
  have h := (Complex.re_le_norm _).trans
    (norm_suzukiXiPole_matrix_sub_finite_centers_le C S w hpoles hT)
  simp only [sub_re] at h
  linarith

/-- For any fixed finite set of actual simple upper poles, one growing
window eventually encloses their full mixed matrix for ALL finite complex
weight families simultaneously. The window choice is independent of the weights. -/
theorem eventually_suzukiXiPole_matrix_enclosure_all_weights
    (C : Finset ℂ)
    (hpoles : ∀ c ∈ C, 0 < c.im ∧ suzukiXiEValue c = 0 ∧ riemannXiSpectral c ≠ 0)
    (hsimple : ∀ c ∈ C, analyticOrderNatAt suzukiXiEValue c = 1) :
    ∀ᶠ T in atTop, ∀ (S : Finset NontrivialZetaZero) (w : NontrivialZetaZero → ℂ),
      ‖(∑ rho ∈ S, ∑ sigma ∈ S, starRingEnd ℂ (w rho) * w sigma *
          ∑ c ∈ C, suzukiXiMixedCarrierPoleResidue rho sigma c) -
        ∑ c ∈ C, suzukiXiFinitePoleResidueCenter S w T c‖ ≤
          ∑ c ∈ C, suzukiXiFinitePoleResidueRadius S w T c := by
  have h : ∀ᶠ T in atTop, ∀ c ∈ C,
      |c.re| + 1 ≤ T ∧ 0 < suzukiXiFinitePoleSlopeMargin T c := by
    rw [eventually_all_finset]
    intro c hc
    exact eventually_suzukiXiFinitePoleSlopeMargin_pos_at_simple_pole
      (hpoles c hc).1 (hpoles c hc).2.1 (hpoles c hc).2.2 (hsimple c hc)
  filter_upwards [h] with T hT
  exact fun S w => norm_suzukiXiPole_matrix_sub_finite_centers_le C S w hpoles hT

/-- The total radius tends to zero for every fixed finite simple pole
set and finite weight family. This is a finite-set limit, not an estimate
uniform over expanding contour pole windows. -/
theorem tendsto_sum_suzukiXiFinitePoleResidueRadius_zero
    (C : Finset ℂ) (S : Finset NontrivialZetaZero) (w : NontrivialZetaZero → ℂ)
    (hpoles : ∀ c ∈ C, 0 < c.im ∧ suzukiXiEValue c = 0 ∧ riemannXiSpectral c ≠ 0)
    (hsimple : ∀ c ∈ C, analyticOrderNatAt suzukiXiEValue c = 1) :
    Tendsto (fun T => ∑ c ∈ C, suzukiXiFinitePoleResidueRadius S w T c) atTop (𝓝 0) := by
  have h := tendsto_finsetSum C (fun c hc =>
    tendsto_suzukiXiFinitePoleResidueRadius_zero S w
      (hpoles c hc).1 (hpoles c hc).2.1 (hpoles c hc).2.2 (hsimple c hc))
  simpa only [Finset.sum_const_zero] using h

end
end RiemannGaussian
