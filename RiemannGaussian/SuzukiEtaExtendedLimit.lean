/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaExtendedCarrier
import RiemannGaussian.SuzukiEtaCarrierLimit

/-!
# Arithmetic carrier limits across the spectral strip boundary

Finite paired eta carriers approximate the literal carrier on compact
paths throughout the full completion domain. Actual and eventual finite
denominator nonvanishing, continuity, and weighted integral convergence
are proved. The upper spectral strip boundary is included away from the
explicit completion exceptions, and interior pole orders are unrestricted.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

/-- The full positive-half-plane completion domain in spectral coordinates,
with the genuine carrier denominator removed only on the observation set. -/
def suzukiXiEtaExtendedCarrierDomain : Set ℂ :=
  {z | suzukiArithmeticZetaArgument z ∈ pairedEtaCompletionDomain ∧ suzukiXiEValue z ≠ 0}

private lemma continuous_argument : Continuous suzukiArithmeticZetaArgument := by
  unfold suzukiArithmeticZetaArgument
  fun_prop

/-- The finite arithmetic carriers converge locally uniformly to the
literal original carrier on its actual nonzero-denominator domain. -/
theorem tendstoLocallyUniformlyOn_suzukiXiEtaFiniteCarrier_on_completionDomain :
    TendstoLocallyUniformlyOn suzukiXiEtaFiniteCarrier suzukiXiZeroCarrier
      atTop suzukiXiEtaExtendedCarrierDomain := by
  have hmap : MapsTo suzukiArithmeticZetaArgument suzukiXiEtaExtendedCarrierDomain suzukiEtaExtendedCarrierDomain := by
    intro z hz
    exact ⟨hz.1, (suzukiEtaCarrierDenominator_ne_zero_iff_on_completionDomain hz.1).mpr hz.2⟩
  have h := tendstoLocallyUniformlyOn_suzukiEtaFiniteCarrier_on_completionDomain.comp
    suzukiArithmeticZetaArgument hmap continuous_argument.continuousOn
  apply h.congr_right
  intro z hz
  exact (suzukiXiZeroCarrier_eq_etaCarrier_on_completionDomain hz.1 hz.2).symm

/-- On any fixed compact observation set, the finite arithmetic
denominators eventually avoid zero simultaneously. Interior poles are
not constrained by this boundary statement. -/
theorem eventually_suzukiXiEtaFiniteDenominator_ne_zero_on_compact_on_completionDomain
    {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ suzukiXiEtaExtendedCarrierDomain) :
    ∀ᶠ N in atTop, ∀ z ∈ K,
      suzukiEtaFiniteCarrierDenominator N (suzukiArithmeticZetaArgument z) ≠ 0 := by
  have hmap : MapsTo suzukiArithmeticZetaArgument K pairedEtaCompletionDomain := fun _ hz => (hKD hz).1
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (tendstoLocallyUniformlyOn_suzukiEtaFiniteCarrierDenominator_on_completionDomain.comp
      suzukiArithmeticZetaArgument hmap continuous_argument.continuousOn)
  have hc : ContinuousOn (fun z => ‖suzukiEtaCarrierDenominator (suzukiArithmeticZetaArgument z)‖) K := by
    intro z hz
    exact ((analyticAt_suzukiEtaCarrierDenominator_on_completionDomain (hmap hz)).continuousAt.comp
      continuous_argument.continuousAt).norm.continuousWithinAt
  have hp : ∀ z ∈ K, 0 < ‖suzukiEtaCarrierDenominator (suzukiArithmeticZetaArgument z)‖ := by
    intro z hz
    exact norm_pos_iff.mpr ((suzukiEtaCarrierDenominator_ne_zero_iff_on_completionDomain (hKD hz).1).mpr (hKD hz).2)
  obtain ⟨delta, hd, hdelta⟩ := hK.exists_forall_le' hc hp
  rw [Metric.tendstoUniformlyOn_iff] at hu
  filter_upwards [hu delta hd] with N hN
  intro z hz hzero
  have hn := hN z hz
  simp only [Function.comp_def, hzero, dist_zero_right] at hn
  exact (not_lt_of_ge (hdelta z hz)) hn

/-- The finite carriers are eventually continuous on every compact
observation set, with denominator nonvanishing supplied by convergence. -/
theorem eventually_continuousOn_suzukiXiEtaFiniteCarrier_on_completionDomain
    {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ suzukiXiEtaExtendedCarrierDomain) :
    ∀ᶠ N in atTop, ContinuousOn (suzukiXiEtaFiniteCarrier N) K := by
  filter_upwards [eventually_suzukiXiEtaFiniteDenominator_ne_zero_on_compact_on_completionDomain hK hKD] with N hN
  intro z hz
  have hnum : AnalyticAt ℂ (fun s => I * pairedEtaCorePartialSum N s)
      (suzukiArithmeticZetaArgument z) := analyticAt_const.mul
    ((differentiable_pairedEtaCorePartialSum N).analyticAt (suzukiArithmeticZetaArgument z))
  have hden := analyticAt_suzukiEtaFiniteCarrierDenominator_on_completionDomain N (hKD hz).1
  exact ((hnum.div hden (hN z hz)).continuousAt.comp
    continuous_argument.continuousAt).continuousWithinAt

/-- Every fixed continuous complex weight and compact path in the true
domain has convergent arithmetic carrier integrals. The original path
and all phases are retained, without any pole simplicity premise. -/
theorem tendsto_intervalIntegral_suzukiXiEtaFiniteCarrier_on_completionDomain
    {a b : ℝ} (gamma : ℝ → ℂ) (w : ℝ → ℂ)
    (hgamma : ContinuousOn gamma (uIcc a b)) (hw : ContinuousOn w (uIcc a b))
    (hgeom : ∀ t ∈ uIcc a b, gamma t ∈ suzukiXiEtaExtendedCarrierDomain) :
    Tendsto (fun N => ∫ t : ℝ in a..b, w t * suzukiXiEtaFiniteCarrier N (gamma t)) atTop
      (𝓝 (∫ t : ℝ in a..b, w t * suzukiXiZeroCarrier (gamma t))) := by
  let K := gamma '' uIcc a b
  have hK : IsCompact K := isCompact_uIcc.image_of_continuousOn hgamma
  have hKD : K ⊆ suzukiXiEtaExtendedCarrierDomain := by
    rintro z ⟨t, ht, rfl⟩
    exact hgeom t ht
  have hgK : MapsTo gamma (uIcc a b) K := fun t ht => mem_image_of_mem gamma ht
  have hlim := tendstoLocallyUniformlyOn_suzukiXiEtaFiniteCarrier_on_completionDomain.comp gamma hgeom hgamma
  have hcont : ContinuousOn (fun t => suzukiXiZeroCarrier (gamma t)) (uIcc a b) := by
    intro t ht
    exact (analyticAt_suzukiXiZeroCarrier_of_E_ne_zero (hgeom t ht).2).continuousAt.comp_continuousWithinAt
      (hgamma t ht)
  have hweighted := (tendstoLocallyUniformlyOn_const_index w).fun_mul₀ hlim hw hcont
  have huniform := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_uIcc).mp hweighted
  apply huniform.tendsto_intervalIntegral_of_continuousOn
  filter_upwards [eventually_continuousOn_suzukiXiEtaFiniteCarrier_on_completionDomain hK hKD] with N hN
  exact hw.mul (hN.comp hgamma hgK)


end
end RiemannGaussian
