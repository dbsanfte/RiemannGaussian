/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiGammaReflectionDecay
import RiemannGaussian.SuzukiReflectionLocalIntegrability

/-!
# Global control of the original companion heat term

The actual smoothed carrier retains its linear vanishing at both reflection
nodes. Its norm decreases with smoothing. These facts turn the singular
reflection weight into an integrable inverse-distance majorant against the
original polynomial Gaussian heat source.
-/

open Complex Filter MeasureTheory Set Topology
namespace RiemannGaussian
noncomputable section

/-- Increasing smoothing from one decreases the actual carrier norm,
including at genuine carrier poles and common zeros. -/
theorem norm_suzukiXiSmoothCarrier_le_one {r : ℝ} (hr : 1 ≤ r) (z : ℂ) :
    ‖suzukiXiSmoothCarrier r z‖ ≤ ‖suzukiXiSmoothCarrier 1 z‖ := by
  by_cases hE : suzukiXiEValue z = 0
  · simp [suzukiXiSmoothCarrier_eq_zero_of_E_zero _ hE]
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hp := complexSmoothQuotient_denominator_pos (r := 1) (by norm_num)
    (a := I * riemannXiSpectral z) (Or.inr hE)
  have hpr := complexSmoothQuotient_denominator_pos hr0
    (a := I * riemannXiSpectral z) (Or.inr hE)
  unfold suzukiXiSmoothCarrier complexSmoothQuotient
  rw [norm_div, norm_div, complexSmoothQuotient_denominator,
    complexSmoothQuotient_denominator, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpr, abs_of_pos hp]
  apply div_le_div_of_nonneg_left (norm_nonneg _) hp
  have hn := normSq_nonneg (I * riemannXiSpectral z)
  nlinarith [mul_nonneg (show 0 ≤ r ^ 2 - 1 by nlinarith [sq_nonneg (r - 1)]) hn]

/-- The actual carrier at unit smoothing has a global linear envelope
about each original xi zero. The analytic chart retains its full multiplicity. -/
theorem exists_suzukiXiSmoothCarrier_linear_bound (rho : NontrivialZetaZero) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖suzukiXiSmoothCarrier 1 z‖ ≤ C * ‖z - zetaSpectralCoordinate rho.1‖ := by
  let a := zetaSpectralCoordinate rho.1
  obtain ⟨q, hq, _hq0, he⟩ := exists_suzukiXiSmoothCarrier_zero_chart rho 1
  have hb : ∀ᶠ z in 𝓝 a, ‖q z‖ < ‖q a‖ + 1 :=
    hq.continuousAt.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨d, hd, hlocal⟩ := Metric.eventually_nhds_iff.mp (he.and hb)
  let C := max (‖q a‖ + 1) (1 / d)
  refine ⟨C, le_trans (by positivity : 0 ≤ ‖q a‖ + 1) (le_max_left _ _), ?_⟩
  intro z
  by_cases hz : ‖z - a‖ < d
  · obtain ⟨heq, hqz⟩ := hlocal (by simpa only [dist_eq_norm] using hz)
    have hn := normSq_nonneg ((z - a) * q z)
    rw [heq]
    change ‖complexSmoothQuotient 1 ((z - a) * q z) 1‖ ≤ C * ‖z - a‖
    rw [complexSmoothQuotient_one_right, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show 0 < 1 + 1 ^ 2 * normSq ((z - a) * q z) by nlinarith)]
    calc
      _ ≤ ‖(z - a) * q z‖ := div_le_self (norm_nonneg _) (by nlinarith)
      _ = ‖z - a‖ * ‖q z‖ := norm_mul _ _
      _ ≤ C * ‖z - a‖ := by
        have hqC : ‖q z‖ ≤ C := hqz.le.trans (le_max_left _ _)
        nlinarith [mul_le_mul_of_nonneg_right hqC (norm_nonneg (z - a))]
  · have hm : ‖suzukiXiSmoothCarrier 1 z‖ ≤ 1 :=
      (norm_suzukiXiSmoothCarrier_le (r := 1) (by norm_num) z).trans (by norm_num)
    calc
      _ ≤ 1 := hm
      _ ≤ (1 / d) * ‖z - a‖ := by
        rw [one_div_mul_eq_div]
        exact (le_div_iff₀ hd).mpr (by simpa using le_of_not_gt hz)
      _ ≤ C * ‖z - a‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

/-- Both singular reflection poles are reduced to inverse distances
when the original unit-smoothing carrier is kept with the weight. -/
theorem exists_suzukiXiReflectionCarrier_inverse_distance_bound (rho : NontrivialZetaZero) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖suzukiXiReflectionWeight rho z‖ * ‖suzukiXiSmoothCarrier 1 z‖ ≤
        C * (‖(z - zetaSpectralCoordinate rho.1)⁻¹‖ +
          ‖(z - starRingEnd ℂ (zetaSpectralCoordinate rho.1))⁻¹‖) := by
  obtain ⟨Ca, hCa, ha⟩ := exists_suzukiXiSmoothCarrier_linear_bound rho
  obtain ⟨Cb, hCb, hb⟩ := exists_suzukiXiSmoothCarrier_linear_bound rho.conjugatePartner
  simp only [NontrivialZetaZero.spectralCoordinate_conjugatePartner] at hb
  refine ⟨2 * (Ca + Cb), by positivity, ?_⟩
  intro z
  have hterm (a : ℂ) (C : ℝ)
      (h : ‖suzukiXiSmoothCarrier 1 z‖ ≤ C * ‖z - a‖) :
      ‖(z - a)⁻¹‖ ^ 2 * ‖suzukiXiSmoothCarrier 1 z‖ ≤ C * ‖(z - a)⁻¹‖ := by
    by_cases hz : z - a = 0
    · simp [hz]
    · rw [norm_inv]
      calc
        _ ≤ (‖z - a‖⁻¹) ^ 2 * (C * ‖z - a‖) := mul_le_mul_of_nonneg_left h (by positivity)
        _ = _ := by field_simp
  have hwa := hterm _ _ (ha z)
  have hwb := hterm _ _ (hb z)
  have htriangle := norm_sub_le ((z - zetaSpectralCoordinate rho.1)⁻¹)
    ((z - starRingEnd ℂ (zetaSpectralCoordinate rho.1))⁻¹)
  have hw : ‖suzukiXiReflectionWeight rho z‖ ≤
      2 * (‖(z - zetaSpectralCoordinate rho.1)⁻¹‖ ^ 2 +
        ‖(z - starRingEnd ℂ (zetaSpectralCoordinate rho.1))⁻¹‖ ^ 2) := by
    unfold suzukiXiReflectionWeight suzukiXiReflectionCauchyDifference
    rw [norm_neg, norm_pow]
    have hs := pow_le_pow_left₀ (norm_nonneg _) htriangle 2
    nlinarith [sq_nonneg (‖(z - zetaSpectralCoordinate rho.1)⁻¹‖ -
      ‖(z - starRingEnd ℂ (zetaSpectralCoordinate rho.1))⁻¹‖)]
  have hm := norm_nonneg (suzukiXiSmoothCarrier 1 z)
  nlinarith [mul_le_mul_of_nonneg_right hw hm,
    mul_nonneg hCa (norm_nonneg ((z - starRingEnd ℂ (zetaSpectralCoordinate rho.1))⁻¹)),
    mul_nonneg hCb (norm_nonneg ((z - zetaSpectralCoordinate rho.1)⁻¹))]

private lemma integrable_re_im_product {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun z : ℂ => f z.re * g z.im) := by
  have hp := hf.mul_prod hg
  exact Complex.volume_preserving_equiv_real_prod.integrable_comp hp.aestronglyMeasurable |>.mpr hp

/-- The actual companion heat source is integrable on the full plane
for every positive Gaussian time, with all polynomial terms retained. -/
theorem integrable_suzukiSpectralCompanionHeat {tau : ℝ} (htau : 0 < tau) (c : ℝ) :
    Integrable (fun z : ℂ => suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau (I * z)) := by
  have h0 := integrable_exp_neg_mul_sq htau
  have h1 := integrable_mul_exp_neg_mul_sq htau
  have h2 : Integrable (fun y : ℝ => y ^ 2 * Real.exp (-tau * y ^ 2)) := by
    simpa only [Real.rpow_two] using integrable_rpow_mul_exp_neg_mul_sq htau (s := 2) (by norm_num)
  have ha := (integrable_re_im_product (h1.comp_sub_right c) h1).ofReal (𝕜 := ℂ)
  have hb := (integrable_re_im_product (h0.comp_sub_right c) h2).ofReal (𝕜 := ℂ)
  have hc := (integrable_re_im_product (h0.comp_sub_right c) h0).ofReal (𝕜 := ℂ)
  have hi := ((ha.const_mul (4 * (tau : ℂ))).add (hb.const_mul (4 * (tau : ℂ) * I))).add
    (hc.const_mul (-2 * I))
  convert! hi using 1
  funext z
  change suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau (I * z) =
    (4 * (tau : ℂ) * (((z.re - c) * Real.exp (-tau * (z.re - c) ^ 2) *
      (z.im * Real.exp (-tau * z.im ^ 2)) : ℝ) : ℂ) +
      4 * (tau : ℂ) * I * ((Real.exp (-tau * (z.re - c) ^ 2) *
        (z.im ^ 2 * Real.exp (-tau * z.im ^ 2)) : ℝ) : ℂ)) +
      (-2 * I) * ((Real.exp (-tau * (z.re - c) ^ 2) * Real.exp (-tau * z.im ^ 2) : ℝ) : ℂ)
  simp only [suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource, I_mul_re, I_mul_im]
  rw [show -tau * ((c - z.re) ^ 2 + (-z.im) ^ 2) =
    -tau * (z.re - c) ^ 2 + -tau * z.im ^ 2 by ring, Real.exp_add]
  simp only [ofReal_mul, ofReal_sub, ofReal_pow, ofReal_neg]
  ring

/-- A continuous integrable function times an inverse-distance kernel
is integrable in the complex plane. Local boundedness controls the node;
outside its unit disk the inverse distance is bounded by one. -/
theorem integrable_norm_mul_inverse_distance {f : ℂ → ℂ}
    (hf : Continuous f) (hi : Integrable f) (a : ℂ) :
    Integrable (fun z => ‖f z‖ * ‖(z - a)⁻¹‖) := by
  let K := Metric.closedBall a 1
  have hK : IsCompact K := isCompact_closedBall _ _
  have hinv := ((locallyIntegrable_complex_inv_sub a).integrableOn_isCompact hK).norm
  have hinside : IntegrableOn (fun z => ‖f z‖ * ‖(z - a)⁻¹‖) K :=
    IntegrableOn.continuousOn_mul hf.norm.continuousOn hinv hK
  have hm : AEStronglyMeasurable (fun z => ‖f z‖ * ‖(z - a)⁻¹‖) := by
    apply Measurable.aestronglyMeasurable
    exact hf.norm.measurable.mul (by fun_prop)
  have houtside : IntegrableOn (fun z => ‖f z‖ * ‖(z - a)⁻¹‖) Kᶜ := by
    apply hi.norm.integrableOn.mono' (hm.mono_measure Measure.restrict_le_self)
    filter_upwards [ae_restrict_mem hK.isClosed.measurableSet.compl] with z hz
    have hd : 1 ≤ ‖z - a‖ := by
      have hh : 1 < ‖z - a‖ := by
        simpa only [K, mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, not_le] using hz
      exact hh.le
    have hinv1 : ‖(z - a)⁻¹‖ ≤ 1 := by
      rw [norm_inv, ← one_div]
      exact (one_div_le_one_div_of_le zero_lt_one hd).trans_eq (by norm_num)
    simp only [Real.norm_eq_abs, abs_mul, abs_norm]
    exact mul_le_of_le_one_right (norm_nonneg _) hinv1
  rw [← integrableOn_univ, ← union_compl_self K]
  exact hinside.union houtside

/-- The original companion heat contribution, retaining the actual
reflection phase and smooth carrier before any norm is applied. -/
def suzukiXiReflectionCompanionHeat (rho : NontrivialZetaZero) (r c tau : ℝ) (z : ℂ) : ℂ :=
  -I * suzukiXiReflectionWeight rho z * suzukiXiSmoothCarrier r z *
    suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau (I * z)

private lemma companion_measurable (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r)
    (c tau : ℝ) : AEStronglyMeasurable (suzukiXiReflectionCompanionHeat rho r c tau) := by
  have hW : Measurable (suzukiXiReflectionWeight rho) := by
    unfold suzukiXiReflectionWeight suzukiXiReflectionCauchyDifference
    fun_prop
  have hS := (contDiff_suzukiXiSmoothCarrier hr).continuous.measurable
  have hH := (continuous_suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau).measurable
  apply Measurable.aestronglyMeasurable
  unfold suzukiXiReflectionCompanionHeat
  fun_prop

private lemma companion_domination (rho : NontrivialZetaZero) {C : ℝ}
    (hC : ∀ z : ℂ, ‖suzukiXiReflectionWeight rho z‖ * ‖suzukiXiSmoothCarrier 1 z‖ ≤
      C * (‖(z - zetaSpectralCoordinate rho.1)⁻¹‖ +
        ‖(z - starRingEnd ℂ (zetaSpectralCoordinate rho.1))⁻¹‖))
    {r : ℝ} (hr : 1 ≤ r) (c tau : ℝ) (z : ℂ) :
    ‖suzukiXiReflectionCompanionHeat rho r c tau z‖ ≤
      C * (‖(z - zetaSpectralCoordinate rho.1)⁻¹‖ +
        ‖(z - starRingEnd ℂ (zetaSpectralCoordinate rho.1))⁻¹‖) *
        ‖suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau (I * z)‖ := by
  simp only [suzukiXiReflectionCompanionHeat, norm_mul, norm_neg, norm_I, one_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (mul_le_mul_of_nonneg_left (norm_suzukiXiSmoothCarrier_le_one hr z) (norm_nonneg _)).trans (hC z)

private lemma companion_dominator_integrable (rho : NontrivialZetaZero) (C c : ℝ)
    {tau : ℝ} (htau : 0 < tau) :
    Integrable (fun z : ℂ => C * (‖(z - zetaSpectralCoordinate rho.1)⁻¹‖ +
      ‖(z - starRingEnd ℂ (zetaSpectralCoordinate rho.1))⁻¹‖) *
      ‖suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau (I * z)‖) := by
  have hcont : Continuous (fun z : ℂ =>
      suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau (I * z)) :=
    (continuous_suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau).comp (by fun_prop)
  have hga := integrable_suzukiSpectralCompanionHeat htau c
  have ha := integrable_norm_mul_inverse_distance hcont hga (zetaSpectralCoordinate rho.1)
  have hb := integrable_norm_mul_inverse_distance hcont hga (starRingEnd ℂ (zetaSpectralCoordinate rho.1))
  convert! (ha.add hb).const_mul C using 1
  funext z
  simp only [Pi.add_apply]
  ring

/-- The original companion heat term is integrable on the entire plane,
through both reflection nodes and every genuine carrier pole. -/
theorem integrable_suzukiXiReflectionCompanionHeat (rho : NontrivialZetaZero) {r tau : ℝ}
    (hr : 1 ≤ r) (htau : 0 < tau) (c : ℝ) :
    Integrable (suzukiXiReflectionCompanionHeat rho r c tau) := by
  obtain ⟨C, _hC, hbound⟩ := exists_suzukiXiReflectionCarrier_inverse_distance_bound rho
  exact (companion_dominator_integrable rho C c htau).mono'
    (companion_measurable rho (lt_of_lt_of_le zero_lt_one hr) c tau)
    (ae_of_all _ (companion_domination rho hbound hr c tau))

private lemma companion_tendsto (rho : NontrivialZetaZero) (c tau : ℝ) (z : ℂ) :
    Tendsto (fun r : ℝ => suzukiXiReflectionCompanionHeat rho r c tau z) atTop (𝓝 0) := by
  have hS : Tendsto (fun r : ℝ => suzukiXiSmoothCarrier r z) atTop (𝓝 0) := by
    have ht : Tendsto (fun r : ℝ => 1 / (2 * r)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop (by norm_num))
    apply squeeze_zero_norm' _ ht
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact norm_suzukiXiSmoothCarrier_le hr z
  simpa only [suzukiXiReflectionCompanionHeat, mul_zero, zero_mul] using
    (hS.const_mul (-I * suzukiXiReflectionWeight rho z)).mul_const
      (suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau (I * z))

/-- The actual companion heat contribution tends to zero in L1 on the
whole complex plane as smoothing grows at fixed positive Gaussian time.
Both reflection nodes are included, without punctures or principal values. -/
theorem tendsto_integral_norm_suzukiXiReflectionCompanionHeat (rho : NontrivialZetaZero)
    {tau : ℝ} (htau : 0 < tau) (c : ℝ) :
    Tendsto (fun r : ℝ => ∫ z : ℂ, ‖suzukiXiReflectionCompanionHeat rho r c tau z‖)
      atTop (𝓝 0) := by
  obtain ⟨C, _hC, hbound⟩ := exists_suzukiXiReflectionCarrier_inverse_distance_bound rho
  have hD := tendsto_integral_filter_of_dominated_convergence (l := (atTop : Filter ℝ))
    (F := fun r : ℝ => fun z => ‖suzukiXiReflectionCompanionHeat rho r c tau z‖)
    (f := fun _ => (0 : ℝ))
    (fun z => C * (‖(z - zetaSpectralCoordinate rho.1)⁻¹‖ +
      ‖(z - starRingEnd ℂ (zetaSpectralCoordinate rho.1))⁻¹‖) *
      ‖suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau (I * z)‖)
    ?_ ?_ (companion_dominator_integrable rho C c htau) ?_
  · simpa only [integral_zero] using hD
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact (companion_measurable rho hr c tau).norm
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact ae_of_all _ fun z => by
      simpa only [Real.norm_eq_abs, abs_norm] using companion_domination rho hbound hr c tau z
  · exact ae_of_all _ fun z => by
      simpa only [norm_zero] using (companion_tendsto rho c tau z).norm

/-- Global L1 decay controls the signed companion integral on arbitrary
moving spatial cutoffs, with no restrictions on their size or location. -/
theorem tendsto_setIntegral_suzukiXiReflectionCompanionHeat (rho : NontrivialZetaZero)
    {tau : ℝ} (htau : 0 < tau) (c : ℝ) (K : ℝ → Set ℂ) :
    Tendsto (fun r : ℝ => ∫ z in K r, suzukiXiReflectionCompanionHeat rho r c tau z)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (tendsto_integral_norm_suzukiXiReflectionCompanionHeat rho htau c)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  apply (norm_integral_le_integral_norm _).trans
  exact setIntegral_le_integral (integrable_suzukiXiReflectionCompanionHeat rho hr htau c).norm
    (ae_of_all _ fun _ => norm_nonneg _)

end
end RiemannGaussian
