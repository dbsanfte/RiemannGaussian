/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ComplexLogDerivativeIntegrability
import RiemannGaussian.SuzukiGammaArithmeticCutoff
import RiemannGaussian.SuzukiCarrierPoleResidues

/-!
# Absolute source decay inside the zero strip

The full normalized source factors through the logarithmic derivative
difference of the two genuine entire fields. Its simple poles are
locally integrable in area. This gives an independent compact L1 bound
through every xi zero and carrier pole, including repeated zeros.
The complex factorization is retained before its downstream norm bound.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

private lemma xi_nonzero_at_I : riemannXiSpectral I ≠ 0 :=
  riemannXiSpectral_ne_zero_of_half_le_abs_im (by norm_num)

private lemma xi_order_finite (z : ℂ) : analyticOrderAt riemannXiSpectral z ≠ ⊤ := by
  intro htop
  have hzero := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z analyticAt_riemannXiSpectral).mp htop
  exact xi_nonzero_at_I (congrFun hzero I)

/-- Both genuine logarithmic derivatives are locally integrable in
the full plane, so their signed difference has no nonintegrable poles. -/
theorem locallyIntegrable_suzukiXi_logDerivative_difference :
    LocallyIntegrable (fun z => logDeriv riemannXiSpectral z - logDeriv suzukiXiEValue z) volume := by
  have hA := locallyIntegrable_logDeriv_of_entire_finite_order analyticAt_riemannXiSpectral xi_order_finite
  have hE := locallyIntegrable_logDeriv_of_entire_finite_order analyticAt_suzukiXiEValue
    analyticOrderAt_suzukiXiEValue_ne_top
  exact hA.sub hE

/-- The exact full source factors through mass, carrier, and the
signed logarithmic Wronskian. It retains their complex phases and the
actual smoothing denominator. The original divisors are excluded only
from this logarithmic factorization, not from the integral estimates. -/
theorem suzukiXiSmoothCarrierSource_eq_logDerivative_difference {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hA : riemannXiSpectral z ≠ 0) (hE : suzukiXiEValue z ≠ 0) :
    suzukiXiSmoothCarrierSource r z = -2 * I * (r : ℂ) ^ 2 *
      (suzukiXiNormalizedMass r z : ℂ) * suzukiXiSmoothCarrier r z *
        starRingEnd ℂ (logDeriv riemannXiSpectral z - logDeriv suzukiXiEValue z) := by
  have hd := complexSmoothQuotient_denominator_pos hr (b := suzukiXiEValue z) (Or.inl hA)
  have hdC : ((normSq (suzukiXiEValue z) + r ^ 2 * normSq (riemannXiSpectral z) : ℝ) : ℂ) ≠ 0 :=
    by exact_mod_cast hd.ne'
  have hAc : starRingEnd ℂ (riemannXiSpectral z) ≠ 0 := by simpa only [map_ne_zero] using hA
  have hEc : starRingEnd ℂ (suzukiXiEValue z) ≠ 0 := by simpa only [map_ne_zero] using hE
  have hm : suzukiXiNormalizedMass r z = normSq (riemannXiSpectral z) /
      (normSq (suzukiXiEValue z) + r ^ 2 * normSq (riemannXiSpectral z)) := rfl
  rw [hm]
  unfold suzukiXiSmoothCarrierSource suzukiXiSmoothCarrier complexSmoothQuotient
  rw [complexSmoothQuotient_denominator]
  simp only [logDeriv_apply, map_sub, map_mul, map_div₀, normSq_I, one_mul, ofReal_div]
  rw [← Complex.mul_conj (riemannXiSpectral z)]
  field_simp
  ring_nf
  simp only [I_sq]
  ring

/-- Almost everywhere on the whole plane, the complete source has an
inverse-smoothing bound by one fixed locally integrable logarithmic
Wronskian. No zero-free strip or simplicity hypothesis is used. -/
theorem ae_norm_suzukiXiSmoothCarrierSource_le_logDerivative_difference {r : ℝ} (hr : 0 < r) :
    ∀ᵐ z : ℂ, ‖suzukiXiSmoothCarrierSource r z‖ ≤
      ‖logDeriv riemannXiSpectral z - logDeriv suzukiXiEValue z‖ / r := by
  have hA := ae_ne_zero_of_entire_nonzero analyticAt_riemannXiSpectral xi_nonzero_at_I
  have hE := ae_ne_zero_of_entire_nonzero analyticAt_suzukiXiEValue
    (suzukiXiEValue_ne_zero_of_half_le_im (z := I) (by norm_num))
  filter_upwards [hA, hE] with z hzA hzE
  rw [suzukiXiSmoothCarrierSource_eq_logDerivative_difference hr hzA hzE]
  simp only [norm_mul, norm_neg, norm_pow, norm_conj, norm_I, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_one,
    abs_of_nonneg (suzukiXiNormalizedMass_nonneg r z)]
  calc
    _ ≤ 2 * r ^ 2 * (1 / r ^ 2) * (1 / (2 * r)) *
        ‖logDeriv riemannXiSpectral z - logDeriv suzukiXiEValue z‖ := by
      gcongr
      · exact suzukiXiNormalizedMass_le hr z
      · exact norm_suzukiXiSmoothCarrier_le hr z
    _ = _ := by field_simp

/-- On every compact planar region the full source has a quantitative
absolute integral bound, including all zeros and genuine carrier poles
inside that region. The right side retains the signed logarithmic
difference before its norm is taken. -/
theorem integral_norm_suzukiXiSmoothCarrierSource_compact_le {r : ℝ} (hr : 0 < r)
    {K : Set ℂ} (hK : IsCompact K) :
    (∫ z in K, ‖suzukiXiSmoothCarrierSource r z‖) ≤
      (∫ z in K, ‖logDeriv riemannXiSpectral z - logDeriv suzukiXiEValue z‖) / r := by
  have hD := (locallyIntegrable_suzukiXi_logDerivative_difference.integrableOn_isCompact hK).norm
  calc
    _ ≤ ∫ z in K, ‖logDeriv riemannXiSpectral z - logDeriv suzukiXiEValue z‖ / r := by
      apply integral_mono_ae
        ((continuous_suzukiXiSmoothCarrierSource hr).norm.continuousOn.integrableOn_compact hK)
        (hD.div_const r)
      exact ae_restrict_of_ae (ae_norm_suzukiXiSmoothCarrierSource_le_logDerivative_difference hr)
    _ = _ := integral_div r _

/-- The actual normalized arithmetic source is continuous throughout
the upper spectral half-plane, including common zeros and carrier poles.
The smooth xi source and its exact mass correction justify those values. -/
theorem continuousOn_suzukiGammaShiftArithmeticSource_upper {r : ℝ} (hr : 0 < r) :
    ContinuousOn (fun z => suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z))
      {z : ℂ | 0 ≤ z.im} := by
  have hs {z : ℂ} (hz : 0 ≤ z.im) : 0 < (suzukiArithmeticZetaArgument z).re := by
    rw [suzukiArithmeticZetaArgument_re]
    linarith
  have harg : Continuous suzukiArithmeticZetaArgument := by unfold suzukiArithmeticZetaArgument; fun_prop
  have hQ : ContinuousOn (fun z => starRingEnd ℂ (deriv suzukiGammaShiftCorrection
      (suzukiArithmeticZetaArgument z))) {z : ℂ | 0 ≤ z.im} := by
    intro z hz
    exact (Complex.continuous_conj.continuousAt.comp
      ((analyticAt_suzukiGammaShiftCorrection (hs hz)).deriv.continuousAt.comp harg.continuousAt)).continuousWithinAt
  have hU : ContinuousOn (fun z => (suzukiXiNormalizedMass r z : ℂ)) {z : ℂ | 0 ≤ z.im} :=
    (Complex.continuous_ofReal.comp (contDiff_suzukiXiNormalizedMass hr).continuous).continuousOn
  have hC : ContinuousOn (fun z => -2 * I * (r : ℂ) ^ 2 * (suzukiXiNormalizedMass r z : ℂ) ^ 2 *
      starRingEnd ℂ (deriv suzukiGammaShiftCorrection (suzukiArithmeticZetaArgument z)))
        {z : ℂ | 0 ≤ z.im} := (continuousOn_const.mul (hU.pow 2)).mul hQ
  apply ((continuous_suzukiXiSmoothCarrierSource hr).continuousOn.sub hC).congr
  intro z hz
  have he := suzukiXiSmoothCarrierSource_eq_gammaShift hr (hs hz)
  rw [suzukiGammaShiftSpectralSource_eq_add (hs hz),
    suzukiGammaShiftCompletionSource_eq_mass, ← suzukiXiNormalizedMass_eq_gammaShift r (hs hz)] at he
  change _ = suzukiXiSmoothCarrierSource r z -
    (-2 * I * (r : ℂ) ^ 2 * (suzukiXiNormalizedMass r z : ℂ) ^ 2 *
      starRingEnd ℂ (deriv suzukiGammaShiftCorrection (suzukiArithmeticZetaArgument z)))
  rw [he]
  ring

/-- On every compact upper planar region, including the zero strip,
the full normalized arithmetic source has an unconditional absolute
integral bound `C_K/r`. All analytic poles and multiple zeros are included. -/
theorem exists_integral_norm_suzukiGammaShiftArithmeticSource_compact_bound
    {K : Set ℂ} (hK : IsCompact K) (hupper : K ⊆ {z : ℂ | 0 ≤ z.im}) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r →
      (∫ z in K, ‖suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z)‖) ≤ C / r := by
  let H := fun z : ℂ => ‖logDeriv riemannXiSpectral z - logDeriv suzukiXiEValue z‖ + 1 / 4
  have hH : IntegrableOn H K :=
    (locallyIntegrable_suzukiXi_logDerivative_difference.integrableOn_isCompact hK).norm.add
      (continuous_const.continuousOn.integrableOn_compact hK)
  refine ⟨∫ z in K, H z, integral_nonneg (fun _ => by dsimp [H]; positivity), ?_⟩
  intro r hr
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hA : IntegrableOn (fun z => ‖suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z)‖) K volume :=
    (((continuousOn_suzukiGammaShiftArithmeticSource_upper hr0).mono hupper).norm).integrableOn_compact hK
  calc
    _ ≤ ∫ z in K, H z / r := by
      apply integral_mono_ae hA (hH.div_const r)
      filter_upwards [ae_restrict_of_ae (s := K)
          (ae_norm_suzukiXiSmoothCarrierSource_le_logDerivative_difference hr0),
        ae_restrict_mem hK.measurableSet] with z hz hzK
      have hs : 0 < (suzukiArithmeticZetaArgument z).re := by
        rw [suzukiArithmeticZetaArgument_re]
        have hzu : 0 ≤ z.im := hupper hzK
        linarith
      have he := norm_suzukiXiSmoothCarrierSource_gammaShift_error_le hr0 hs (1 : ℂ)
      simp only [one_mul, norm_one] at he
      have ht := norm_sub_le (suzukiXiSmoothCarrierSource r z)
        (suzukiXiSmoothCarrierSource r z -
          suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z))
      rw [sub_sub_cancel] at ht
      apply (ht.trans (add_le_add hz he)).trans
      have hrate : 1 / (4 * r ^ 2) ≤ (1 / 4) / r := by
        apply (div_le_div_iff₀ (by positivity) hr0).mpr
        nlinarith
      dsimp [H]
      rw [add_div]
      exact add_le_add le_rfl hrate
    _ = _ := integral_div r _

/-- One compact-region constant controls every measurable complex
weight family with a common norm budget. The weights may change with
smoothing; their complete complex values remain in the source. -/
theorem exists_suzukiGammaShiftArithmeticSource_compact_all_weight_bound
    {K : Set ℂ} (hK : IsCompact K) (hupper : K ⊆ {z : ℂ | 0 ≤ z.im}) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ M : ℝ, 0 ≤ M → ∀ P : ℂ → ℂ,
      AEStronglyMeasurable P (volume.restrict K) →
      (∀ᵐ z ∂volume.restrict K, ‖P z‖ ≤ M) →
      (∫ z in K, ‖P z * suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z)‖) ≤ M * C / r := by
  obtain ⟨C, hC, hbound⟩ := exists_integral_norm_suzukiGammaShiftArithmeticSource_compact_bound hK hupper
  refine ⟨C, hC, ?_⟩
  intro r hr M hM P hP hPM
  have hA : IntegrableOn (fun z => suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z)) K :=
    ((continuousOn_suzukiGammaShiftArithmeticSource_upper (lt_of_lt_of_le zero_lt_one hr)).mono
      hupper).integrableOn_compact hK
  calc
    _ ≤ ∫ z in K, M * ‖suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z)‖ := by
      apply integral_mono_ae (hA.bdd_mul hP hPM).norm (hA.norm.const_mul M)
      filter_upwards [hPM] with z hz
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
    _ = M * ∫ z in K, ‖suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z)‖ :=
      integral_const_mul _ _
    _ ≤ M * (C / r) := mul_le_mul_of_nonneg_left (hbound r hr) hM
    _ = _ := by ring

/-- In the upper half-plane the full original reflection weight costs
at most four times the inverse square distance to the upper reflected
node. The lower node's distance pays its exact numerator. -/
theorem norm_suzukiXiReflectionWeight_le_reflected_distance
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) {z : ℂ}
    (hz : 0 ≤ z.im) (hb : z ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1)) :
    ‖suzukiXiReflectionWeight rho z‖ ≤ 4 / ‖z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)‖ ^ 2 := by
  let a := zetaSpectralCoordinate rho.1
  have ha : a.im < 0 := by dsimp [a]; rw [zetaSpectralCoordinate_im]; linarith
  have hdist : -a.im ≤ ‖z - a‖ := by
    have hh := Complex.im_le_norm (z - a)
    simp only [sub_im] at hh
    linarith
  have hda : 0 < ‖z - a‖ := (neg_pos.mpr ha).trans_le hdist
  have hdb : 0 < ‖z - starRingEnd ℂ a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hb)
  have hza : z ≠ a := sub_ne_zero.mp (norm_pos_iff.mp hda)
  rw [suzukiXiReflectionWeight_eq_quartic rho hza hb, norm_div, norm_mul, norm_pow,
    norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  norm_num only [norm_ofNat]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hh : a.im ^ 2 ≤ ‖z - a‖ ^ 2 := by nlinarith
  have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖z - starRingEnd ℂ a‖)
  dsimp [a] at hh'
  nlinarith

/-- Outside any positive-radius disk about the reflected zero, the
full weighted arithmetic source has bound `C/(r*epsilon^2)` on a fixed
compact upper region. One constant works for every selected right-half
zero, radius and smoothing parameter, through all other zeros and poles. -/
theorem exists_integral_norm_suzukiGammaShiftWeightedArithmeticSource_outside_ball_bound
    {K : Set ℂ} (hK : IsCompact K) (hupper : K ⊆ {z : ℂ | 0 ≤ z.im}) (c tau : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : NontrivialZetaZero, 1 / 2 < rho.1.re →
      ∀ r : ℝ, 1 ≤ r → ∀ epsilon : ℝ, 0 < epsilon →
      (∫ z in K \ ball (starRingEnd ℂ (zetaSpectralCoordinate rho.1)) epsilon,
        ‖suzukiGammaShiftWeightedArithmeticSource rho r c tau z‖) ≤ C / (r * epsilon ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_integral_norm_suzukiGammaShiftArithmeticSource_compact_bound hK hupper
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (differentiable_suzukiSmoothSpectralBoundaryHeat c tau).continuous.continuousOn
  let B := max M 0
  have hB : 0 ≤ B := le_max_right _ _
  have hBbound : ∀ z ∈ K, ‖suzukiSmoothSpectralBoundaryHeat c tau z‖ ≤ B :=
    fun z hz => (hM z hz).trans (le_max_left _ _)
  refine ⟨4 * B * C, by positivity, ?_⟩
  intro rho hzero r hr epsilon hepsilon
  let b := starRingEnd ℂ (zetaSpectralCoordinate rho.1)
  let F := K \ ball b epsilon
  have hF : IsCompact F := hK.diff isOpen_ball
  have hFK : F ⊆ K := sdiff_subset
  have hfar : ∀ z ∈ F, epsilon ≤ ‖z - b‖ := by
    intro z hz
    exact le_of_not_gt (by simpa only [mem_ball, dist_eq_norm] using hz.2)
  have hb : ∀ z ∈ F, z ≠ b := by
    intro z hz hzb
    subst z
    have hh := hfar b hz
    simp only [sub_self, norm_zero] at hh
    linarith
  have ha : ∀ z ∈ F, z ≠ zetaSpectralCoordinate rho.1 := by
    intro z hz hza
    have hh : 0 ≤ z.im := hupper (hFK hz)
    rw [hza, zetaSpectralCoordinate_im] at hh
    linarith
  have hW : ContinuousOn (suzukiXiReflectionWeight rho) F :=
    fun z hz => (analyticAt_suzukiXiReflectionWeight rho (ha z hz) (hb z hz)).continuousAt.continuousWithinAt
  have hHeat := (differentiable_suzukiSmoothSpectralBoundaryHeat c tau).continuous.continuousOn (s := F)
  have hA := (continuousOn_suzukiGammaShiftArithmeticSource_upper
    (lt_of_lt_of_le zero_lt_one hr)).mono (hFK.trans hupper)
  have hInt : IntegrableOn (suzukiGammaShiftWeightedArithmeticSource rho r c tau) F :=
    ((hW.mul hHeat).mul hA).integrableOn_compact hF
  have hAK : IntegrableOn (fun z => suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z)) K :=
    ((continuousOn_suzukiGammaShiftArithmeticSource_upper
      (lt_of_lt_of_le zero_lt_one hr)).mono hupper).integrableOn_compact hK
  calc
    _ ≤ ∫ z in F, (4 * B / epsilon ^ 2) *
        ‖suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z)‖ := by
      apply integral_mono_ae hInt.norm ((IntegrableOn.mono_set hAK.norm hFK).const_mul _)
      filter_upwards [ae_restrict_mem hF.measurableSet] with z hz
      have hw := (norm_suzukiXiReflectionWeight_le_reflected_distance rho hzero (hupper (hFK hz))
        (hb z hz)).trans
          (div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hepsilon)
            (pow_le_pow_left₀ hepsilon.le (hfar z hz) 2))
      unfold suzukiGammaShiftWeightedArithmeticSource
      simp only [norm_mul]
      calc
        _ ≤ (4 / epsilon ^ 2) * B *
            ‖suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z)‖ := by
          gcongr
          exact hBbound z (hFK hz)
        _ = _ := by ring
    _ = (4 * B / epsilon ^ 2) * ∫ z in F,
        ‖suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z)‖ := integral_const_mul _ _
    _ ≤ (4 * B / epsilon ^ 2) * ∫ z in K,
        ‖suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z)‖ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact setIntegral_mono_set hAK.norm (ae_of_all _ fun _ => norm_nonneg _)
        (ae_of_all _ fun _ hz => hFK hz)
    _ ≤ (4 * B / epsilon ^ 2) * (C / r) := mul_le_mul_of_nonneg_left (hbound r hr) (by positivity)
    _ = _ := by ring

/-- Even a shrinking reflected neighborhood captures all nonnegligible
arithmetic mass whenever `r*epsilon(r)^2` tends to infinity. This is a
uniform estimate of the full complex source outside that neighborhood. -/
theorem tendsto_integral_norm_suzukiGammaShiftWeightedArithmeticSource_outside_moving_ball
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re)
    {K : Set ℂ} (hK : IsCompact K) (hupper : K ⊆ {z : ℂ | 0 ≤ z.im}) (c tau : ℝ)
    (epsilon : ℝ → ℝ) (hepsilon : ∀ᶠ r in atTop, 0 < epsilon r)
    (hscale : Tendsto (fun r : ℝ => r * epsilon r ^ 2) atTop atTop) :
    Tendsto (fun r : ℝ => ∫ z in K \ ball (starRingEnd ℂ (zetaSpectralCoordinate rho.1)) (epsilon r),
      ‖suzukiGammaShiftWeightedArithmeticSource rho r c tau z‖) atTop (𝓝 0) := by
  obtain ⟨C, _hC, hbound⟩ :=
    exists_integral_norm_suzukiGammaShiftWeightedArithmeticSource_outside_ball_bound hK hupper c tau
  have ht : Tendsto (fun r : ℝ => C / (r * epsilon r ^ 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hscale
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _) _ ht
  filter_upwards [eventually_ge_atTop (1 : ℝ), hepsilon] with r hr he
  exact hbound rho hzero r hr (epsilon r) he

open scoped Interval in
/-- The complete hypothetical-zero source is captured by a moving
reflected neighborhood whenever its radius obeys `r*epsilon(r)^2 -> infinity`.
All other zero and carrier-pole contributions have an independent absolute
bound tending to zero outside that neighborhood. -/
theorem tendsto_suzukiGammaShiftWeightedArithmeticSource_moving_reflected_ball
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) {tau R : ℝ}
    (htau : 0 < tau) (hR : 1 ≤ R) (c : ℝ) (hc : 2 * |c| ≤ R)
    (hRe : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R)
    (epsilon : ℝ → ℝ) (hepsilon : ∀ᶠ r in atTop, 0 < epsilon r)
    (hscale : Tendsto (fun r : ℝ => r * epsilon r ^ 2) atTop atTop) :
    Tendsto (fun r : ℝ => ∫ z in (([[-R,R]] ×ℂ [[0,R]]) ∩
      ball (starRingEnd ℂ (zetaSpectralCoordinate rho.1)) (epsilon r)),
        suzukiGammaShiftWeightedArithmeticSource rho r c tau z) atTop
      (𝓝 ((2 * Real.pi * I) * ((analyticZetaZeroMultiplicity rho : ℂ)⁻¹ *
        suzukiSmoothSpectralBoundaryHeat c tau (starRingEnd ℂ (zetaSpectralCoordinate rho.1))))) := by
  let K : Set ℂ := [[-R,R]] ×ℂ [[0,R]]
  have hK : IsCompact K := isCompact_uIcc.reProdIm isCompact_uIcc
  have hupper : K ⊆ {z : ℂ | 0 ≤ z.im} := by
    intro z hz
    have hy := hz.2
    rw [uIcc_of_le (show 0 ≤ R by linarith)] at hy
    exact hy.1
  have hfull := tendsto_suzukiGammaShiftWeightedArithmeticSource_moving_rectangle
    rho hzero htau c (fun _ => R) (fun _ => hR) (fun _ => hc) (fun _ => hRe)
  have hnorm := tendsto_integral_norm_suzukiGammaShiftWeightedArithmeticSource_outside_moving_ball
    rho hzero hK hupper c tau epsilon hepsilon hscale
  have htail : Tendsto (fun r : ℝ => ∫ z in K \
      ball (starRingEnd ℂ (zetaSpectralCoordinate rho.1)) (epsilon r),
        suzukiGammaShiftWeightedArithmeticSource rho r c tau z) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hnorm
    exact Eventually.of_forall fun _ => norm_integral_le_integral_norm _
  have h := hfull.sub htail
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hA := integrableOn_suzukiGammaShiftWeightedArithmeticSource rho hr htau c hK hupper
  have he := integral_inter_add_sdiff (s := K)
    (t := ball (starRingEnd ℂ (zetaSpectralCoordinate rho.1)) (epsilon r)) measurableSet_ball hA
  change (∫ z in K, suzukiGammaShiftWeightedArithmeticSource rho r c tau z) -
      (∫ z in K \ ball (starRingEnd ℂ (zetaSpectralCoordinate rho.1)) (epsilon r),
        suzukiGammaShiftWeightedArithmeticSource rho r c tau z) = _
  rw [← he]
  ring

end
end RiemannGaussian
