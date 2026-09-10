/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiGammaShiftSource
import RiemannGaussian.GaussianArchimedeanContour

/-!
# Decay of the actual reflected Gamma completion contribution

The actual xi mass vanishes quadratically at both reflection nodes. Keeping
that information before estimating the singular reflection weight gives a
global integrable Gaussian dominator for the completed source contribution.
-/

open Complex Filter MeasureTheory Set Topology
namespace RiemannGaussian
noncomputable section

/-- The globally normalized actual mass has a quadratic envelope about
each original zero, with all multiplicities supplied by the analytic chart. -/
theorem exists_suzukiXiNormalizedMass_quadratic_bound (rho : NontrivialZetaZero) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      suzukiXiNormalizedMass 1 z ≤ C * ‖z - zetaSpectralCoordinate rho.1‖ ^ 2 := by
  let a := zetaSpectralCoordinate rho.1
  obtain ⟨q, hq, _hq0, he⟩ := exists_suzukiXiNormalizedMass_zero_chart rho 1
  have hb : ∀ᶠ z in 𝓝 a, ‖q z‖ < ‖q a‖ + 1 :=
    hq.continuousAt.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨d, hd, hlocal⟩ := Metric.eventually_nhds_iff.mp (he.and hb)
  let C := max ((‖q a‖ + 1) ^ 2) (1 / d ^ 2)
  refine ⟨C, le_trans (sq_nonneg _) (le_max_left _ _), ?_⟩
  intro z
  by_cases hz : ‖z - a‖ < d
  · obtain ⟨heq, hqz⟩ := hlocal (by simpa only [dist_eq_norm] using hz)
    rw [heq]
    simp only [one_pow, one_mul]
    calc
      _ ≤ normSq ((z - a) * q z) := by
        exact div_le_self (normSq_nonneg _) (by linarith [normSq_nonneg ((z - a) * q z)])
      _ = ‖z - a‖ ^ 2 * ‖q z‖ ^ 2 := by rw [map_mul, normSq_eq_norm_sq, normSq_eq_norm_sq]
      _ ≤ C * ‖z - a‖ ^ 2 := by
        have hq2 : ‖q z‖ ^ 2 ≤ (‖q a‖ + 1) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hqz.le 2
        have hqC : ‖q z‖ ^ 2 ≤ C := hq2.trans (le_max_left _ _)
        nlinarith [mul_le_mul_of_nonneg_right hqC (sq_nonneg ‖z - a‖)]
  · have hm : suzukiXiNormalizedMass 1 z ≤ 1 := by
      simpa using suzukiXiNormalizedMass_le (r := 1) (by norm_num) z
    have hn : d ^ 2 ≤ ‖z - a‖ ^ 2 := pow_le_pow_left₀ hd.le (le_of_not_gt hz) 2
    calc
      _ ≤ 1 := hm
      _ ≤ (1 / d ^ 2) * ‖z - a‖ ^ 2 := by
        rw [one_div_mul_eq_div]
        exact (le_div_iff₀ (sq_pos_of_pos hd)).mpr (by simpa using hn)
      _ ≤ C * ‖z - a‖ ^ 2 := mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)

/-- The complete singular reflection weight times the actual mass at
unit smoothing is globally bounded; both reflection poles are included. -/
theorem exists_norm_suzukiXiReflectionWeight_mul_mass_bound (rho : NontrivialZetaZero) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖suzukiXiReflectionWeight rho z‖ * suzukiXiNormalizedMass 1 z ≤ C := by
  obtain ⟨Ca, hCa, ha⟩ := exists_suzukiXiNormalizedMass_quadratic_bound rho
  obtain ⟨Cb, hCb, hb⟩ := exists_suzukiXiNormalizedMass_quadratic_bound rho.conjugatePartner
  simp only [NontrivialZetaZero.spectralCoordinate_conjugatePartner] at hb
  refine ⟨2 * (Ca + Cb), by positivity, ?_⟩
  intro z
  have hterm (a : ℂ) (C : ℝ) (hC : 0 ≤ C)
      (h : suzukiXiNormalizedMass 1 z ≤ C * ‖z - a‖ ^ 2) :
      ‖(z - a)⁻¹‖ ^ 2 * suzukiXiNormalizedMass 1 z ≤ C := by
    by_cases hz : z - a = 0
    · simpa [hz] using hC
    · rw [norm_inv, inv_pow]
      calc
        _ ≤ (‖z - a‖ ^ 2)⁻¹ * (C * ‖z - a‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h (by positivity)
        _ = C := by field_simp
  have hwa := hterm _ _ hCa (ha z)
  have hwb := hterm _ _ hCb (hb z)
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
  have hm := suzukiXiNormalizedMass_nonneg 1 z
  nlinarith [mul_le_mul_of_nonneg_right hw hm]

/-- At all smoothing parameters at least one, the squared actual mass
is dominated by the same mass at unit smoothing. -/
theorem suzukiXiNormalizedMass_scaled_square_le {r : ℝ} (hr : 1 ≤ r) (z : ℂ) :
    r ^ 2 * suzukiXiNormalizedMass r z ^ 2 ≤ suzukiXiNormalizedMass 1 z := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hu := suzukiXiNormalizedMass_le hr0 z
  have hun := suzukiXiNormalizedMass_nonneg r z
  have hru : r ^ 2 * suzukiXiNormalizedMass r z ≤ 1 := by
    have h := (le_div_iff₀ (sq_pos_of_pos hr0)).mp hu
    nlinarith
  have hmono : suzukiXiNormalizedMass r z ≤ suzukiXiNormalizedMass 1 z := by
    by_cases hA : riemannXiSpectral z = 0
    · simp [suzukiXiNormalizedMass_eq_zero _ hA]
    have hp := complexSmoothQuotient_denominator_pos (r := 1) (by norm_num)
      (b := suzukiXiEValue z) (Or.inl hA)
    change normSq (riemannXiSpectral z) /
        (normSq (suzukiXiEValue z) + r ^ 2 * normSq (riemannXiSpectral z)) ≤
      normSq (riemannXiSpectral z) /
        (normSq (suzukiXiEValue z) + 1 ^ 2 * normSq (riemannXiSpectral z))
    apply div_le_div_of_nonneg_left (normSq_nonneg _) hp
    nlinarith [normSq_nonneg (riemannXiSpectral z), sq_nonneg (r - 1),
      mul_nonneg (show 0 ≤ r ^ 2 - 1 by nlinarith [sq_nonneg (r - 1)])
        (normSq_nonneg (riemannXiSpectral z))]
  nlinarith [mul_le_mul_of_nonneg_right hru hun]

/-- The full spectral boundary heat is integrable in the plane for
every positive Gaussian time. -/
theorem integrable_suzukiSmoothSpectralBoundaryHeat {tau : ℝ} (htau : 0 < tau) (c : ℝ) :
    Integrable (suzukiSmoothSpectralBoundaryHeat c tau) := by
  have hx := integrable_translatedGaussian htau c
  have hy := (integrable_mul_exp_neg_mul_sq htau).const_mul 2
  have hp := hx.mul_prod hy
  have hc := Complex.volume_preserving_equiv_real_prod.integrable_comp hp.aestronglyMeasurable
  have hreal : Integrable (fun z : ℂ =>
      2 * z.im * Real.exp (-tau * ((c - z.re) ^ 2 + z.im ^ 2))) := by
    convert! hc.mpr hp using 1
    funext z
    simp only [Function.comp_def, Complex.measurableEquivRealProd_apply,
      translatedGaussian, mul_add, Real.exp_add]
    rw [sub_sq_comm c z.re]
    ring
  convert! hreal.ofReal (𝕜 := ℂ) using 1
  exact funext (suzukiSmoothSpectralBoundaryHeat_eq c tau)

/-- The literal difference between the full reflected xi source and
its normalized arithmetic contribution; the original reflection weight
and Gaussian are retained inside the expression. -/
def suzukiGammaShiftReflectionError (rho : NontrivialZetaZero) (r c tau : ℝ) (z : ℂ) : ℂ :=
  suzukiXiReflectionWeight rho z * suzukiSmoothSpectralBoundaryHeat c tau z *
    (suzukiXiSmoothCarrierSource r z -
      suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z))

/-- The remaining arithmetic reflection density retains the full
denominator, original reflection phase and original companion heat term. -/
def suzukiGammaShiftArithmeticReflectionSource (rho : NontrivialZetaZero)
    (r c tau : ℝ) (z : ℂ) : ℂ :=
  suzukiXiReflectionWeight rho z *
    (suzukiSmoothSpectralBoundaryHeat c tau z *
      suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z) -
      I * suzukiXiSmoothCarrier r z *
        suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau (I * z))

/-- The original complete reflected source is exactly the remaining
arithmetic density plus the independently controlled completion error. -/
theorem suzukiXiSmoothReflectionSource_eq_gammaShift_add_error
    (rho : NontrivialZetaZero) (r c tau : ℝ) (z : ℂ) :
    suzukiXiSmoothReflectionSource rho r c tau z =
      suzukiGammaShiftArithmeticReflectionSource rho r c tau z +
        suzukiGammaShiftReflectionError rho r c tau z := by
  unfold suzukiXiSmoothReflectionSource suzukiXiSmoothBoundaryHeatBulk
    suzukiGammaShiftArithmeticReflectionSource suzukiGammaShiftReflectionError
  ring

private lemma upper_argument {z : ℂ} (hz : 0 ≤ z.im) :
    0 < (suzukiArithmeticZetaArgument z).re := by
  rw [suzukiArithmeticZetaArgument_re]
  linarith

/-- The exact reflected error is the completion curvature times the
squared actual mass. This identity precedes any norm or integration. -/
theorem suzukiGammaShiftReflectionError_eq_mass (rho : NontrivialZetaZero) {r : ℝ}
    (hr : 0 < r) (c tau : ℝ) {z : ℂ} (hz : 0 ≤ z.im) :
    suzukiGammaShiftReflectionError rho r c tau z =
      (-2 * I * (r : ℂ) ^ 2) * suzukiXiReflectionWeight rho z *
        suzukiSmoothSpectralBoundaryHeat c tau z * (suzukiXiNormalizedMass r z : ℂ) ^ 2 *
        starRingEnd ℂ (deriv suzukiGammaShiftCorrection (suzukiArithmeticZetaArgument z)) := by
  unfold suzukiGammaShiftReflectionError
  rw [suzukiXiSmoothCarrierSource_eq_gammaShift hr (upper_argument hz),
    suzukiGammaShiftSpectralSource_eq_add (upper_argument hz), add_sub_cancel_left,
    suzukiGammaShiftCompletionSource_eq_mass, ← suzukiXiNormalizedMass_eq_gammaShift r (upper_argument hz)]
  ring

private lemma reflection_error_measurable (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r)
    (c tau : ℝ) : AEStronglyMeasurable (suzukiGammaShiftReflectionError rho r c tau)
      (volume.restrict {z : ℂ | 0 ≤ z.im}) := by
  have hm : MeasurableSet {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const Complex.continuous_im |>.measurableSet
  have hW : Measurable (suzukiXiReflectionWeight rho) := by
    unfold suzukiXiReflectionWeight suzukiXiReflectionCauchyDifference
    fun_prop
  have hQ : ContinuousOn (fun z => deriv suzukiGammaShiftCorrection (suzukiArithmeticZetaArgument z))
      {z : ℂ | 0 ≤ z.im} := by
    intro z hz
    exact ((analyticAt_suzukiGammaShiftCorrection (upper_argument hz)).deriv.continuousAt.comp
      (f := suzukiArithmeticZetaArgument) (by unfold suzukiArithmeticZetaArgument; fun_prop)).continuousWithinAt
  have hB := (differentiable_suzukiSmoothSpectralBoundaryHeat c tau).continuous.aestronglyMeasurable (μ := volume)
  have hU := (Complex.continuous_ofReal.comp (contDiff_suzukiXiNormalizedMass hr).continuous).aestronglyMeasurable
    (μ := volume)
  have hprod : AEStronglyMeasurable (fun z =>
      (-2 * I * (r : ℂ) ^ 2) * suzukiXiReflectionWeight rho z *
        suzukiSmoothSpectralBoundaryHeat c tau z * (suzukiXiNormalizedMass r z : ℂ) ^ 2 *
        starRingEnd ℂ (deriv suzukiGammaShiftCorrection (suzukiArithmeticZetaArgument z)))
      (volume.restrict {z : ℂ | 0 ≤ z.im}) := by
    exact ((((aestronglyMeasurable_const.mul hW.aestronglyMeasurable).mul hB).mul
      (hU.pow 2)).mono_measure Measure.restrict_le_self).mul (hQ.aestronglyMeasurable hm).star
  apply hprod.congr
  filter_upwards [ae_restrict_mem hm] with z hz
  exact (suzukiGammaShiftReflectionError_eq_mass rho hr c tau hz).symm

private lemma reflection_error_domination (rho : NontrivialZetaZero) {C : ℝ}
    (hC : ∀ z : ℂ, ‖suzukiXiReflectionWeight rho z‖ * suzukiXiNormalizedMass 1 z ≤ C)
    {r : ℝ} (hr : 1 ≤ r) (c tau : ℝ) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖suzukiGammaShiftReflectionError rho r c tau z‖ ≤
      (C / 4) * ‖suzukiSmoothSpectralBoundaryHeat c tau z‖ := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [suzukiGammaShiftReflectionError_eq_mass rho hr0 c tau hz]
  simp only [norm_mul, norm_neg, norm_pow, norm_conj, norm_I, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_one]
  calc
    _ = 2 * (r ^ 2 * suzukiXiNormalizedMass r z ^ 2) *
        ‖suzukiXiReflectionWeight rho z‖ * ‖suzukiSmoothSpectralBoundaryHeat c tau z‖ *
        ‖deriv suzukiGammaShiftCorrection (suzukiArithmeticZetaArgument z)‖ := by ring
    _ ≤ 2 * suzukiXiNormalizedMass 1 z * ‖suzukiXiReflectionWeight rho z‖ *
        ‖suzukiSmoothSpectralBoundaryHeat c tau z‖ * (1 / 8) := by
      gcongr
      · positivity [suzukiXiNormalizedMass_nonneg 1 z]
      · exact suzukiXiNormalizedMass_scaled_square_le hr z
      · exact norm_deriv_suzukiGammaShiftCorrection_le (upper_argument hz)
    _ ≤ _ := by
      nlinarith [mul_le_mul_of_nonneg_right (hC z)
        (norm_nonneg (suzukiSmoothSpectralBoundaryHeat c tau z))]

/-- The actual full reflected completion error is integrable on the
whole upper half-plane, including the reflected zero, at every smoothing
parameter at least one and positive Gaussian time. -/
theorem integrableOn_suzukiGammaShiftReflectionError (rho : NontrivialZetaZero) {r tau : ℝ}
    (hr : 1 ≤ r) (htau : 0 < tau) (c : ℝ) :
    IntegrableOn (suzukiGammaShiftReflectionError rho r c tau) {z : ℂ | 0 ≤ z.im} := by
  obtain ⟨C, _hC, hbound⟩ := exists_norm_suzukiXiReflectionWeight_mul_mass_bound rho
  have hi := ((integrable_suzukiSmoothSpectralBoundaryHeat htau c).norm.const_mul (C / 4)).integrableOn
    (s := {z : ℂ | 0 ≤ z.im})
  refine hi.mono' (reflection_error_measurable rho (lt_of_lt_of_le zero_lt_one hr) c tau) ?_
  filter_upwards [ae_restrict_mem (isClosed_le continuous_const Complex.continuous_im).measurableSet] with z hz
  exact reflection_error_domination rho hbound hr c tau hz

private lemma reflection_error_tendsto (rho : NontrivialZetaZero) (c tau : ℝ) {z : ℂ}
    (hz : 0 ≤ z.im) :
    Tendsto (fun r : ℝ => suzukiGammaShiftReflectionError rho r c tau z) atTop (𝓝 0) := by
  have ht : Tendsto (fun r : ℝ =>
      ‖suzukiXiReflectionWeight rho z * suzukiSmoothSpectralBoundaryHeat c tau z‖ /
        (4 * r ^ 2)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop (by norm_num))
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact norm_suzukiXiSmoothCarrierSource_gammaShift_error_le hr (upper_argument hz) _

/-- The full actual reflected completion contribution tends to zero in
L1 on the whole upper half-plane. No reflection node is excised and no
growing-rectangle limit or unproved arithmetic bound is used. -/
theorem tendsto_integral_norm_suzukiGammaShiftReflectionError (rho : NontrivialZetaZero)
    {tau : ℝ} (htau : 0 < tau) (c : ℝ) :
    Tendsto (fun r : ℝ => ∫ z in {z : ℂ | 0 ≤ z.im},
      ‖suzukiGammaShiftReflectionError rho r c tau z‖) atTop (𝓝 0) := by
  obtain ⟨C, _hC, hbound⟩ := exists_norm_suzukiXiReflectionWeight_mul_mass_bound rho
  have hm : MeasurableSet {z : ℂ | 0 ≤ z.im} := (isClosed_le continuous_const Complex.continuous_im).measurableSet
  have hD := tendsto_integral_filter_of_dominated_convergence
    (l := (atTop : Filter ℝ))
    (μ := volume.restrict {z : ℂ | 0 ≤ z.im})
    (F := fun r : ℝ => fun z => ‖suzukiGammaShiftReflectionError rho r c tau z‖)
    (f := fun _ => (0 : ℝ))
    (fun z => (C / 4) * ‖suzukiSmoothSpectralBoundaryHeat c tau z‖) ?_ ?_
    (((integrable_suzukiSmoothSpectralBoundaryHeat htau c).norm.const_mul (C / 4)).integrableOn) ?_
  · simpa only [integral_zero] using hD
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact (reflection_error_measurable rho hr c tau).norm
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    filter_upwards [ae_restrict_mem hm] with z hz
    simpa only [Real.norm_eq_abs, abs_norm] using reflection_error_domination rho hbound hr c tau hz
  · filter_upwards [ae_restrict_mem hm] with z hz
    simpa only [norm_zero] using (reflection_error_tendsto rho c tau hz).norm

/-- The complete complex reflected completion integral vanishes as
smoothing grows, as a consequence of the stronger L1 estimate. -/
theorem tendsto_integral_suzukiGammaShiftReflectionError (rho : NontrivialZetaZero)
    {tau : ℝ} (htau : 0 < tau) (c : ℝ) :
    Tendsto (fun r : ℝ => ∫ z in {z : ℂ | 0 ≤ z.im},
      suzukiGammaShiftReflectionError rho r c tau z) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (tendsto_integral_norm_suzukiGammaShiftReflectionError rho htau c)
  filter_upwards with r
  exact norm_integral_le_integral_norm _

/-- The same completion error vanishes for arbitrary moving spatial
cutoffs inside the upper half-plane. The L1 control is global, so no
interchange of smoothing and expanding-region limits is required here. -/
theorem tendsto_setIntegral_suzukiGammaShiftReflectionError (rho : NontrivialZetaZero)
    {tau : ℝ} (htau : 0 < tau) (c : ℝ) (K : ℝ → Set ℂ)
    (hK : ∀ r : ℝ, K r ⊆ {z : ℂ | 0 ≤ z.im}) :
    Tendsto (fun r : ℝ => ∫ z in K r,
      suzukiGammaShiftReflectionError rho r c tau z) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (tendsto_integral_norm_suzukiGammaShiftReflectionError rho htau c)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  apply (norm_integral_le_integral_norm _).trans
  exact setIntegral_mono_set (integrableOn_suzukiGammaShiftReflectionError rho hr htau c).norm
    (ae_of_all _ fun z => norm_nonneg _) (ae_of_all _ fun _ hz => hK r hz)

end
end RiemannGaussian
