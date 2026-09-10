/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiGammaArithmeticCutoff
import RiemannGaussian.AnalyticHalfPlaneDerivative

/-!
# Removing the entire safe half-plane from the arithmetic source

The actual carrier's signed phase in the known zero-free half-plane
controls its derivative by the existing Cayley--Schwarz estimate. This
gives uniform decay of the full smoothed source at a fixed positive
distance from the zero strip, before any arithmetic term is discarded.
The original reflection weight and Gaussian then give global L1 decay.
-/

open Complex Filter MeasureTheory Metric Set Topology
namespace RiemannGaussian
noncomputable section

private lemma safe_ball {delta : ℝ} {z w : ℂ}
    (hz : 1 / 2 + delta ≤ z.im) (hw : w ∈ ball z delta) : 1 / 2 ≤ w.im := by
  have hn : ‖w - z‖ < delta := mem_ball_iff_norm.mp hw
  have hi := (abs_le.mp (Complex.abs_im_le_norm (w - z))).1
  simp only [sub_im] at hi
  linarith

/-- In every closed half-plane a fixed distance beyond the zero strip,
the actual carrier derivative is controlled by its signed imaginary
part. Its complex value remains available in the separate exact source. -/
theorem norm_deriv_suzukiXiZeroCarrier_le_im_safe {delta : ℝ} (hdelta : 0 < delta)
    {z : ℂ} (hz : 1 / 2 + delta ≤ z.im) :
    ‖deriv suzukiXiZeroCarrier z‖ ≤ 2 * (suzukiXiZeroCarrier z).im / delta := by
  have hd : DifferentiableOn ℂ (fun w => -suzukiXiZeroCarrier w) (ball z delta) := by
    intro w hw
    exact (analyticAt_suzukiXiZeroCarrier_of_half_le_im (safe_ball hz hw)).differentiableAt.neg.differentiableWithinAt
  have h := norm_deriv_le_of_im_nonpos_on_ball hdelta hd (fun w hw => by
    have hs := norm_suzukiXiZeroCarrier_sq_le_im_of_half_le_im (safe_ball hz hw)
    simp only [neg_im]
    nlinarith [sq_nonneg ‖suzukiXiZeroCarrier w‖])
  have hq := (analyticAt_suzukiXiZeroCarrier_of_half_le_im (by linarith : 1 / 2 ≤ z.im)).differentiableAt
  have hneg : deriv (fun w => -suzukiXiZeroCarrier w) z = -deriv suzukiXiZeroCarrier z := by
    convert! hq.hasDerivAt.neg.deriv using 1
  rw [hneg, norm_neg] at h
  simpa only [neg_im, neg_neg] using h

/-- The actual safe-half-plane source has this exact radial derivative
formula, retaining the full complex phase and normalization. -/
theorem suzukiXiSmoothCarrierSource_eq_radial_deriv_safe {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : 1 / 2 ≤ z.im) :
    suzukiXiSmoothCarrierSource r z =
      -2 * I * (r : ℂ) ^ 2 * suzukiXiZeroCarrier z ^ 2 *
        starRingEnd ℂ (deriv suzukiXiZeroCarrier z) /
          ((1 + r ^ 2 * normSq (suzukiXiZeroCarrier z) : ℝ) : ℂ) ^ 2 := by
  have hE := suzukiXiEValue_ne_zero_of_half_le_im hz
  have he : suzukiXiSmoothCarrier r =ᶠ[𝓝 z]
      fun w => complexSmoothQuotient r (suzukiXiZeroCarrier w) 1 := by
    filter_upwards [(analyticAt_suzukiXiEValue z).continuousAt.eventually_ne hE] with w hw
    exact suzukiXiSmoothCarrier_eq_regular_chart r hw
  rw [← complexCauchyGreenSource_suzukiXiSmoothCarrier hr]
  have heq : complexCauchyGreenSource (suzukiXiSmoothCarrier r) z =
      complexCauchyGreenSource (fun w => complexSmoothQuotient r (suzukiXiZeroCarrier w) 1) z := by
    unfold complexCauchyGreenSource
    rw [he.fderiv_eq]
  rw [heq, complexCauchyGreenSource_complexSmoothQuotient hr
    (analyticAt_suzukiXiZeroCarrier_of_half_le_im hz).differentiableAt
    (differentiableAt_const (1 : ℂ)) (Or.inr one_ne_zero)]
  simp only [deriv_const, mul_zero, one_mul, zero_sub, map_neg, normSq_one]
  ring

private lemma radial_cubic_bound {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    r ^ 2 * a ^ 3 / (1 + r ^ 2 * a ^ 2) ^ 2 ≤ 1 / r := by
  have hx : 0 ≤ r * a := mul_nonneg hr.le ha
  have hl : r * a ≤ 1 + (r * a) ^ 2 := by nlinarith [sq_nonneg (r * a - 1)]
  have hp := mul_le_mul (show (r * a) ^ 2 ≤ 1 + (r * a) ^ 2 by linarith)
    hl hx (by positivity : 0 ≤ 1 + (r * a) ^ 2)
  apply (div_le_div_iff₀ (by positivity) hr).mpr
  nlinarith [hp]

/-- Smoothing kills the entire actual source uniformly beyond any
fixed positive distance from the known zero strip. This bound uses its
signed carrier phase before taking a norm. -/
theorem norm_suzukiXiSmoothCarrierSource_le_safe {r delta : ℝ}
    (hr : 0 < r) (hdelta : 0 < delta) {z : ℂ} (hz : 1 / 2 + delta ≤ z.im) :
    ‖suzukiXiSmoothCarrierSource r z‖ ≤ 4 / (r * delta) := by
  have hd := (norm_deriv_suzukiXiZeroCarrier_le_im_safe hdelta hz).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Complex.im_le_norm (suzukiXiZeroCarrier z)) (by norm_num)) hdelta.le)
  rw [suzukiXiSmoothCarrierSource_eq_radial_deriv_safe hr (by linarith)]
  simp only [norm_div, norm_mul, norm_neg, norm_pow, norm_conj, norm_I,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_one,
    normSq_eq_norm_sq]
  calc
    _ ≤ 2 * r ^ 2 * ‖suzukiXiZeroCarrier z‖ ^ 2 *
        (2 * ‖suzukiXiZeroCarrier z‖ / delta) /
        (1 + r ^ 2 * ‖suzukiXiZeroCarrier z‖ ^ 2) ^ 2 := by gcongr
    _ = (4 / delta) * (r ^ 2 * ‖suzukiXiZeroCarrier z‖ ^ 3 /
        (1 + r ^ 2 * ‖suzukiXiZeroCarrier z‖ ^ 2) ^ 2) := by ring
    _ ≤ (4 / delta) * (1 / r) :=
      mul_le_mul_of_nonneg_left (radial_cubic_bound hr (norm_nonneg _)) (by positivity)
    _ = _ := by ring

/-- The remaining normalized arithmetic contribution inherits uniform
decay on the safe half-plane, with its actual denominator unchanged. -/
theorem norm_suzukiGammaShiftArithmeticSource_le_safe {r delta : ℝ}
    (hr : 0 < r) (hdelta : 0 < delta) {z : ℂ} (hz : 1 / 2 + delta ≤ z.im) :
    ‖suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z)‖ ≤
      4 / (r * delta) + 1 / (4 * r ^ 2) := by
  have hs : 0 < (suzukiArithmeticZetaArgument z).re := by
    rw [suzukiArithmeticZetaArgument_re]
    linarith
  have he := norm_suzukiXiSmoothCarrierSource_gammaShift_error_le hr hs (1 : ℂ)
  simp only [one_mul, norm_one] at he
  have hb := norm_suzukiXiSmoothCarrierSource_le_safe hr hdelta hz
  have ht := norm_sub_le (suzukiXiSmoothCarrierSource r z)
    (suzukiXiSmoothCarrierSource r z - suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z))
  rw [sub_sub_cancel] at ht
  exact ht.trans (add_le_add hb he)

/-- The full complex reflection weight has a uniform bound a positive
distance beyond both nodes. The distance is measured from the known strip. -/
theorem norm_suzukiXiReflectionWeight_le_safe (rho : NontrivialZetaZero)
    {delta : ℝ} (hdelta : 0 < delta) {z : ℂ} (hz : 1 / 2 + delta ≤ z.im) :
    ‖suzukiXiReflectionWeight rho z‖ ≤ 4 * (zetaSpectralCoordinate rho.1).im ^ 2 / delta ^ 4 := by
  let a := zetaSpectralCoordinate rho.1
  have ha := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  have hd : delta ≤ ‖z - a‖ := by
    have hi := (Complex.im_le_norm (z - a))
    simp only [sub_im] at hi
    dsimp [a] at *
    linarith [le_abs_self (zetaSpectralCoordinate rho.1).im]
  have he : delta ≤ ‖z - starRingEnd ℂ a‖ := by
    have hi := Complex.im_le_norm (z - starRingEnd ℂ a)
    simp only [sub_im, conj_im] at hi
    dsimp [a] at *
    linarith [neg_le_abs (zetaSpectralCoordinate rho.1).im]
  have hza : z ≠ a := sub_ne_zero.mp (norm_pos_iff.mp (hdelta.trans_le hd))
  have hzb : z ≠ starRingEnd ℂ a := sub_ne_zero.mp (norm_pos_iff.mp (hdelta.trans_le he))
  rw [suzukiXiReflectionWeight_eq_quartic rho hza hzb, norm_div, norm_mul, norm_pow,
    norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  norm_num only [norm_ofNat]
  calc
    _ ≤ 4 * (zetaSpectralCoordinate rho.1).im ^ 2 / (delta * delta) ^ 2 := by gcongr
    _ = _ := by ring

/-- The full reflected normalized arithmetic density admits an
integrable Gaussian majorant on every safe half-plane, with an explicit
smoothing rate and no restriction on the spatial cutoff. -/
theorem norm_suzukiGammaShiftWeightedArithmeticSource_le_safe
    (rho : NontrivialZetaZero) {r delta : ℝ} (hr : 0 < r) (hdelta : 0 < delta)
    (c tau : ℝ) {z : ℂ} (hz : 1 / 2 + delta ≤ z.im) :
    ‖suzukiGammaShiftWeightedArithmeticSource rho r c tau z‖ ≤
      (4 * (zetaSpectralCoordinate rho.1).im ^ 2 / delta ^ 4) *
        (4 / (r * delta) + 1 / (4 * r ^ 2)) * ‖suzukiSmoothSpectralBoundaryHeat c tau z‖ := by
  unfold suzukiGammaShiftWeightedArithmeticSource
  simp only [norm_mul]
  calc
    _ ≤ (4 * (zetaSpectralCoordinate rho.1).im ^ 2 / delta ^ 4) *
        ‖suzukiSmoothSpectralBoundaryHeat c tau z‖ *
        (4 / (r * delta) + 1 / (4 * r ^ 2)) := by
      gcongr
      · exact norm_suzukiXiReflectionWeight_le_safe rho hdelta hz
      · exact norm_suzukiGammaShiftArithmeticSource_le_safe hr hdelta hz
    _ = _ := by ring

private lemma integrable_weighted_source_safe (rho : NontrivialZetaZero)
    {r tau delta : ℝ} (hr : 0 < r) (htau : 0 < tau) (hdelta : 0 < delta) (c : ℝ) :
    IntegrableOn (fun z => suzukiXiReflectionWeight rho z * suzukiSmoothSpectralBoundaryHeat c tau z *
      suzukiXiSmoothCarrierSource r z) {z : ℂ | 1 / 2 + delta ≤ z.im} := by
  have hW : Measurable (suzukiXiReflectionWeight rho) := by
    unfold suzukiXiReflectionWeight suzukiXiReflectionCauchyDifference
    fun_prop
  have hB := (differentiable_suzukiSmoothSpectralBoundaryHeat c tau).continuous.measurable
  have hV := (continuous_suzukiXiSmoothCarrierSource hr).measurable
  have hm := ((hW.mul hB).mul hV).aestronglyMeasurable (μ := volume)
  have hmajor := (((integrable_suzukiSmoothSpectralBoundaryHeat htau c).norm.const_mul
    ((4 * (zetaSpectralCoordinate rho.1).im ^ 2 / delta ^ 4) * (4 / (r * delta))))).integrableOn
      (s := {z : ℂ | 1 / 2 + delta ≤ z.im})
  refine hmajor.mono' (hm.mono_measure Measure.restrict_le_self) ?_
  filter_upwards [ae_restrict_mem (isClosed_le continuous_const Complex.continuous_im).measurableSet] with z hz
  simp only [norm_mul]
  calc
    _ ≤ (4 * (zetaSpectralCoordinate rho.1).im ^ 2 / delta ^ 4) *
        ‖suzukiSmoothSpectralBoundaryHeat c tau z‖ * (4 / (r * delta)) := by
      gcongr
      · exact norm_suzukiXiReflectionWeight_le_safe rho hdelta hz
      · exact norm_suzukiXiSmoothCarrierSource_le_safe hr hdelta hz
    _ = _ := by ring

/-- The normalized arithmetic density is genuinely integrable over
the whole safe half-plane at fixed positive heat time and smoothing. -/
theorem integrableOn_suzukiGammaShiftWeightedArithmeticSource_safe
    (rho : NontrivialZetaZero) {r tau delta : ℝ} (hr : 1 ≤ r)
    (htau : 0 < tau) (hdelta : 0 < delta) (c : ℝ) :
    IntegrableOn (suzukiGammaShiftWeightedArithmeticSource rho r c tau)
      {z : ℂ | 1 / 2 + delta ≤ z.im} := by
  have hV := integrable_weighted_source_safe rho (lt_of_lt_of_le zero_lt_one hr) htau hdelta c
  have hE := (integrableOn_suzukiGammaShiftReflectionError rho hr htau c).mono_set
    (show {z : ℂ | 1 / 2 + delta ≤ z.im} ⊆ {z : ℂ | 0 ≤ z.im} from
      fun _ hz => (show (0 : ℝ) ≤ 1 / 2 + delta by linarith).trans hz)
  convert! hV.sub hE using 1
  funext z
  simp only [Pi.sub_apply, suzukiGammaShiftWeightedArithmeticSource, suzukiGammaShiftReflectionError]
  ring

/-- A quantitative bound for the entire safe-half-plane L1 mass of the
remaining arithmetic density. The Gaussian norm integral is global and finite. -/
theorem integral_norm_suzukiGammaShiftWeightedArithmeticSource_safe_le
    (rho : NontrivialZetaZero) {r tau delta : ℝ} (hr : 1 ≤ r)
    (htau : 0 < tau) (hdelta : 0 < delta) (c : ℝ) :
    (∫ z in {z : ℂ | 1 / 2 + delta ≤ z.im},
      ‖suzukiGammaShiftWeightedArithmeticSource rho r c tau z‖) ≤
        ((4 * (zetaSpectralCoordinate rho.1).im ^ 2 / delta ^ 4) *
          (4 / (r * delta) + 1 / (4 * r ^ 2))) *
            ∫ z : ℂ, ‖suzukiSmoothSpectralBoundaryHeat c tau z‖ := by
  let C := (4 * (zetaSpectralCoordinate rho.1).im ^ 2 / delta ^ 4) *
    (4 / (r * delta) + 1 / (4 * r ^ 2))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hB := (integrable_suzukiSmoothSpectralBoundaryHeat htau c).norm
  calc
    _ ≤ ∫ z in {z : ℂ | 1 / 2 + delta ≤ z.im}, C * ‖suzukiSmoothSpectralBoundaryHeat c tau z‖ := by
      apply integral_mono_ae
        (integrableOn_suzukiGammaShiftWeightedArithmeticSource_safe rho hr htau hdelta c).norm
        (hB.const_mul C).integrableOn
      filter_upwards [ae_restrict_mem (isClosed_le continuous_const Complex.continuous_im).measurableSet] with z hz
      exact norm_suzukiGammaShiftWeightedArithmeticSource_le_safe rho
        (lt_of_lt_of_le zero_lt_one hr) hdelta c tau hz
    _ = C * ∫ z in {z : ℂ | 1 / 2 + delta ≤ z.im}, ‖suzukiSmoothSpectralBoundaryHeat c tau z‖ :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hB (ae_of_all _ fun _ => norm_nonneg _)) hC

/-- The entire safe-half-plane arithmetic contribution tends to zero
in L1, independently of the hypothesis of a right-half zero. -/
theorem tendsto_integral_norm_suzukiGammaShiftWeightedArithmeticSource_safe
    (rho : NontrivialZetaZero) {tau delta : ℝ} (htau : 0 < tau)
    (hdelta : 0 < delta) (c : ℝ) :
    Tendsto (fun r : ℝ => ∫ z in {z : ℂ | 1 / 2 + delta ≤ z.im},
      ‖suzukiGammaShiftWeightedArithmeticSource rho r c tau z‖) atTop (𝓝 0) := by
  have h1 : Tendsto (fun r : ℝ => (4 / delta) / r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h2 : Tendsto (fun r : ℝ => 1 / (4 * r ^ 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop (by norm_num))
  have hb := ((h1.add h2).const_mul (4 * (zetaSpectralCoordinate rho.1).im ^ 2 / delta ^ 4)).mul_const
    (∫ z : ℂ, ‖suzukiSmoothSpectralBoundaryHeat c tau z‖)
  simp only [add_zero, mul_zero, zero_mul] at hb
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _) _ hb
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  convert integral_norm_suzukiGammaShiftWeightedArithmeticSource_safe_le rho hr htau hdelta c using 1
  ring

/-- Arbitrary moving cutoffs inside the entire safe half-plane inherit
the same arithmetic decay, without a cutoff-dependent majorant. -/
theorem tendsto_setIntegral_suzukiGammaShiftWeightedArithmeticSource_safe
    (rho : NontrivialZetaZero) {tau delta : ℝ} (htau : 0 < tau)
    (hdelta : 0 < delta) (c : ℝ) (K : ℝ → Set ℂ)
    (hK : ∀ r, K r ⊆ {z : ℂ | 1 / 2 + delta ≤ z.im}) :
    Tendsto (fun r : ℝ => ∫ z in K r, suzukiGammaShiftWeightedArithmeticSource rho r c tau z)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (tendsto_integral_norm_suzukiGammaShiftWeightedArithmeticSource_safe rho htau hdelta c)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  apply (norm_integral_le_integral_norm _).trans
  exact setIntegral_mono_set
    (integrableOn_suzukiGammaShiftWeightedArithmeticSource_safe rho hr htau hdelta c).norm
    (ae_of_all _ fun _ => norm_nonneg _) (ae_of_all _ fun _ hz => hK r hz)

open scoped Interval in
/-- All of the original reflected source remains in the bounded
vertical band after the independently negligible safe half-plane is
removed, even with simultaneous spatial and smoothing growth. -/
theorem tendsto_suzukiGammaShiftWeightedArithmeticSource_moving_band
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) {tau delta : ℝ}
    (htau : 0 < tau) (hdelta : 0 < delta) (c : ℝ) (R : ℝ → ℝ)
    (hR : ∀ r, 1 ≤ R r) (hc : ∀ r, 2 * |c| ≤ R r)
    (hRe : ∀ r, 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R r) :
    Tendsto (fun r : ℝ => ∫ z in ([[ -R r,R r]] ×ℂ [[0,R r]]) \ {z : ℂ | 1 / 2 + delta ≤ z.im},
      suzukiGammaShiftWeightedArithmeticSource rho r c tau z) atTop
      (𝓝 ((2 * Real.pi * I) * ((analyticZetaZeroMultiplicity rho : ℂ)⁻¹ *
        suzukiSmoothSpectralBoundaryHeat c tau (starRingEnd ℂ (zetaSpectralCoordinate rho.1))))) := by
  let K : ℝ → Set ℂ := fun r => [[-R r,R r]] ×ℂ [[0,R r]]
  let T : Set ℂ := {z : ℂ | 1 / 2 + delta ≤ z.im}
  have hT : MeasurableSet T := (isClosed_le continuous_const Complex.continuous_im).measurableSet
  have hfull := tendsto_suzukiGammaShiftWeightedArithmeticSource_moving_rectangle rho hzero htau c R hR hc hRe
  have htail := tendsto_setIntegral_suzukiGammaShiftWeightedArithmeticSource_safe rho htau hdelta c
    (fun r => K r ∩ T) (fun _ => inter_subset_right)
  have h := hfull.sub htail
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hupper : K r ⊆ {z : ℂ | 0 ≤ z.im} := by
    intro z hz
    have hy := hz.2
    rw [uIcc_of_le (show 0 ≤ R r by linarith [hR r])] at hy
    exact hy.1
  have hA := integrableOn_suzukiGammaShiftWeightedArithmeticSource rho hr htau c
    (show IsCompact (K r) from isCompact_uIcc.reProdIm isCompact_uIcc) hupper
  have he := integral_inter_add_sdiff hT hA
  change (∫ z in K r, suzukiGammaShiftWeightedArithmeticSource rho r c tau z) -
      (∫ z in K r ∩ T, suzukiGammaShiftWeightedArithmeticSource rho r c tau z) =
      (∫ z in K r \ T, suzukiGammaShiftWeightedArithmeticSource rho r c tau z)
  rw [← he]
  ring

end
end RiemannGaussian
