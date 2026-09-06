import RiemannGaussian.EtaLogColourPrimitive

/-!
# Gaussian integration of the signed Wallis colour remainder

The actual cumulative eta colour approaches its Wallis constant with an
exponential error. Integration by parts retains that signed remainder
against the Gaussian derivative, with genuine infinite-time integrability.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The real displacement derivative of the normalized eta Gaussian. -/
def etaNormalizedHeatKernelDeriv (h r : ℝ) : ℝ :=
  -r / (2 * h ^ 2) * etaNormalizedHeatKernel h r

/-- Differentiating the literal normalized Gaussian retains its amplitude. -/
theorem hasDerivAt_etaNormalizedHeatKernel {h : ℝ} (hh : 0 < h) (r : ℝ) :
    HasDerivAt (etaNormalizedHeatKernel h) (etaNormalizedHeatKernelDeriv h r) r := by
  have he : etaNormalizedHeatKernel h =
      (fun x ↦ Real.exp (-(1 / (4 * h ^ 2)) * x ^ 2) / (2 * Real.sqrt Real.pi * h)) :=
    funext (etaNormalizedHeatKernel_eq_quadratic hh)
  unfold etaNormalizedHeatKernelDeriv
  rw [he]
  convert ((((hasDerivAt_id r).pow 2).const_mul (-(1 / (4 * h ^ 2)))).exp.div_const
    (2 * Real.sqrt Real.pi * h)) using 1 <;>
    first | rfl | (simp only [id_eq, Pi.pow_apply]; ring_nf)

/-- Translating the Gaussian retains the same displacement derivative. -/
theorem hasDerivAt_etaNormalizedHeatKernel_sub {h : ℝ} (hh : 0 < h) (c w : ℝ) :
    HasDerivAt (fun x ↦ etaNormalizedHeatKernel h (x - c))
      (etaNormalizedHeatKernelDeriv h (w - c)) w := by
  simpa only [mul_one, Function.comp_def, id_eq] using (hasDerivAt_etaNormalizedHeatKernel hh (w - c)).comp w
    ((hasDerivAt_id w).sub_const c)

/-- The translated Gaussian derivative has an explicit polynomial envelope
on nonnegative time and center. -/
theorem abs_etaNormalizedHeatKernelDeriv_sub_le {h c w : ℝ} (hh : 0 < h)
    (hc : 0 ≤ c) (hw : 0 ≤ w) :
    |etaNormalizedHeatKernelDeriv h (w - c)| ≤ (w + c) / (4 * Real.sqrt Real.pi * h ^ 3) := by
  have hd : |w - c| ≤ w + c := by rw [abs_le]; constructor <;> linarith
  unfold etaNormalizedHeatKernelDeriv
  rw [abs_mul, abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2 * h ^ 2),
    abs_of_pos (etaNormalizedHeatKernel_pos hh _)]
  calc
    _ ≤ ((w + c) / (2 * h ^ 2)) * (1 / (2 * Real.sqrt Real.pi * h)) :=
      mul_le_mul (div_le_div_of_nonneg_right hd (by positivity)) (etaNormalizedHeatKernel_le hh _)
        (etaNormalizedHeatKernel_pos hh _).le (by positivity)
    _ = _ := by ring

/-- The signed Gaussian correction from the actual colour primitive. -/
def pairedEtaGaussianColourCorrection (h c : ℝ) : ℝ :=
  ∫ w in Ioi (0 : ℝ), pairedEtaLogColourRemainder w * etaNormalizedHeatKernelDeriv h (w - c)

/-- The elementary exponential moment that controls the colour correction. -/
theorem integrableOn_etaGaussianColourEnvelope (c : ℝ) :
    IntegrableOn (fun w : ℝ ↦ (w + c) * Real.exp (-w)) (Ioi 0) := by
  have hi₀ : IntegrableOn (fun w : ℝ ↦ Real.exp (-w)) (Ioi 0) := by
    simpa using integrableOn_pow_mul_exp_neg_mul_Ioi_zero_nat 0 (by norm_num : (0 : ℝ) < 1)
  have hi₁ : IntegrableOn (fun w : ℝ ↦ w * Real.exp (-w)) (Ioi 0) := by
    simpa using integrableOn_pow_mul_exp_neg_mul_Ioi_zero_nat 1 (by norm_num : (0 : ℝ) < 1)
  have he : (fun w : ℝ ↦ (w + c) * Real.exp (-w)) =
      (fun w ↦ w * Real.exp (-w) + c * Real.exp (-w)) := by funext w; ring
  rw [he]
  exact hi₁.add (hi₀.const_mul c)

/-- The Gaussian colour envelope has the exact elementary mass `1+c`. -/
theorem integral_Ioi_etaGaussianColourEnvelope (c : ℝ) :
    (∫ w in Ioi (0 : ℝ), (w + c) * Real.exp (-w)) = 1 + c := by
  have hi₀ : IntegrableOn (fun w : ℝ ↦ Real.exp (-w)) (Ioi 0) := by
    simpa using integrableOn_pow_mul_exp_neg_mul_Ioi_zero_nat 0 (by norm_num : (0 : ℝ) < 1)
  have hi₁ : IntegrableOn (fun w : ℝ ↦ w * Real.exp (-w)) (Ioi 0) := by
    simpa using integrableOn_pow_mul_exp_neg_mul_Ioi_zero_nat 1 (by norm_num : (0 : ℝ) < 1)
  have h₀ : (∫ w in Ioi (0 : ℝ), Real.exp (-w)) = 1 := by
    simpa [positiveHalfLineRealLogLaplaceMoment] using
      positiveHalfLineRealLogLaplaceMoment_eq_factorial 0 (by norm_num : (0 : ℝ) < 1)
  have h₁ : (∫ w in Ioi (0 : ℝ), w * Real.exp (-w)) = 1 := by
    simpa [positiveHalfLineRealLogLaplaceMoment] using
      positiveHalfLineRealLogLaplaceMoment_eq_factorial 1 (by norm_num : (0 : ℝ) < 1)
  simp_rw [add_mul]
  rw [integral_add hi₁ (hi₀.const_mul c), integral_const_mul, h₀, h₁, mul_one]

/-- The actual signed integrand is dominated by the exponential colour error. -/
theorem abs_pairedEtaGaussianColourCorrection_integrand_le {h c w : ℝ}
    (hh : 0 < h) (hc : 0 ≤ c) (hw : 0 ≤ w) :
    |pairedEtaLogColourRemainder w * etaNormalizedHeatKernelDeriv h (w - c)| ≤
      (9 / (4 * Real.sqrt Real.pi * h ^ 3)) * ((w + c) * Real.exp (-w)) := by
  rw [abs_mul]
  calc
    _ ≤ (9 * Real.exp (-w)) * ((w + c) / (4 * Real.sqrt Real.pi * h ^ 3)) :=
      mul_le_mul (pairedEtaLogColourPrimitive_wallis_error_le hw)
        (abs_etaNormalizedHeatKernelDeriv_sub_le hh hc hw) (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- The colour correction is absolutely convergent over the complete positive half-line. -/
theorem integrableOn_pairedEtaGaussianColourCorrection {h c : ℝ} (hh : 0 < h) (hc : 0 ≤ c) :
    IntegrableOn (fun w ↦ pairedEtaLogColourRemainder w * etaNormalizedHeatKernelDeriv h (w - c)) (Ioi 0) := by
  apply ((integrableOn_etaGaussianColourEnvelope c).const_mul
    (9 / (4 * Real.sqrt Real.pi * h ^ 3))).mono'
  · have hm : Continuous (fun w ↦ pairedEtaLogColourRemainder w * etaNormalizedHeatKernelDeriv h (w - c)) := by
      apply continuous_pairedEtaLogColourRemainder.mul
      unfold etaNormalizedHeatKernelDeriv etaNormalizedHeatKernel
      fun_prop
    exact hm.measurable.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    simpa only [Real.norm_eq_abs] using abs_pairedEtaGaussianColourCorrection_integrand_le hh hc hw.le

/-- The actual signed Gaussian colour correction has an inverse-cubic-width bound. -/
theorem pairedEtaGaussianColourCorrection_abs_le {h c : ℝ} (hh : 0 < h) (hc : 0 ≤ c) :
    |pairedEtaGaussianColourCorrection h c| ≤ 9 * (1 + c) / (4 * Real.sqrt Real.pi * h ^ 3) := by
  have hb := norm_integral_le_of_norm_le
    ((integrableOn_etaGaussianColourEnvelope c).const_mul (9 / (4 * Real.sqrt Real.pi * h ^ 3)))
    (f := fun w ↦ pairedEtaLogColourRemainder w * etaNormalizedHeatKernelDeriv h (w - c)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      simpa only [Real.norm_eq_abs] using abs_pairedEtaGaussianColourCorrection_integrand_le hh hc hw.le)
  rw [integral_const_mul, integral_Ioi_etaGaussianColourEnvelope] at hb
  simpa only [pairedEtaGaussianColourCorrection, Real.norm_eq_abs, mul_div_assoc, div_mul_eq_mul_div] using hb

/-- Exact finite integration by parts retains the signed colour remainder
and the terminal boundary, before passing to infinite time. -/
theorem integral_etaSignedColour_gaussian_eq_remainder {h : ℝ} (hh : 0 < h) (c b : ℝ) :
    (∫ w in (0 : ℝ)..b, pairedEtaLogSignedColour w * etaNormalizedHeatKernel h (w - c)) =
      pairedEtaLogColourRemainder b * etaNormalizedHeatKernel h (b - c) +
        Real.log (Real.pi / 2) * etaNormalizedHeatKernel h c -
        ∫ w in (0 : ℝ)..b, pairedEtaLogColourRemainder w * etaNormalizedHeatKernelDeriv h (w - c) := by
  let W : ℝ → ℝ := fun w ↦ etaNormalizedHeatKernel h (w - c)
  have hW : AbsolutelyContinuousOnInterval W 0 b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    unfold W etaNormalizedHeatKernel
    fun_prop
  have hB : AbsolutelyContinuousOnInterval pairedEtaLogColourRemainder 0 b :=
    (absolutelyContinuousOnInterval_pairedEtaLogColourPrimitive b).sub
      (contDiff_const.contDiffOn.absolutelyContinuousOnInterval)
  have hleft : (∫ w in (0 : ℝ)..b, W w * deriv pairedEtaLogColourRemainder w) =
      ∫ w in (0 : ℝ)..b, pairedEtaLogSignedColour w * etaNormalizedHeatKernel h (w - c) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(intervalIntegrable_pairedEtaLogSignedColour 0 b).ae_hasDerivAt_integral] with w hw hwb
    have hd : HasDerivAt pairedEtaLogColourRemainder (pairedEtaLogSignedColour w) w :=
      (hw (uIoc_subset_uIcc hwb) 0 (by simp)).sub_const _
    rw [hd.deriv]
    exact mul_comm _ _
  have hright : (∫ w in (0 : ℝ)..b, deriv W w * pairedEtaLogColourRemainder w) =
      ∫ w in (0 : ℝ)..b, pairedEtaLogColourRemainder w * etaNormalizedHeatKernelDeriv h (w - c) := by
    apply intervalIntegral.integral_congr
    intro w _
    change deriv (fun x ↦ etaNormalizedHeatKernel h (x - c)) w * pairedEtaLogColourRemainder w = _
    rw [(hasDerivAt_etaNormalizedHeatKernel_sub hh c w).deriv]
    exact mul_comm _ _
  have hp := hW.integral_mul_deriv_eq_deriv_mul hB
  rw [hleft, hright] at hp
  simpa only [W, pairedEtaLogColourRemainder, pairedEtaLogColourPrimitive,
    intervalIntegral.integral_same, zero_sub, etaNormalizedHeatKernel_neg, mul_neg, neg_mul,
    sub_neg_eq_add, mul_comm] using hp

/-- The signed colour times the translated Gaussian is integrable on the full line. -/
theorem integrable_etaSignedColour_gaussian {h : ℝ} (hh : 0 < h) (c : ℝ) :
    Integrable (fun w ↦ pairedEtaLogSignedColour w * etaNormalizedHeatKernel h (w - c)) := by
  simpa only [mul_comm] using ((integrable_etaNormalizedHeatKernel hh).comp_sub_right c).mul_bdd
    measurable_pairedEtaLogSignedColour.aestronglyMeasurable
    (Eventually.of_forall fun w ↦ show ‖pairedEtaLogSignedColour w‖ ≤ (1 : ℝ) from by
      simp only [Real.norm_eq_abs, abs_pairedEtaLogSignedColour, le_refl])

/-- The finite terminal colour boundary tends to zero, using its actual
exponential remainder and the Gaussian amplitude bound. -/
theorem pairedEtaGaussianColour_boundary_tendsto {h : ℝ} (hh : 0 < h) (c : ℝ) :
    Tendsto (fun b : ℝ ↦ pairedEtaLogColourRemainder b * etaNormalizedHeatKernel h (b - c))
      atTop (𝓝 0) := by
  have hd : Tendsto (fun b : ℝ ↦ 9 * Real.exp (-b) / (2 * Real.sqrt Real.pi * h)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div] using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul 9 |>.div_const
      (2 * Real.sqrt Real.pi * h)
  apply squeeze_zero_norm' _ hd
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with b hb
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (etaNormalizedHeatKernel_pos hh _)]
  calc
    _ ≤ (9 * Real.exp (-b)) * (1 / (2 * Real.sqrt Real.pi * h)) :=
      mul_le_mul (pairedEtaLogColourPrimitive_wallis_error_le hb) (etaNormalizedHeatKernel_le hh _)
        (etaNormalizedHeatKernel_pos hh _).le (by positivity)
    _ = _ := by ring

/-- Passing the exact colour integration by parts to the complete positive
half-line retains a genuinely integrable signed correction. -/
theorem integral_Ioi_etaSignedColour_gaussian_eq_remainder {h c : ℝ} (hh : 0 < h) (hc : 0 ≤ c) :
    (∫ w in Ioi (0 : ℝ), pairedEtaLogSignedColour w * etaNormalizedHeatKernel h (w - c)) =
      Real.log (Real.pi / 2) * etaNormalizedHeatKernel h c - pairedEtaGaussianColourCorrection h c := by
  have hleft := intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
    (integrable_etaSignedColour_gaussian hh c).integrableOn tendsto_id
  have hright := intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
    (integrableOn_pairedEtaGaussianColourCorrection hh hc) tendsto_id
  simp only [id_eq] at hleft hright
  have ht := ((pairedEtaGaussianColour_boundary_tendsto hh c).add
    (tendsto_const_nhds (x := Real.log (Real.pi / 2) * etaNormalizedHeatKernel h c))).sub hright
  simp only [zero_add] at ht
  have he : (fun b : ℝ ↦ ∫ w in (0 : ℝ)..b, pairedEtaLogSignedColour w * etaNormalizedHeatKernel h (w - c)) =
      (fun b ↦ pairedEtaLogColourRemainder b * etaNormalizedHeatKernel h (b - c) +
        Real.log (Real.pi / 2) * etaNormalizedHeatKernel h c -
        ∫ w in (0 : ℝ)..b, pairedEtaLogColourRemainder w * etaNormalizedHeatKernelDeriv h (w - c)) :=
    funext (integral_etaSignedColour_gaussian_eq_remainder hh c)
  rw [he] at hleft
  exact tendsto_nhds_unique hleft ht

/-- The actual gap mass has an exact Wallis endpoint decomposition,
with the full signed Gaussian colour correction retained. -/
theorem pairedEtaGaussianGapMass_eq_colourCorrection {h c : ℝ} (hh : 0 < h) (hc : 0 ≤ c) :
    pairedEtaGaussianGapMass h c = 1 / 4 +
      (∫ w in (0 : ℝ)..c, etaNormalizedHeatKernel h w) / 2 -
      Real.log (Real.pi / 2) * etaNormalizedHeatKernel h c / 2 + pairedEtaGaussianColourCorrection h c / 2 := by
  have hi := (integrable_etaNormalizedHeatKernel hh).comp_sub_right c
  have hiC := integrable_etaSignedColour_gaussian hh c
  have hiS : Integrable (fun w ↦ pairedEtaLogSignedColour w * etaNormalizedHeatKernel h (w - c))
      pairedEtaLogMeasure := Integrable.mono_measure hiC Measure.restrict_le_self
  have hiG : Integrable (fun w ↦ pairedEtaLogSignedColour w * etaNormalizedHeatKernel h (w - c))
      pairedEtaLogGapMeasure := Integrable.mono_measure hiC Measure.restrict_le_self
  have hsum : (∫ w in Ioi (0 : ℝ), etaNormalizedHeatKernel h (w - c)) =
      (∫ w, etaNormalizedHeatKernel h (w - c) ∂pairedEtaLogMeasure) + pairedEtaGaussianGapMass h c := by
    rw [volume_restrict_Ioi_zero_eq_pairedEtaLogMeasure_add_gapMeasure]
    exact integral_add_measure (Integrable.mono_measure hi Measure.restrict_le_self)
      (integrable_etaNormalizedHeatKernel_gap hh c)
  have hcolour : (∫ w in Ioi (0 : ℝ), pairedEtaLogSignedColour w * etaNormalizedHeatKernel h (w - c)) =
      (∫ w, etaNormalizedHeatKernel h (w - c) ∂pairedEtaLogMeasure) - pairedEtaGaussianGapMass h c := by
    rw [volume_restrict_Ioi_zero_eq_pairedEtaLogMeasure_add_gapMeasure,
      integral_add_measure hiS hiG]
    have hs : (∫ w, pairedEtaLogSignedColour w * etaNormalizedHeatKernel h (w - c) ∂pairedEtaLogMeasure) =
        ∫ w, etaNormalizedHeatKernel h (w - c) ∂pairedEtaLogMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_pairedEtaLogSupport] with w hw
      norm_num [pairedEtaLogSignedColour, pairedEtaLogIndicator, hw]
    have hg : (∫ w, pairedEtaLogSignedColour w * etaNormalizedHeatKernel h (w - c) ∂pairedEtaLogGapMeasure) =
        -pairedEtaGaussianGapMass h c := by
      rw [pairedEtaGaussianGapMass, ← integral_neg]
      apply integral_congr_ae
      filter_upwards [ae_mem_pairedEtaLogGapSupport] with w hw
      simp [pairedEtaLogSignedColour, pairedEtaLogIndicator, hw.2]
    rw [hs, hg]
    ring
  rw [integral_Ioi_etaNormalizedHeatKernel_sub hh] at hsum
  rw [integral_Ioi_etaSignedColour_gaussian_eq_remainder hh hc] at hcolour
  linarith

end

end RiemannGaussian
