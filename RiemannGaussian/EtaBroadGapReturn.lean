import RiemannGaussian.EtaIntegratedGapReturn

/-!
# Broad heat reconstruction through the actual eta gap

At fixed positive tilt the Gaussian amplitude is removed before the width
tends to infinity. An integrable exponential on the entire actual gap
justifies the limit. Its positive mass is retained as the normalization;
the result is the original current with its endpoint tilt still present.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The total exponentially tilted mass of the actual infinite eta gap. -/
def pairedEtaGapLaplaceMass (a : ℝ) : ℝ :=
  ∫ w, Real.exp (-a * w) ∂pairedEtaLogGapMeasure

/-- The actual gap measure is nonzero, as witnessed by its first interval. -/
theorem pairedEtaLogGapMeasure_ne_zero : pairedEtaLogGapMeasure ≠ 0 := by
  have hsub : pairedEtaLogGapInterval 0 ⊆ pairedEtaLogGapSupport := by
    rw [pairedEtaLogGapSupport_eq_explicit]
    exact subset_iUnion (fun n : ℕ ↦ pairedEtaLogGapInterval n) 0
  have hvol : 0 < volume (pairedEtaLogGapInterval 0) := by
    rw [pairedEtaLogGapInterval, Real.volume_Ioc]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr (pairedEtaLogGapInterval_pos 0))
  have hpos : 0 < pairedEtaLogGapMeasure univ := by
    simpa only [pairedEtaLogGapMeasure, Measure.restrict_apply_univ] using
      lt_of_lt_of_le hvol (measure_mono hsub)
  intro hz
  simp only [hz, Measure.coe_zero, Pi.zero_apply, lt_self_iff_false] at hpos

/-- The normalization mass is strictly positive at every positive tilt. -/
theorem pairedEtaGapLaplaceMass_pos {a : ℝ} (ha : 0 < a) :
    0 < pairedEtaGapLaplaceMass a := by
  let _ : NeZero pairedEtaLogGapMeasure := ⟨pairedEtaLogGapMeasure_ne_zero⟩
  exact integral_exp_pos (integrable_rexp_neg_mul_pairedEtaLogGapMeasure ha)

/-- The amplitude-free profile of one actual heat transition. -/
def pairedEtaHeatTransitionProfile (h r : ℝ) : ℝ :=
  Real.exp (-(1 / 4) * (r / (Real.sqrt 2 * h)) ^ 2)

/-- A transition profile is positive and at most one, at every real width. -/
theorem pairedEtaHeatTransitionProfile_bounds (h r : ℝ) :
    0 < pairedEtaHeatTransitionProfile h r ∧ pairedEtaHeatTransitionProfile h r ≤ 1 := by
  exact ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (r / (Real.sqrt 2 * h))])⟩

/-- A broad transition profile tends to one at each fixed displacement. -/
theorem pairedEtaHeatTransitionProfile_tendsto (r : ℝ) :
    Tendsto (fun h : ℝ ↦ pairedEtaHeatTransitionProfile h r) atTop (𝓝 1) := by
  have hr : Tendsto (fun h : ℝ ↦ r / (Real.sqrt 2 * h)) atTop (𝓝 0) :=
    (tendsto_id.const_mul_atTop (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).const_div_atTop r
  simpa only [pairedEtaHeatTransitionProfile, Function.comp_def, zero_pow (by norm_num : 2 ≠ 0), mul_zero, Real.exp_zero] using
    Real.continuous_exp.tendsto (-(1 / 4 : ℝ) * 0 ^ 2) |>.comp
      ((hr.pow 2).const_mul (-(1 / 4 : ℝ)))

/-- The full real amplitude-free return profile, before its gap-time integral. -/
def pairedEtaBroadGapReturnKernel (a h t u w : ℝ) : ℝ :=
  Real.exp (-a * (t + u) / 2) * Real.exp (-a * w) *
    pairedEtaHeatTransitionProfile h (w - t) * pairedEtaHeatTransitionProfile h (u - w)

/-- On nonnegative endpoint times the full profile is dominated by the
integrable intermediate-time exponential, independently of heat width. -/
theorem pairedEtaBroadGapReturnKernel_bounds {a t u : ℝ} (ha : 0 ≤ a)
    (ht : 0 ≤ t) (hu : 0 ≤ u) (h w : ℝ) :
    0 ≤ pairedEtaBroadGapReturnKernel a h t u w ∧
      pairedEtaBroadGapReturnKernel a h t u w ≤ Real.exp (-a * w) := by
  have hp := pairedEtaHeatTransitionProfile_bounds h (w - t)
  have hq := pairedEtaHeatTransitionProfile_bounds h (u - w)
  have he : Real.exp (-a * (t + u) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  unfold pairedEtaBroadGapReturnKernel
  constructor
  · exact mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) hp.1.le) hq.1.le
  · calc
      _ ≤ Real.exp (-a * (t + u) / 2) * Real.exp (-a * w) * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hp.2 (by positivity)) hq.2 hq.1.le (by positivity)
      _ ≤ _ := by simpa only [mul_one] using mul_le_of_le_one_left (Real.exp_pos _).le he

/-- Pointwise broad heat retains exactly the endpoint damping and gap exponential. -/
theorem pairedEtaBroadGapReturnKernel_tendsto (a t u w : ℝ) :
    Tendsto (fun h : ℝ ↦ pairedEtaBroadGapReturnKernel a h t u w) atTop
      (𝓝 (Real.exp (-a * (t + u) / 2) * Real.exp (-a * w))) := by
  simpa only [pairedEtaBroadGapReturnKernel, mul_one] using
    ((pairedEtaHeatTransitionProfile_tendsto (w - t)).const_mul
      (Real.exp (-a * (t + u) / 2) * Real.exp (-a * w))).mul
        (pairedEtaHeatTransitionProfile_tendsto (u - w))

/-- The amplitude-free profile is exactly the scaled literal two-transition
return, at zero probe phases and equal tilts and widths. -/
theorem pairedEtaBroadGapReturnKernel_eq_scaled {h : ℝ} (hh : 0 < h)
    (a t u : ℝ) {w : ℝ} (hw : w ∈ pairedEtaLogGapSupport) :
    (pairedEtaBroadGapReturnKernel a h t u w : ℂ) =
      ((pairedEtaHeatTransitionAmplitude h) ^ 2 : ℝ) *
        pairedEtaOrderedGapReturnKernelCore a h a h (fun _ ↦ 0) (fun _ ↦ 0) t u w := by
  have hc : pairedEtaLogIndicator w = 0 := Set.indicator_of_notMem hw.2 _
  have he : Real.exp (-a * (t + u) / 2) * Real.exp (-a * w) =
      Real.exp (-a * (t + w) / 2) * Real.exp (-a * (w + u) / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp only [pairedEtaOrderedGapReturnKernelCore, hc, sub_zero, mul_one,
    pairedEtaHeatPhaseUnit, sub_self, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  rw [← Complex.ofReal_mul]
  congr 1
  unfold pairedEtaBroadGapReturnKernel pairedEtaHeatTransitionProfile etaNormalizedHeatKernel
    pairedEtaHeatTransitionAmplitude
  rw [he]
  field_simp

/-- The square of the exact amplitude denominator is `8*pi*h^2`. -/
theorem pairedEtaHeatTransitionAmplitude_sq (h : ℝ) :
    pairedEtaHeatTransitionAmplitude h ^ 2 = 8 * Real.pi * h ^ 2 := by
  unfold pairedEtaHeatTransitionAmplitude
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Dominated convergence on the actual gap-current product reconstructs
the tilted current, multiplied by the exact positive gap mass. -/
theorem integral_current_broadGapReturn_tendsto {μ : Measure (ℝ × ℝ)} [SFinite μ]
    {f : ℝ × ℝ → ℝ} (hf : Integrable f μ) {T : ℝ × ℝ → ℝ} (hT : Measurable T)
    (hpos : ∀ᵐ p ∂μ, 0 ≤ T p ∧ 0 ≤ p.2) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun h : ℝ ↦ ∫ z : (ℝ × ℝ) × ℝ,
      (f z.1 : ℂ) * (pairedEtaBroadGapReturnKernel a h (T z.1) z.1.2 z.2 : ℂ)
      ∂(μ.prod pairedEtaLogGapMeasure)) atTop
      (𝓝 ((pairedEtaGapLaplaceMass a : ℂ) *
        ∫ p : ℝ × ℝ, (f p : ℂ) * (Real.exp (-a * (T p + p.2) / 2) : ℂ) ∂μ)) := by
  have hlim : Tendsto (fun h : ℝ ↦ ∫ z : (ℝ × ℝ) × ℝ,
      (f z.1 : ℂ) * (pairedEtaBroadGapReturnKernel a h (T z.1) z.1.2 z.2 : ℂ)
      ∂(μ.prod pairedEtaLogGapMeasure)) atTop
      (𝓝 (∫ z : (ℝ × ℝ) × ℝ, (f z.1 : ℂ) *
        (Real.exp (-a * (T z.1 + z.1.2) / 2) * Real.exp (-a * z.2) : ℝ)
        ∂(μ.prod pairedEtaLogGapMeasure))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun z : (ℝ × ℝ) × ℝ ↦ |f z.1| * Real.exp (-a * z.2))
    · apply Eventually.of_forall
      intro h
      have hm : Measurable (fun z : (ℝ × ℝ) × ℝ ↦ pairedEtaBroadGapReturnKernel a h (T z.1) z.1.2 z.2) := by
        unfold pairedEtaBroadGapReturnKernel pairedEtaHeatTransitionProfile
        fun_prop
      exact hf.ofReal.aestronglyMeasurable.comp_fst.mul hm.complex_ofReal.aestronglyMeasurable
    · apply Eventually.of_forall
      intro h
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hpos] with z hz
      have hb := pairedEtaBroadGapReturnKernel_bounds ha.le hz.1 hz.2 h z.2
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact mul_le_mul_of_nonneg_left hb.2 (abs_nonneg _)
    · exact hf.abs.mul_prod (integrable_rexp_neg_mul_pairedEtaLogGapMeasure ha)
    · exact Eventually.of_forall fun z ↦
        ((Complex.continuous_ofReal.tendsto _).comp
          (pairedEtaBroadGapReturnKernel_tendsto a (T z.1) z.1.2 z.2)).const_mul (f z.1 : ℂ)
  have heq : (∫ z : (ℝ × ℝ) × ℝ, (f z.1 : ℂ) *
      (Real.exp (-a * (T z.1 + z.1.2) / 2) * Real.exp (-a * z.2) : ℝ)
      ∂(μ.prod pairedEtaLogGapMeasure)) =
      (pairedEtaGapLaplaceMass a : ℂ) *
        ∫ p : ℝ × ℝ, (f p : ℂ) * (Real.exp (-a * (T p + p.2) / 2) : ℂ) ∂μ := by
    simp only [Complex.ofReal_mul, ← mul_assoc]
    rw [integral_prod_mul (μ := μ) (ν := pairedEtaLogGapMeasure)
      (fun p : ℝ × ℝ ↦ (f p : ℂ) * (Real.exp (-a * (T p + p.2) / 2) : ℂ))
      (fun w : ℝ ↦ (Real.exp (-a * w) : ℂ)), integral_complex_ofReal]
    exact mul_comm _ _
  exact heq ▸ hlim

/-- At each positive width, removing the amplitude commutes exactly with
the full current-gap integral. -/
theorem integral_current_broadGapReturn_eq_scaled {μ : Measure (ℝ × ℝ)}
    (f : ℝ × ℝ → ℝ) (T : ℝ × ℝ → ℝ) {h : ℝ} (hh : 0 < h) (a : ℝ) :
    (∫ z : (ℝ × ℝ) × ℝ, (f z.1 : ℂ) *
      (pairedEtaBroadGapReturnKernel a h (T z.1) z.1.2 z.2 : ℂ) ∂(μ.prod pairedEtaLogGapMeasure)) =
      ((pairedEtaHeatTransitionAmplitude h) ^ 2 : ℝ) *
        ∫ z : (ℝ × ℝ) × ℝ, (f z.1 : ℂ) *
          pairedEtaOrderedGapReturnKernelCore a h a h (fun _ ↦ 0) (fun _ ↦ 0) (T z.1) z.1.2 z.2
          ∂(μ.prod pairedEtaLogGapMeasure) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae ae_mem_pairedEtaLogGapSupport] with z hz
  rw [pairedEtaBroadGapReturnKernel_eq_scaled hh a (T z.1) z.1.2 hz]
  ring

/-- The fully normalized literal return converges to the damped current.
The gap normalization is proved nonzero and no integral is totalized. -/
theorem normalized_integral_current_gapReturn_tendsto {μ : Measure (ℝ × ℝ)} [SFinite μ]
    {f : ℝ × ℝ → ℝ} (hf : Integrable f μ) {T : ℝ × ℝ → ℝ} (hT : Measurable T)
    (hpos : ∀ᵐ p ∂μ, 0 ≤ T p ∧ 0 ≤ p.2) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun h : ℝ ↦ (((pairedEtaHeatTransitionAmplitude h) ^ 2 / pairedEtaGapLaplaceMass a : ℝ) : ℂ) *
      ∫ z : (ℝ × ℝ) × ℝ, (f z.1 : ℂ) *
        pairedEtaOrderedGapReturnKernelCore a h a h (fun _ ↦ 0) (fun _ ↦ 0) (T z.1) z.1.2 z.2
        ∂(μ.prod pairedEtaLogGapMeasure)) atTop
      (𝓝 (∫ p : ℝ × ℝ, (f p : ℂ) * (Real.exp (-a * (T p + p.2) / 2) : ℂ) ∂μ)) := by
  have hm : (pairedEtaGapLaplaceMass a : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pairedEtaGapLaplaceMass_pos ha).ne'
  have hl := (integral_current_broadGapReturn_tendsto hf hT hpos ha).const_mul
    (pairedEtaGapLaplaceMass a : ℂ)⁻¹
  simp only [inv_mul_cancel_left₀ hm] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with h hh
  rw [integral_current_broadGapReturn_eq_scaled f T hh a]
  push_cast
  ring

end

end RiemannGaussian
