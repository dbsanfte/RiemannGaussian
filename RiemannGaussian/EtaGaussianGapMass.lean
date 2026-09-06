import RiemannGaussian.EtaDecreasingGapMass

/-!
# Quantitative Gaussian mass on the full eta gap

The actual logarithmic interval balance gives a Gaussian normalization
without exponential tilt. The gap mass approaches one quarter of the
full-line Gaussian mass, with an explicit inverse-width error.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- A positive-width Gaussian decreases on nonnegative displacements. -/
theorem antitoneOn_etaNormalizedHeatKernel {h : ℝ} (hh : 0 < h) :
    AntitoneOn (etaNormalizedHeatKernel h) (Ici 0) := by
  intro x hx y hy hxy
  simp only [etaNormalizedHeatKernel_eq_quadratic hh]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hsq : x ^ 2 ≤ y ^ 2 := sq_le_sq₀ hx hy |>.2 hxy
  exact mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr (by positivity))

/-- Exactly one half of the normalized Gaussian lies at positive time. -/
theorem integral_Ioi_etaNormalizedHeatKernel {h : ℝ} (hh : 0 < h) :
    (∫ w in Ioi (0 : ℝ), etaNormalizedHeatKernel h w) = 1 / 2 := by
  simp_rw [etaNormalizedHeatKernel_eq_quadratic hh]
  rw [integral_div, integral_gaussian_Ioi]
  rw [show Real.pi / (1 / (4 * h ^ 2)) = Real.pi * (2 * h) ^ 2 by field_simp; ring,
    Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq (by positivity)]
  have hsqrt : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  field_simp

/-- The mass of a translated normalized Gaussian on the entire actual gap. -/
def pairedEtaGaussianGapMass (h c : ℝ) : ℝ :=
  ∫ w, etaNormalizedHeatKernel h (w - c) ∂pairedEtaLogGapMeasure

/-- Every translated Gaussian is genuinely integrable on the full gap. -/
theorem integrable_etaNormalizedHeatKernel_gap {h : ℝ} (hh : 0 < h) (c : ℝ) :
    Integrable (fun w ↦ etaNormalizedHeatKernel h (w - c)) pairedEtaLogGapMeasure :=
  Integrable.mono_measure ((integrable_etaNormalizedHeatKernel hh).comp_sub_right c)
    Measure.restrict_le_self

/-- Actual gap mass is positive at every positive width and every center. -/
theorem pairedEtaGaussianGapMass_pos {h : ℝ} (hh : 0 < h) (c : ℝ) :
    0 < pairedEtaGaussianGapMass h c := by
  apply (integral_pos_iff_support_of_nonneg
    (fun w ↦ (etaNormalizedHeatKernel_pos hh (w - c)).le)
    (integrable_etaNormalizedHeatKernel_gap hh c)).2
  have hs : Function.support (fun w ↦ etaNormalizedHeatKernel h (w - c)) = univ := by
    ext w
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (etaNormalizedHeatKernel_pos hh _).ne'
  rw [hs]
  exact Measure.measure_univ_pos.mpr pairedEtaLogGapMeasure_ne_zero

/-- The full gap cannot contain more than the unit full-line Gaussian mass. -/
theorem pairedEtaGaussianGapMass_le_one {h : ℝ} (hh : 0 < h) (c : ℝ) :
    pairedEtaGaussianGapMass h c ≤ 1 := by
  have hle := integral_mono_measure (show pairedEtaLogGapMeasure ≤ volume from Measure.restrict_le_self)
    (Eventually.of_forall fun w ↦ (etaNormalizedHeatKernel_pos hh (w - c)).le)
    ((integrable_etaNormalizedHeatKernel hh).comp_sub_right c)
  simpa only [pairedEtaGaussianGapMass, integral_sub_right_eq_self,
    integral_etaNormalizedHeatKernel hh] using hle

/-- The actual centered gap mass is within an explicit inverse-width
error below one quarter, with no density-limit hypothesis. -/
theorem pairedEtaGaussianGapMass_zero_bounds {h : ℝ} (hh : 0 < h) :
    1 / 4 - Real.log 2 / (4 * Real.sqrt Real.pi * h) ≤ pairedEtaGaussianGapMass h 0 ∧
      pairedEtaGaussianGapMass h 0 ≤ 1 / 4 := by
  have hb := pairedEta_decreasing_gap_mass_bounds
    (integrable_etaNormalizedHeatKernel hh).integrableOn
    (antitoneOn_etaNormalizedHeatKernel hh)
    (fun w _ ↦ (etaNormalizedHeatKernel_pos hh w).le)
  rw [integral_Ioi_etaNormalizedHeatKernel hh] at hb
  have hz : etaNormalizedHeatKernel h 0 = 1 / (2 * Real.sqrt Real.pi * h) := by
    simp [etaNormalizedHeatKernel]
  simp only [pairedEtaGaussianGapMass, sub_zero]
  rw [hz] at hb
  constructor
  · convert hb.1 using 1; ring
  · convert hb.2 using 1; norm_num

/-- At width at least two the full-gap normalization is uniformly
bounded away from zero by an explicit rational constant. -/
theorem pairedEtaGaussianGapMass_zero_ge_eighth {h : ℝ} (hh : 2 ≤ h) :
    1 / 8 ≤ pairedEtaGaussianGapMass h 0 := by
  have hh0 : 0 < h := lt_of_lt_of_le (by norm_num) hh
  have hsqrt : 1 ≤ Real.sqrt Real.pi := Real.one_le_sqrt.mpr (by linarith [Real.pi_gt_three])
  have hlog : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1; norm_num
  have hden : 8 ≤ 4 * Real.sqrt Real.pi * h := by nlinarith
  have he : Real.log 2 / (4 * Real.sqrt Real.pi * h) ≤ 1 / 8 := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith
  have hb := (pairedEtaGaussianGapMass_zero_bounds hh0).1
  linarith

/-- Translating the Gaussian to the left removes exactly its finite
initial interval mass from the positive half-line. -/
theorem integral_Ioi_etaNormalizedHeatKernel_add {h : ℝ} (hh : 0 < h) (c : ℝ) :
    (∫ w in Ioi (0 : ℝ), etaNormalizedHeatKernel h (w + c)) =
      1 / 2 - ∫ w in (0 : ℝ)..c, etaNormalizedHeatKernel h w := by
  have he : (∫ w in Ioi (0 : ℝ), etaNormalizedHeatKernel h (w + c)) =
      ∫ w in Ioi c, etaNormalizedHeatKernel h w := by
    calc
      _ = ∫ w : ℝ, (Ioi c).indicator (etaNormalizedHeatKernel h) (w + c) := by
        rw [← integral_indicator measurableSet_Ioi]
        apply integral_congr_ae
        filter_upwards with w
        by_cases hw : 0 < w
        · rw [indicator_of_mem (show w ∈ Ioi (0 : ℝ) from hw),
            indicator_of_mem (show w + c ∈ Ioi c by change c < w + c; linarith)]
        · rw [indicator_of_notMem (show w ∉ Ioi (0 : ℝ) from hw),
            indicator_of_notMem (show w + c ∉ Ioi c by change ¬c < w + c; linarith)]
      _ = _ := by rw [integral_add_right_eq_self, integral_indicator measurableSet_Ioi]
  rw [he]
  have hi := intervalIntegral.integral_Ioi_sub_Ioi'
    (a := (0 : ℝ)) (b := c) (integrable_etaNormalizedHeatKernel hh).integrableOn
    (integrable_etaNormalizedHeatKernel hh).integrableOn
  rw [integral_Ioi_etaNormalizedHeatKernel hh] at hi
  linarith

/-- Translating the Gaussian to the right adds exactly its finite
initial interval mass to the positive half-line. -/
theorem integral_Ioi_etaNormalizedHeatKernel_sub {h : ℝ} (hh : 0 < h) (c : ℝ) :
    (∫ w in Ioi (0 : ℝ), etaNormalizedHeatKernel h (w - c)) =
      1 / 2 + ∫ w in (0 : ℝ)..c, etaNormalizedHeatKernel h w := by
  have he : (∫ w in (0 : ℝ)..(-c), etaNormalizedHeatKernel h w) =
      -(∫ w in (0 : ℝ)..c, etaNormalizedHeatKernel h w) := by
    have hev := intervalIntegral.integral_comp_neg (etaNormalizedHeatKernel h) (a := (0 : ℝ)) (b := c)
    simp only [etaNormalizedHeatKernel_neg, neg_zero] at hev
    rw [intervalIntegral.integral_symm, ← hev]
  simpa only [sub_eq_add_neg, he, neg_neg] using integral_Ioi_etaNormalizedHeatKernel_add hh (-c)

/-- On positive time the absolute translation error has an integrable
three-Gaussian majorant, retaining the exact translated kernels. -/
theorem etaNormalizedHeatKernel_translation_abs_le {h c w : ℝ} (hh : 0 < h)
    (hc : 0 ≤ c) (hw : 0 ≤ w) :
    |etaNormalizedHeatKernel h (w - c) - etaNormalizedHeatKernel h w| ≤
      etaNormalizedHeatKernel h (w - c) + etaNormalizedHeatKernel h w -
        2 * etaNormalizedHeatKernel h (w + c) := by
  have hd₁ : etaNormalizedHeatKernel h (w + c) ≤ etaNormalizedHeatKernel h (w - c) := by
    simp only [etaNormalizedHeatKernel_eq_quadratic hh]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr (by positivity))
    nlinarith [mul_nonneg hw hc]
  have hd₂ : etaNormalizedHeatKernel h (w + c) ≤ etaNormalizedHeatKernel h w :=
    antitoneOn_etaNormalizedHeatKernel hh hw (add_nonneg hw hc) (le_add_of_nonneg_right hc)
  apply abs_sub_le_iff.mpr
  constructor <;> linarith

/-- Shifting the center has an explicit inverse-width cost on the full
actual gap; no invariance of the arithmetic measure is assumed. -/
theorem pairedEtaGaussianGapMass_sub_zero_le {h c : ℝ} (hh : 0 < h) (hc : 0 ≤ c) :
    |pairedEtaGaussianGapMass h c - pairedEtaGaussianGapMass h 0| ≤
      3 * c / (2 * Real.sqrt Real.pi * h) := by
  have hi₀ := integrable_etaNormalizedHeatKernel hh
  have hiSub := hi₀.comp_sub_right c
  have hiAdd := hi₀.comp_add_right c
  have hiE : IntegrableOn (fun w ↦ etaNormalizedHeatKernel h (w - c) + etaNormalizedHeatKernel h w -
      2 * etaNormalizedHeatKernel h (w + c)) (Ioi (0 : ℝ)) :=
    (hiSub.add hi₀ |>.sub (hiAdd.const_mul 2)).integrableOn
  have hmass : (∫ w in Ioi (0 : ℝ), etaNormalizedHeatKernel h (w - c) + etaNormalizedHeatKernel h w -
      2 * etaNormalizedHeatKernel h (w + c)) =
      3 * ∫ w in (0 : ℝ)..c, etaNormalizedHeatKernel h w := by
    rw [integral_sub (f := fun w ↦ etaNormalizedHeatKernel h (w - c) + etaNormalizedHeatKernel h w)
      (g := fun w ↦ 2 * etaNormalizedHeatKernel h (w + c))
      (hiSub.add hi₀).integrableOn (hiAdd.const_mul 2).integrableOn,
      integral_add hiSub.integrableOn hi₀.integrableOn, integral_const_mul,
      integral_Ioi_etaNormalizedHeatKernel_sub hh, integral_Ioi_etaNormalizedHeatKernel_add hh,
      integral_Ioi_etaNormalizedHeatKernel hh]
    ring
  have hfinite : (∫ w in (0 : ℝ)..c, etaNormalizedHeatKernel h w) ≤
      c / (2 * Real.sqrt Real.pi * h) := by
    rw [intervalIntegral.integral_of_le hc]
    calc
      _ ≤ ∫ _w in Ioc (0 : ℝ) c, 1 / (2 * Real.sqrt Real.pi * h) :=
        integral_mono_ae hi₀.integrableOn (integrable_const _)
          (Eventually.of_forall fun w ↦ etaNormalizedHeatKernel_le hh w)
      _ = _ := by rw [setIntegral_const, Real.volume_real_Ioc_of_le hc, smul_eq_mul, sub_zero]; ring
  calc
    _ = |∫ w, (etaNormalizedHeatKernel h (w - c) - etaNormalizedHeatKernel h w) ∂pairedEtaLogGapMeasure| := by
      simp only [pairedEtaGaussianGapMass, sub_zero]
      rw [integral_sub (integrable_etaNormalizedHeatKernel_gap hh c)
        (Integrable.mono_measure hi₀ Measure.restrict_le_self)]
    _ ≤ ∫ w, |etaNormalizedHeatKernel h (w - c) - etaNormalizedHeatKernel h w| ∂pairedEtaLogGapMeasure :=
      abs_integral_le_integral_abs
    _ ≤ ∫ w in Ioi (0 : ℝ), |etaNormalizedHeatKernel h (w - c) - etaNormalizedHeatKernel h w| :=
      integral_mono_measure pairedEtaLogGapMeasure_le_volume_restrict_Ioi_zero
        (Eventually.of_forall fun _ ↦ abs_nonneg _) (hiSub.sub hi₀).abs.integrableOn
    _ ≤ ∫ w in Ioi (0 : ℝ), etaNormalizedHeatKernel h (w - c) + etaNormalizedHeatKernel h w -
        2 * etaNormalizedHeatKernel h (w + c) := by
      apply integral_mono_ae (hiSub.sub hi₀).abs.integrableOn hiE
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      exact etaNormalizedHeatKernel_translation_abs_le hh hc hw.le
    _ = 3 * ∫ w in (0 : ℝ)..c, etaNormalizedHeatKernel h w := hmass
    _ ≤ _ := by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hfinite (by norm_num : (0 : ℝ) ≤ 3)

end

end RiemannGaussian
