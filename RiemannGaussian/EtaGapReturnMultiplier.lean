import RiemannGaussian.EtaLeadingCurrentReconstruction

/-!
# Quantitative Gaussian return on the actual infinite eta gap

The normalized gap-time average is a multiplier between zero and one.
Its exact signed error is an integral of the two-transition profile minus
one. The second exponential gap moment controls that error at order `h⁻²`,
with both physical endpoint times retained.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The second real exponential moment of the actual gap. -/
def pairedEtaGapLaplaceSecondMoment (a : ℝ) : ℝ :=
  ∫ w, w ^ 2 * Real.exp (-a * w) ∂pairedEtaLogGapMeasure

/-- The actual second gap moment is genuinely integrable at positive tilt. -/
theorem integrable_gapLaplaceSecondMoment {a : ℝ} (ha : 0 < a) :
    Integrable (fun w : ℝ ↦ w ^ 2 * Real.exp (-a * w)) pairedEtaLogGapMeasure :=
  Integrable.mono_measure (integrableOn_pow_mul_exp_neg_mul_Ioi_zero_nat 2 ha)
    pairedEtaLogGapMeasure_le_volume_restrict_Ioi_zero

/-- The gap second moment is nonnegative and bounded by the exact complete
half-line moment, retaining the cubic cost as the tilt vanishes. -/
theorem pairedEtaGapLaplaceSecondMoment_bounds {a : ℝ} (ha : 0 < a) :
    0 ≤ pairedEtaGapLaplaceSecondMoment a ∧ pairedEtaGapLaplaceSecondMoment a ≤ 2 / a ^ 3 := by
  constructor
  · exact integral_nonneg fun _ ↦ by positivity
  · have hm := integral_mono_measure pairedEtaLogGapMeasure_le_volume_restrict_Ioi_zero
      (Eventually.of_forall (fun w : ℝ ↦ by positivity : ∀ w : ℝ, 0 ≤ w ^ 2 * Real.exp (-a * w)))
      (integrableOn_pow_mul_exp_neg_mul_Ioi_zero_nat 2 ha)
    change pairedEtaGapLaplaceSecondMoment a ≤ positiveHalfLineRealLogLaplaceMoment 2 a at hm
    rw [positiveHalfLineRealLogLaplaceMoment_eq_factorial 2 ha] at hm
    norm_num at hm
    exact hm

/-- Decreasing a positive tilt increases the actual gap normalization mass. -/
theorem pairedEtaGapLaplaceMass_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    pairedEtaGapLaplaceMass b ≤ pairedEtaGapLaplaceMass a := by
  apply integral_mono_ae (integrable_rexp_neg_mul_pairedEtaLogGapMeasure (ha.trans_le hab))
    (integrable_rexp_neg_mul_pairedEtaLogGapMeasure ha)
  filter_upwards [ae_mem_pairedEtaLogGapSupport] with w hw
  exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hab (le_of_lt hw.1)])

/-- The exact product of the two amplitude-free profiles retains both
ordered displacements in one Gaussian exponent. -/
theorem pairedEtaHeatTransitionProfile_product {h : ℝ} (hh : 0 < h) (t u w : ℝ) :
    pairedEtaHeatTransitionProfile h (w - t) * pairedEtaHeatTransitionProfile h (u - w) =
      Real.exp (-((w - t) ^ 2 + (u - w) ^ 2) / (8 * h ^ 2)) := by
  unfold pairedEtaHeatTransitionProfile
  rw [← Real.exp_add]
  congr 1
  rw [div_pow, div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp
  ring

/-- The Gaussian return error has a quadratic endpoint majorant, uniformly
over the whole intermediate-time gap. -/
theorem pairedEtaHeatTransitionProfile_product_error_le {h : ℝ} (hh : 0 < h) (t u w : ℝ) :
    |pairedEtaHeatTransitionProfile h (w - t) * pairedEtaHeatTransitionProfile h (u - w) - 1| ≤
      (w ^ 2 + t ^ 2 + u ^ 2) / h ^ 2 := by
  rw [pairedEtaHeatTransitionProfile_product hh]
  have hD : 0 ≤ ((w - t) ^ 2 + (u - w) ^ 2) / (8 * h ^ 2) := by positivity
  have he : Real.exp (-((w - t) ^ 2 + (u - w) ^ 2) / (8 * h ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by simpa only [neg_div] using neg_nonpos.mpr hD)
  rw [abs_of_nonpos (sub_nonpos.mpr he)]
  have hx := Real.add_one_le_exp (-((w - t) ^ 2 + (u - w) ^ 2) / (8 * h ^ 2))
  simp only [neg_div] at hx ⊢
  have hbound : ((w - t) ^ 2 + (u - w) ^ 2) / (8 * h ^ 2) ≤ (w ^ 2 + t ^ 2 + u ^ 2) / h ^ 2 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 8 * h ^ 2) (sq_pos_of_pos hh)).mpr
    nlinarith [sq_nonneg (w + t), sq_nonneg (w + u), sq_nonneg t, sq_nonneg u, sq_nonneg w]
  linarith

/-- The normalized average of the two actual transition profiles over all gap times. -/
def pairedEtaGapReturnMultiplier (a h t u : ℝ) : ℝ :=
  (∫ w, Real.exp (-a * w) *
    (pairedEtaHeatTransitionProfile h (w - t) * pairedEtaHeatTransitionProfile h (u - w))
    ∂pairedEtaLogGapMeasure) / pairedEtaGapLaplaceMass a

/-- The complete multiplier integral is absolutely convergent. -/
theorem integrable_gapReturnMultiplier_kernel {a : ℝ} (ha : 0 < a) (h t u : ℝ) :
    Integrable (fun w : ℝ ↦ Real.exp (-a * w) *
      (pairedEtaHeatTransitionProfile h (w - t) * pairedEtaHeatTransitionProfile h (u - w)))
      pairedEtaLogGapMeasure := by
  apply (integrable_rexp_neg_mul_pairedEtaLogGapMeasure ha).mul_bdd
    (show AEStronglyMeasurable (fun w : ℝ ↦
      pairedEtaHeatTransitionProfile h (w - t) * pairedEtaHeatTransitionProfile h (u - w)) pairedEtaLogGapMeasure by
      unfold pairedEtaHeatTransitionProfile
      fun_prop)
  apply Eventually.of_forall
  intro w
  have hp := pairedEtaHeatTransitionProfile_bounds h (w - t)
  have hq := pairedEtaHeatTransitionProfile_bounds h (u - w)
  change ‖pairedEtaHeatTransitionProfile h (w - t) * pairedEtaHeatTransitionProfile h (u - w)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos hp.1 hq.1)]
  exact mul_le_one₀ hp.2 hq.1.le hq.2

/-- The normalized full gap multiplier is between zero and one. -/
theorem pairedEtaGapReturnMultiplier_bounds {a : ℝ} (ha : 0 < a) (h t u : ℝ) :
    0 ≤ pairedEtaGapReturnMultiplier a h t u ∧ pairedEtaGapReturnMultiplier a h t u ≤ 1 := by
  have hm := pairedEtaGapLaplaceMass_pos ha
  unfold pairedEtaGapReturnMultiplier
  constructor
  · apply div_nonneg _ hm.le
    apply integral_nonneg
    intro w
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg
      (pairedEtaHeatTransitionProfile_bounds h (w - t)).1.le (pairedEtaHeatTransitionProfile_bounds h (u - w)).1.le)
  · apply (div_le_one₀ hm).mpr
    apply integral_mono (integrable_gapReturnMultiplier_kernel ha h t u) (integrable_rexp_neg_mul_pairedEtaLogGapMeasure ha)
    intro w
    apply mul_le_of_le_one_right (Real.exp_pos _).le
    exact mul_le_one₀ (pairedEtaHeatTransitionProfile_bounds h (w - t)).2
      (pairedEtaHeatTransitionProfile_bounds h (u - w)).1.le (pairedEtaHeatTransitionProfile_bounds h (u - w)).2

/-- The signed multiplier defect remains the integral of the exact signed
two-transition profile defect, before taking an absolute value. -/
theorem pairedEtaGapReturnMultiplier_sub_one {a : ℝ} (ha : 0 < a) (h t u : ℝ) :
    pairedEtaGapReturnMultiplier a h t u - 1 =
      (∫ w, Real.exp (-a * w) *
        (pairedEtaHeatTransitionProfile h (w - t) * pairedEtaHeatTransitionProfile h (u - w) - 1)
        ∂pairedEtaLogGapMeasure) / pairedEtaGapLaplaceMass a := by
  have hi := integral_sub (integrable_gapReturnMultiplier_kernel ha h t u)
    (integrable_rexp_neg_mul_pairedEtaLogGapMeasure ha)
  simp only [mul_sub, mul_one]
  rw [hi]
  unfold pairedEtaGapReturnMultiplier
  change _ / pairedEtaGapLaplaceMass a - 1 = (_ - pairedEtaGapLaplaceMass a) / pairedEtaGapLaplaceMass a
  field_simp [(pairedEtaGapLaplaceMass_pos ha).ne']

/-- The normalized return approaches one with an explicit inverse-square
heat-width error, retaining the actual gap mass and second moment. -/
theorem pairedEtaGapReturnMultiplier_error_le {a h : ℝ} (ha : 0 < a) (hh : 0 < h) (t u : ℝ) :
    |pairedEtaGapReturnMultiplier a h t u - 1| ≤
      (pairedEtaGapLaplaceSecondMoment a / pairedEtaGapLaplaceMass a + t ^ 2 + u ^ 2) / h ^ 2 := by
  have hm := pairedEtaGapLaplaceMass_pos ha
  have hi : Integrable (fun w : ℝ ↦ Real.exp (-a * w) * ((w ^ 2 + t ^ 2 + u ^ 2) / h ^ 2))
      pairedEtaLogGapMeasure := by
    convert ((integrable_gapLaplaceSecondMoment ha).add
      ((integrable_rexp_neg_mul_pairedEtaLogGapMeasure ha).const_mul (t ^ 2 + u ^ 2))).div_const (h ^ 2) using 1
    ext w
    simp only [Pi.add_apply]
    ring
  have hb := norm_integral_le_of_norm_le
    (f := fun w : ℝ ↦ Real.exp (-a * w) *
      (pairedEtaHeatTransitionProfile h (w - t) * pairedEtaHeatTransitionProfile h (u - w) - 1))
    hi (Eventually.of_forall fun w ↦ by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (pairedEtaHeatTransitionProfile_product_error_le hh t u w) (Real.exp_pos _).le)
  have hiv : (∫ w, Real.exp (-a * w) * ((w ^ 2 + t ^ 2 + u ^ 2) / h ^ 2) ∂pairedEtaLogGapMeasure) =
      (pairedEtaGapLaplaceSecondMoment a + (t ^ 2 + u ^ 2) * pairedEtaGapLaplaceMass a) / h ^ 2 := by
    have heq : (fun w : ℝ ↦ Real.exp (-a * w) * ((w ^ 2 + t ^ 2 + u ^ 2) / h ^ 2)) =
        (fun w ↦ (w ^ 2 * Real.exp (-a * w) + (t ^ 2 + u ^ 2) * Real.exp (-a * w)) / h ^ 2) := by
      ext w
      ring
    rw [heq, integral_div, integral_add (integrable_gapLaplaceSecondMoment ha)
      ((integrable_rexp_neg_mul_pairedEtaLogGapMeasure ha).const_mul _), integral_const_mul]
    rfl
  rw [pairedEtaGapReturnMultiplier_sub_one ha, abs_div, abs_of_pos hm]
  rw [Real.norm_eq_abs, hiv] at hb
  calc
    _ ≤ ((pairedEtaGapLaplaceSecondMoment a + (t ^ 2 + u ^ 2) * pairedEtaGapLaplaceMass a) / h ^ 2) /
        pairedEtaGapLaplaceMass a := div_le_div_of_nonneg_right hb hm.le
    _ = _ := by field_simp [hm.ne']; ring

/-- One fixed positive gap mass controls the normalized second moment
throughout `0 < a ≤ 1`, retaining the cubic tilt cost. -/
theorem pairedEtaGapLaplaceSecondMoment_div_mass_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    pairedEtaGapLaplaceSecondMoment a / pairedEtaGapLaplaceMass a ≤
      2 / (pairedEtaGapLaplaceMass 1 * a ^ 3) := by
    calc
      _ ≤ (2 / a ^ 3) / pairedEtaGapLaplaceMass a :=
        div_le_div_of_nonneg_right (pairedEtaGapLaplaceSecondMoment_bounds ha).2 (pairedEtaGapLaplaceMass_pos ha).le
      _ ≤ (2 / a ^ 3) / pairedEtaGapLaplaceMass 1 :=
        div_le_div_of_nonneg_left (by positivity) (pairedEtaGapLaplaceMass_pos (by norm_num : (0 : ℝ) < 1))
          (pairedEtaGapLaplaceMass_antitone ha ha1)
      _ = _ := by ring

/-- A fixed positive gap mass controls the entire positive-tilt interval
`0 < a ≤ 1`, with the explicit cubic cost `a⁻³`. -/
theorem pairedEtaGapReturnMultiplier_error_le_smallTilt {a h : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hh : 0 < h) (t u : ℝ) :
    |pairedEtaGapReturnMultiplier a h t u - 1| ≤
      (2 / (pairedEtaGapLaplaceMass 1 * a ^ 3) + t ^ 2 + u ^ 2) / h ^ 2 := by
  apply (pairedEtaGapReturnMultiplier_error_le ha hh t u).trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg h)
  exact add_le_add (add_le_add (pairedEtaGapLaplaceSecondMoment_div_mass_le ha ha1) le_rfl) le_rfl

end

end RiemannGaussian
