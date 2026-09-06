import RiemannGaussian.EtaGaussianGapMass

/-!
# Actual zero-tilt gap normalization and reconstruction multiplier

The full-gap Gaussian mass replaces the positive-tilt Laplace mass. Exact
midpoint composition retains the arithmetic gap before a quantitative
finite-window estimate compares its normalized multiplier with one.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Gaussian normalization of the full actual gap return at zero tilt. -/
def pairedEtaZeroTiltGapNormalization (h : ℝ) : ℝ :=
  4 * Real.sqrt Real.pi * h / pairedEtaGaussianGapMass h 0

/-- The exact normalized zero-tilt multiplier on the original endpoints. -/
def pairedEtaZeroTiltGapMultiplier (h t u : ℝ) : ℝ :=
  Real.exp (-((u - t) ^ 2 / (16 * h ^ 2))) *
    (pairedEtaGaussianGapMass h ((t + u) / 2) / pairedEtaGaussianGapMass h 0)

/-- The new normalization is positive and grows at most linearly in width. -/
theorem pairedEtaZeroTiltGapNormalization_bounds {h : ℝ} (hh : 2 ≤ h) :
    0 < pairedEtaZeroTiltGapNormalization h ∧
      pairedEtaZeroTiltGapNormalization h ≤ 32 * Real.sqrt Real.pi * h := by
  have hh0 : 0 < h := lt_of_lt_of_le (by norm_num) hh
  have hg := pairedEtaGaussianGapMass_pos hh0 0
  have hbound := pairedEtaGaussianGapMass_zero_ge_eighth hh
  unfold pairedEtaZeroTiltGapNormalization
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ (4 * Real.sqrt Real.pi * h) / (1 / 8) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hbound
    _ = _ := by ring

/-- The arithmetic Gaussian gap mass is measurable in its center. -/
theorem measurable_pairedEtaGaussianGapMass (h : ℝ) :
    Measurable (pairedEtaGaussianGapMass h) := by
  have hm : Measurable (fun p : ℝ × ℝ ↦ etaNormalizedHeatKernel h (p.2 - p.1)) := by
    unfold etaNormalizedHeatKernel
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- The actual zero-tilt multiplier is jointly measurable in its endpoints. -/
theorem measurable_pairedEtaZeroTiltGapMultiplier (h : ℝ) :
    Measurable (fun p : ℝ × ℝ ↦ pairedEtaZeroTiltGapMultiplier h p.1 p.2) := by
  have hm := (measurable_pairedEtaGaussianGapMass h).comp
    ((measurable_fst.add measurable_snd).div_const 2)
  unfold pairedEtaZeroTiltGapMultiplier
  exact (by fun_prop : Measurable (fun p : ℝ × ℝ ↦
    Real.exp (-((p.2 - p.1) ^ 2 / (16 * h ^ 2))))).mul (hm.div_const _)

/-- Every normalized multiplier is positive and uniformly at most eight,
including endpoints outside the positive arithmetic window. -/
theorem pairedEtaZeroTiltGapMultiplier_bounds {h : ℝ} (hh : 2 ≤ h) (t u : ℝ) :
    0 < pairedEtaZeroTiltGapMultiplier h t u ∧ pairedEtaZeroTiltGapMultiplier h t u ≤ 8 := by
  have hh0 : 0 < h := lt_of_lt_of_le (by norm_num) hh
  have hg := pairedEtaGaussianGapMass_pos hh0 0
  have hc := pairedEtaGaussianGapMass_pos hh0 ((t + u) / 2)
  have he : Real.exp (-((u - t) ^ 2 / (16 * h ^ 2))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hr : pairedEtaGaussianGapMass h ((t + u) / 2) / pairedEtaGaussianGapMass h 0 ≤ 8 := by
    calc
      _ ≤ 1 / pairedEtaGaussianGapMass h 0 :=
        div_le_div_of_nonneg_right (pairedEtaGaussianGapMass_le_one hh0 _) hg.le
      _ ≤ 1 / (1 / 8) := one_div_le_one_div_of_le (by norm_num)
        (pairedEtaGaussianGapMass_zero_ge_eighth hh)
      _ = _ := by norm_num
  unfold pairedEtaZeroTiltGapMultiplier
  exact ⟨by positivity, (mul_le_of_le_one_left (by positivity) he).trans hr⟩

/-- Exact Gaussian amplitude removal at the composed width. -/
theorem etaNormalizedHeatKernel_double_width_scaled {h : ℝ} (hh : 0 < h) (r : ℝ) :
    (4 * Real.sqrt Real.pi * h) * etaNormalizedHeatKernel (2 * h) r =
      Real.exp (-(r ^ 2 / (16 * h ^ 2))) := by
  rw [etaNormalizedHeatKernel_eq_quadratic (by positivity)]
  have he : -(1 / (4 * (2 * h) ^ 2)) * r ^ 2 = -(r ^ 2 / (16 * h ^ 2)) := by ring
  rw [he]
  have hsqrt : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  field_simp
  norm_num

/-- The normalized full-gap slice equals its arithmetic midpoint multiplier.
This evaluates the existing continuous two-transition kernel at zero tilt. -/
theorem integral_fullTwoHeat_zero_phase_gap_normalized {h : ℝ} (hh : 0 < h) (t u : ℝ) :
    (pairedEtaZeroTiltGapNormalization h : ℂ) *
      (∫ w, pairedEtaFullTwoHeatKernel 0 h (fun _ ↦ 0) (fun _ ↦ 0) t u w ∂pairedEtaLogGapMeasure) =
      (pairedEtaZeroTiltGapMultiplier h t u : ℂ) := by
  have he : (fun w ↦ pairedEtaFullTwoHeatKernel 0 h (fun _ ↦ 0) (fun _ ↦ 0) t u w) =
      (fun w ↦ ((etaNormalizedHeatKernel (2 * h) (u - t)) : ℂ) *
        (etaNormalizedHeatKernel h (w - (t + u) / 2) : ℂ)) := by
    funext w
    rw [pairedEtaFullTwoHeatKernel_same_phase, pairedEtaFullTwoHeatEnvelope_eq_midpoint hh]
    simp [etaTiltedHeatEnvelope, pairedEtaHeatPhaseUnit]
  rw [he, integral_const_mul, integral_complex_ofReal]
  change (pairedEtaZeroTiltGapNormalization h : ℂ) *
    ((etaNormalizedHeatKernel (2 * h) (u - t) : ℂ) *
      (pairedEtaGaussianGapMass h ((t + u) / 2) : ℂ)) = _
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  unfold pairedEtaZeroTiltGapNormalization pairedEtaZeroTiltGapMultiplier
  rw [show 4 * Real.sqrt Real.pi * h / pairedEtaGaussianGapMass h 0 *
      (etaNormalizedHeatKernel (2 * h) (u - t) * pairedEtaGaussianGapMass h ((t + u) / 2)) =
      ((4 * Real.sqrt Real.pi * h) * etaNormalizedHeatKernel (2 * h) (u - t)) *
        (pairedEtaGaussianGapMass h ((t + u) / 2) / pairedEtaGaussianGapMass h 0) by ring,
    etaNormalizedHeatKernel_double_width_scaled hh]

/-- The normalized shifted gap mass has a quantitative translation error. -/
theorem pairedEtaGaussianGapMass_ratio_error_le {h c : ℝ} (hh : 2 ≤ h) (hc : 0 ≤ c) :
    |pairedEtaGaussianGapMass h c / pairedEtaGaussianGapMass h 0 - 1| ≤
      12 * c / (Real.sqrt Real.pi * h) := by
  have hh0 : 0 < h := lt_of_lt_of_le (by norm_num) hh
  have hg := pairedEtaGaussianGapMass_pos hh0 0
  rw [div_sub_one hg.ne', abs_div, abs_of_pos hg]
  calc
    _ ≤ (3 * c / (2 * Real.sqrt Real.pi * h)) / pairedEtaGaussianGapMass h 0 :=
      div_le_div_of_nonneg_right (pairedEtaGaussianGapMass_sub_zero_le hh0 hc) hg.le
    _ ≤ (3 * c / (2 * Real.sqrt Real.pi * h)) / (1 / 8) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (pairedEtaGaussianGapMass_zero_ge_eighth hh)
    _ = _ := by ring

/-- The exact endpoint separation and midpoint shift give independent
quantitative costs in reconstructing one from the actual gap multiplier. -/
theorem pairedEtaZeroTiltGapMultiplier_error_le {h t u : ℝ} (hh : 2 ≤ h)
    (ht : 0 ≤ t) (hu : 0 ≤ u) :
    |pairedEtaZeroTiltGapMultiplier h t u - 1| ≤
      12 * ((t + u) / 2) / (Real.sqrt Real.pi * h) + (u - t) ^ 2 / (16 * h ^ 2) := by
  have he : Real.exp (-((u - t) ^ 2 / (16 * h ^ 2))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have herr : |Real.exp (-((u - t) ^ 2 / (16 * h ^ 2))) - 1| ≤ (u - t) ^ 2 / (16 * h ^ 2) := by
    rw [abs_of_nonpos (sub_nonpos.mpr he)]
    have hexp := Real.add_one_le_exp (-((u - t) ^ 2 / (16 * h ^ 2)))
    linarith
  calc
    _ = |Real.exp (-((u - t) ^ 2 / (16 * h ^ 2))) *
        (pairedEtaGaussianGapMass h ((t + u) / 2) / pairedEtaGaussianGapMass h 0 - 1) +
        (Real.exp (-((u - t) ^ 2 / (16 * h ^ 2))) - 1)| := by
      unfold pairedEtaZeroTiltGapMultiplier
      congr 1
      ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add
      (by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact (mul_le_of_le_one_left (abs_nonneg _) he).trans
          (pairedEtaGaussianGapMass_ratio_error_le hh (by positivity))) herr)

/-- The zero-tilt reconstruction error is uniform on the physical window,
with a polynomial endpoint cost and only inverse heat width. -/
theorem pairedEtaZeroTiltGapMultiplier_window_error_le {h L t u : ℝ}
    (hh : 2 ≤ h) (ht : t ∈ Icc 0 L) (hu : u ∈ Icc 0 L) :
    |pairedEtaZeroTiltGapMultiplier h t u - 1| ≤ 13 * (1 + L) ^ 2 / h := by
  have hh0 : 0 < h := lt_of_lt_of_le (by norm_num) hh
  have hL : 0 ≤ L := ht.1.trans ht.2
  have hsqrt : 1 ≤ Real.sqrt Real.pi := Real.one_le_sqrt.mpr (by linarith [Real.pi_gt_three])
  have hc : (t + u) / 2 ≤ L := by linarith [ht.2, hu.2]
  have hd : (u - t) ^ 2 ≤ L ^ 2 := by
    have hmul : 0 ≤ (L - (u - t)) * (L + (u - t)) := mul_nonneg (by linarith [ht.1, hu.2]) (by linarith [hu.1, ht.2])
    nlinarith
  have hfirst : 12 * ((t + u) / 2) / (Real.sqrt Real.pi * h) ≤ 12 * L / h :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num)) (by positivity)).trans
      (div_le_div_of_nonneg_left (by positivity) hh0 (by nlinarith))
  have hsecond : (u - t) ^ 2 / (16 * h ^ 2) ≤ L ^ 2 / h :=
    (div_le_div_of_nonneg_right hd (by positivity)).trans
      (div_le_div_of_nonneg_left (sq_nonneg L) hh0 (by nlinarith))
  calc
    _ ≤ 12 * L / h + L ^ 2 / h :=
      (pairedEtaZeroTiltGapMultiplier_error_le hh ht.1 hu.1).trans (add_le_add hfirst hsecond)
    _ = (12 * L + L ^ 2) / h := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [sq_nonneg L]) hh0.le

end

end RiemannGaussian
