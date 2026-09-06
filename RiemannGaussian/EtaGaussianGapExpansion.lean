import RiemannGaussian.EtaGaussianColourRemainder

/-!
# The evaluated broad-Gaussian expansion on the actual eta gap

The exact signed colour identity gives a first-order term with the Wallis
constant. A quantitative Gaussian Taylor estimate bounds the remainder
uniformly in the nonnegative center, without a density approximation.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The normalized Gaussian has a quadratic displacement error from its peak. -/
theorem etaNormalizedHeatKernel_sub_zero_le {h : ℝ} (hh : 0 < h) (r : ℝ) :
    |etaNormalizedHeatKernel h r - 1 / (2 * Real.sqrt Real.pi * h)| ≤
      r ^ 2 / (8 * Real.sqrt Real.pi * h ^ 3) := by
  have he : Real.exp (-(r ^ 2 / (4 * h ^ 2))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hb : 1 - Real.exp (-(r ^ 2 / (4 * h ^ 2))) ≤ r ^ 2 / (4 * h ^ 2) := by
    have hx := Real.add_one_le_exp (-(r ^ 2 / (4 * h ^ 2)))
    linarith
  rw [etaNormalizedHeatKernel_eq_quadratic hh,
    show -(1 / (4 * h ^ 2)) * r ^ 2 = -(r ^ 2 / (4 * h ^ 2)) by ring,
    ← sub_div, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.sqrt Real.pi * h),
    abs_of_nonpos (sub_nonpos.mpr he)]
  calc
    _ ≤ (r ^ 2 / (4 * h ^ 2)) / (2 * Real.sqrt Real.pi * h) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

/-- The finite positive Gaussian mass has an explicit cubic endpoint error. -/
theorem integral_etaNormalizedHeatKernel_sub_peak_le {h c : ℝ} (hh : 0 < h) (hc : 0 ≤ c) :
    |(∫ w in (0 : ℝ)..c, etaNormalizedHeatKernel h w) - c / (2 * Real.sqrt Real.pi * h)| ≤
      c ^ 3 / (8 * Real.sqrt Real.pi * h ^ 3) := by
  have hi : IntervalIntegrable (etaNormalizedHeatKernel h) volume 0 c := by
    apply Continuous.intervalIntegrable
    unfold etaNormalizedHeatKernel
    fun_prop
  have he : c / (2 * Real.sqrt Real.pi * h) =
      ∫ _w in (0 : ℝ)..c, 1 / (2 * Real.sqrt Real.pi * h) := by
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  rw [he, ← intervalIntegral.integral_sub hi intervalIntegrable_const]
  calc
    _ ≤ ∫ w in (0 : ℝ)..c, |etaNormalizedHeatKernel h w - 1 / (2 * Real.sqrt Real.pi * h)| :=
      intervalIntegral.abs_integral_le_integral_abs hc
    _ ≤ ∫ _w in (0 : ℝ)..c, c ^ 2 / (8 * Real.sqrt Real.pi * h ^ 3) := by
      apply intervalIntegral.integral_mono_on hc (hi.sub intervalIntegrable_const).abs intervalIntegrable_const
      intro w hw
      exact (etaNormalizedHeatKernel_sub_zero_le hh w).trans
        (div_le_div_of_nonneg_right (sq_le_sq₀ hw.1 hc |>.2 hw.2) (by positivity))
    _ = _ := by simp; ring

/-- The logarithmic Wallis endpoint lies between zero and one. -/
theorem etaWallisLog_bounds : 0 ≤ Real.log (Real.pi / 2) ∧ Real.log (Real.pi / 2) ≤ 1 := by
  constructor
  · exact Real.log_nonneg (by linarith [Real.pi_gt_three])
  · have he := Real.log_le_sub_one_of_pos (by positivity : 0 < Real.pi / 2)
    linarith [Real.pi_lt_four]

/-- The actual translated gap mass has its evaluated first broad-heat
coefficient and an explicit inverse-cubic-width remainder, uniformly in
every nonnegative center. -/
theorem pairedEtaGaussianGapMass_wallis_expansion_error_le {h c : ℝ} (hh : 0 < h) (hc : 0 ≤ c) :
    |pairedEtaGaussianGapMass h c - 1 / 4 - (c - Real.log (Real.pi / 2)) / (4 * Real.sqrt Real.pi * h)| ≤
      2 * (1 + c) ^ 3 / h ^ 3 := by
  have hlog := etaWallisLog_bounds
  have he : pairedEtaGaussianGapMass h c - 1 / 4 -
      (c - Real.log (Real.pi / 2)) / (4 * Real.sqrt Real.pi * h) =
      ((∫ w in (0 : ℝ)..c, etaNormalizedHeatKernel h w) - c / (2 * Real.sqrt Real.pi * h)) / 2 -
        Real.log (Real.pi / 2) * (etaNormalizedHeatKernel h c - 1 / (2 * Real.sqrt Real.pi * h)) / 2 +
        pairedEtaGaussianColourCorrection h c / 2 := by
    rw [pairedEtaGaussianGapMass_eq_colourCorrection hh hc]
    ring
  rw [he]
  have htri (a b d : ℝ) : |a - b + d| ≤ |a| + |b| + |d| := by
    exact (abs_add_le _ _).trans (add_le_add
      (by simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le a 0 b) le_rfl)
  calc
    _ ≤ |((∫ w in (0 : ℝ)..c, etaNormalizedHeatKernel h w) - c / (2 * Real.sqrt Real.pi * h)) / 2| +
        |Real.log (Real.pi / 2) * (etaNormalizedHeatKernel h c - 1 / (2 * Real.sqrt Real.pi * h)) / 2| +
        |pairedEtaGaussianColourCorrection h c / 2| := htri _ _ _
    _ ≤ (c ^ 3 / (8 * Real.sqrt Real.pi * h ^ 3)) / 2 +
        Real.log (Real.pi / 2) * (c ^ 2 / (8 * Real.sqrt Real.pi * h ^ 3)) / 2 +
        (9 * (1 + c) / (4 * Real.sqrt Real.pi * h ^ 3)) / 2 := by
      simp only [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_mul, abs_of_nonneg hlog.1]
      exact add_le_add (add_le_add
        (div_le_div_of_nonneg_right (integral_etaNormalizedHeatKernel_sub_peak_le hh hc) (by norm_num))
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (etaNormalizedHeatKernel_sub_zero_le hh c) hlog.1) (by norm_num)))
        (div_le_div_of_nonneg_right (pairedEtaGaussianColourCorrection_abs_le hh hc) (by norm_num))
    _ = (c ^ 3 + Real.log (Real.pi / 2) * c ^ 2 + 18 * (1 + c)) /
        (16 * Real.sqrt Real.pi * h ^ 3) := by ring
    _ ≤ (c ^ 3 + c ^ 2 + 18 * (1 + c)) / (16 * Real.sqrt Real.pi * h ^ 3) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right hlog.2 (sq_nonneg c)]
    _ ≤ (c ^ 3 + c ^ 2 + 18 * (1 + c)) / (16 * h ^ 3) := by
      have hs : 1 ≤ Real.sqrt Real.pi := Real.one_le_sqrt.mpr (by linarith [Real.pi_gt_three])
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have he := mul_le_mul_of_nonneg_right hs (show 0 ≤ 16 * h ^ 3 by positivity)
      nlinarith
    _ ≤ (32 * (1 + c) ^ 3) / (16 * h ^ 3) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [pow_nonneg hc 3]
    _ = _ := by ring

end

end RiemannGaussian
