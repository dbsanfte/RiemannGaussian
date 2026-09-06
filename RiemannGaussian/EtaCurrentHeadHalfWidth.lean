import RiemannGaussian.EtaCurrentReturnGrowth

/-!
# The actual simple-zero head and half the logarithmic cutoff step

The support head occupies almost half of its full support-plus-gap
logarithmic step. Its exact positive width discrepancy is one arithmetic
power smaller. This module keeps that discrepancy and the complex
exponential error separate before bounding the head Laplace moment.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The support-head width minus half the complete logarithmic step is
exactly a positive logarithmic second difference. -/
theorem pairedEtaShiftedLogHeadWidth_sub_half_step_eq (N : ℕ) :
    pairedEtaShiftedLogHeadWidth (N + 1) - pairedEtaLogTailShiftIncrement (N + 1) / 2 =
      Real.log (1 + 1 / ((((2 * (N + 1) + 1 : ℕ) : ℝ)) * (((2 * (N + 1) + 3 : ℕ) : ℝ)))) / 2 := by
  let q : ℝ := ((2 * (N + 1) + 1 : ℕ) : ℝ)
  have hq : 0 < q := by dsimp [q]; positivity
  have hw : pairedEtaShiftedLogHeadWidth (N + 1) = Real.log (q + 1) - Real.log q := by
    unfold pairedEtaShiftedLogHeadWidth pairedEtaLogTailCutoff q
    congr 2
    push_cast
    ring
  have hd : pairedEtaLogTailShiftIncrement (N + 1) = Real.log (q + 2) - Real.log q := by
    unfold pairedEtaLogTailShiftIncrement pairedEtaLogTailCutoff q
    congr 2
    push_cast
    ring
  have he : 1 + 1 / (q * (q + 2)) = (q + 1) ^ 2 / (q * (q + 2)) := by field_simp; ring
  have hq2 : (((2 * (N + 1) + 3 : ℕ) : ℝ)) = q + 2 := by dsimp [q]; push_cast; ring
  change _ = Real.log (1 + 1 / (q * (((2 * (N + 1) + 3 : ℕ) : ℝ)))) / 2
  rw [hw, hd, hq2, he, Real.log_div (by positivity) (by positivity),
    Real.log_pow, Real.log_mul hq.ne' (by positivity)]
  ring

/-- The exact head-width discrepancy is nonnegative and has an explicit
inverse-square arithmetic bound at every cutoff. -/
theorem pairedEtaShiftedLogHeadWidth_sub_half_step_bounds (N : ℕ) :
    0 ≤ pairedEtaShiftedLogHeadWidth (N + 1) - pairedEtaLogTailShiftIncrement (N + 1) / 2 ∧
      pairedEtaShiftedLogHeadWidth (N + 1) - pairedEtaLogTailShiftIncrement (N + 1) / 2 ≤
        1 / (2 * (N + 1 : ℝ) ^ 2) := by
  rw [pairedEtaShiftedLogHeadWidth_sub_half_step_eq]
  let q : ℝ := ((2 * (N + 1) + 1 : ℕ) : ℝ)
  let p : ℝ := ((2 * (N + 1) + 3 : ℕ) : ℝ)
  have hq : 0 < q := by dsimp [q]; positivity
  have hp : 0 < p := by dsimp [p]; positivity
  have hx : 0 < (N + 1 : ℝ) := by positivity
  have hxq : (N + 1 : ℝ) ≤ q := by dsimp [q]; exact_mod_cast (show N + 1 ≤ 2 * (N + 1) + 1 by omega)
  have hxp : (N + 1 : ℝ) ≤ p := by dsimp [p]; exact_mod_cast (show N + 1 ≤ 2 * (N + 1) + 3 by omega)
  change 0 ≤ Real.log (1 + 1 / (q * p)) / 2 ∧ Real.log (1 + 1 / (q * p)) / 2 ≤ _
  constructor
  · exact div_nonneg (Real.log_nonneg (le_add_of_nonneg_right (by positivity))) (by norm_num)
  · have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / (q * p))
    have hinv := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (N + 1 : ℝ) ^ 2)
      (show (N + 1 : ℝ) ^ 2 ≤ q * p by nlinarith)
    have hlog' : Real.log (1 + 1 / (q * p)) ≤ 1 / (q * p) := by linarith
    have hdiv := div_le_div_of_nonneg_right (hlog'.trans hinv)
      (by norm_num : (0 : ℝ) ≤ 2)
    exact hdiv.trans_eq (by rw [div_div, mul_comm ((N + 1 : ℝ) ^ 2) 2])

/-- A fixed finite constant bounds the exponential variation over every
actual head, whose complete successor step is at most one. -/
def pairedEtaCurrentHeadVariationConstant (rho : NontrivialZetaZero) : ℝ :=
  ‖rho.1‖ * Real.exp ‖rho.1‖

/-- The actual head variation constant is nonnegative. -/
theorem pairedEtaCurrentHeadVariationConstant_nonneg (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaCurrentHeadVariationConstant rho := by unfold pairedEtaCurrentHeadVariationConstant; positivity

/-- Complex exponential variation is controlled before taking any
completed-channel difference. The full ordinate remains in the constant. -/
theorem norm_pairedEtaCurrent_head_exp_sub_one_le (rho : NontrivialZetaZero) {u : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖Complex.exp (-rho.1 * (u : ℂ)) - 1‖ ≤ pairedEtaCurrentHeadVariationConstant rho * u := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (-rho.1 * (u : ℂ)) 1
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one,
    norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu] at h
  calc
    _ ≤ (‖rho.1‖ * u) * Real.exp (‖rho.1‖ * u) := h
    _ ≤ (‖rho.1‖ * u) * Real.exp ‖rho.1‖ :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_of_le_one_right (norm_nonneg _) hu1)) (by positivity)
    _ = _ := by unfold pairedEtaCurrentHeadVariationConstant; ring

/-- The actual order-zero shifted head differs from its width by the
integral of the exact complex exponential variation. -/
theorem pairedEtaShiftedLogHeadLaplaceMoment_zero_sub_width (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaShiftedLogHeadLaplaceMoment 0 rho.1 (N + 1) - (pairedEtaShiftedLogHeadWidth (N + 1) : ℂ) =
      ∫ u : ℝ, (Complex.exp (-rho.1 * (u : ℂ)) - 1) ∂pairedEtaShiftedLogHeadMeasure (N + 1) := by
  have hi : Integrable (fun u : ℝ ↦ Complex.exp (-rho.1 * (u : ℂ))) (pairedEtaShiftedLogHeadMeasure (N + 1)) := by
    simpa only [pow_zero, one_mul] using integrable_pairedEtaShiftedLogHeadLaplaceMoment_integrand 0
      (NontrivialZetaZero.zero_lt_re rho) (N + 1)
  unfold pairedEtaShiftedLogHeadLaplaceMoment
  simp only [pow_zero, one_mul]
  rw [pairedEtaShiftedLogHeadMeasure_eq_restrict_Ioc] at hi ⊢
  rw [integral_sub hi (integrable_const (1 : ℂ)), integral_const,
    measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le (pairedEtaShiftedLogHeadWidth_pos (N + 1)).le]
  simp only [Complex.real_smul, mul_one, sub_zero]

/-- The width error of the actual shifted head has a quadratic cutoff-step
bound, with genuine integrability and all complex phase variation retained. -/
theorem norm_pairedEtaShiftedLogHeadLaplaceMoment_zero_sub_width_le (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaShiftedLogHeadLaplaceMoment 0 rho.1 (N + 1) - (pairedEtaShiftedLogHeadWidth (N + 1) : ℂ)‖ ≤
      pairedEtaCurrentHeadVariationConstant rho * pairedEtaLogTailShiftIncrement (N + 1) ^ 2 := by
  have hw := (pairedEtaShiftedLogHeadWidth_pos (N + 1)).le
  have hwd := (pairedEtaShiftedLogHeadWidth_lt_shiftIncrement (N + 1)).le
  have hd := (pairedEtaLogTailShiftIncrement_pos (N + 1)).le
  have hK := pairedEtaCurrentHeadVariationConstant_nonneg rho
  rw [pairedEtaShiftedLogHeadLaplaceMoment_zero_sub_width, pairedEtaShiftedLogHeadMeasure_eq_restrict_Ioc]
  have hb : ∀ᵐ u : ℝ ∂volume.restrict (Ioc 0 (pairedEtaShiftedLogHeadWidth (N + 1))),
      ‖Complex.exp (-rho.1 * (u : ℂ)) - 1‖ ≤
        pairedEtaCurrentHeadVariationConstant rho * pairedEtaLogTailShiftIncrement (N + 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (norm_pairedEtaCurrent_head_exp_sub_one_le rho hu.1.le
      (hu.2.trans (hwd.trans (pairedEtaLogTailShiftIncrement_succ_le_one N)))).trans
        (mul_le_mul_of_nonneg_left (hu.2.trans hwd) hK)
  calc
    _ ≤ (pairedEtaCurrentHeadVariationConstant rho * pairedEtaLogTailShiftIncrement (N + 1)) *
        (volume.restrict (Ioc 0 (pairedEtaShiftedLogHeadWidth (N + 1)))).real univ :=
      norm_integral_le_of_norm_le_const hb
    _ = (pairedEtaCurrentHeadVariationConstant rho * pairedEtaLogTailShiftIncrement (N + 1)) *
        pairedEtaShiftedLogHeadWidth (N + 1) := by rw [measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le hw, sub_zero]
    _ ≤ (pairedEtaCurrentHeadVariationConstant rho * pairedEtaLogTailShiftIncrement (N + 1)) *
        pairedEtaLogTailShiftIncrement (N + 1) := mul_le_mul_of_nonneg_left hwd (mul_nonneg hK hd)
    _ = _ := by ring

end

end RiemannGaussian
