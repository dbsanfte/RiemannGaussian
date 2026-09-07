import RiemannGaussian.EtaPhaseProjectionBound

/-!
# Actual zero margins from the phase-matched eta projection

The boundary eta value determines a literal horizontal zero margin.
Reflection applies the same value at the identical ordinate to both strip
edges. No approximation or unknown norm bound is a theorem premise.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The boundary phase retains its exact quotient by the complex spectral parameter. -/
theorem pairedEtaPhaseBoundaryValue_eq_core_div (y : ℝ) :
    pairedEtaPhaseBoundaryValue y = pairedEtaCore (1 + (y : ℂ) * Complex.I) /
      (1 + (y : ℂ) * Complex.I) := by
  rw [pairedEtaPhaseBoundaryValue,
    ← integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition (by norm_num),
    integral_exp_neg_mul_pairedEtaLogMeasure_eq_pairedEtaCore_div (by norm_num)]

/-- The boundary eta transform has at most unit norm, from the full positive-half-line mass. -/
theorem norm_pairedEtaPhaseBoundaryValue_le_one (y : ℝ) : ‖pairedEtaPhaseBoundaryValue y‖ ≤ 1 := by
  rw [pairedEtaPhaseBoundaryValue,
    ← integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition (by norm_num)]
  have hmass : (∫ t : ℝ, Real.exp (-t) ∂pairedEtaLogMeasure) ≤ 1 := by
    have h := integral_etaPhaseProjectionBase_sq_le_one
    have he (t : ℝ) : Real.exp (-(1 / 2) * t) ^ 2 = Real.exp (-t) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    simpa only [he] using h
  apply (norm_integral_le_integral_norm _).trans
  have he : (fun t : ℝ ↦ ‖Complex.exp (-(1 + (y : ℂ) * Complex.I) * t)‖) =
      fun t ↦ Real.exp (-t) := by
    funext t
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  simpa only [he] using hmass

/-- The actual positive eta support bounds every boundary phase by its zero-frequency mass. -/
theorem norm_pairedEtaPhaseBoundaryValue_le_zero (y : ℝ) :
    ‖pairedEtaPhaseBoundaryValue y‖ ≤ ‖pairedEtaPhaseBoundaryValue 0‖ := by
  have hmass : pairedEtaPhaseBoundaryValue 0 =
      ((∫ t : ℝ, Real.exp (-t) ∂pairedEtaLogMeasure : ℝ) : ℂ) := by
    rw [pairedEtaPhaseBoundaryValue,
      ← integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition (by norm_num)]
    simp only [Complex.ofReal_zero, zero_mul, add_zero, neg_mul, one_mul]
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    exact Eventually.of_forall fun t ↦ by simp
  rw [hmass, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun t ↦ (Real.exp_pos (-t)).le)),
    pairedEtaPhaseBoundaryValue,
    ← integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition (by norm_num)]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  exact Eventually.of_forall fun t ↦ by
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- The actual phase projection's horizontal margin at each ordinate. -/
def etaPhaseProjectionZeroMargin (y : ℝ) : ℝ :=
  ‖pairedEtaPhaseBoundaryValue y‖ / (1 + ‖pairedEtaPhaseBoundaryValue y‖)

/-- The margin is nonnegative, and its denominator is always strictly positive. -/
theorem etaPhaseProjectionZeroMargin_nonneg (y : ℝ) : 0 ≤ etaPhaseProjectionZeroMargin y := by
  unfold etaPhaseProjectionZeroMargin
  positivity

/-- The boundary norm keeps the margin within the natural half-strip. -/
theorem etaPhaseProjectionZeroMargin_le_half (y : ℝ) : etaPhaseProjectionZeroMargin y ≤ 1 / 2 := by
  unfold etaPhaseProjectionZeroMargin
  rw [div_le_iff₀ (by positivity)]
  linarith [norm_pairedEtaPhaseBoundaryValue_le_one y]

/-- The actual zero condition and the proved projection budget give the right boundary margin. -/
theorem etaPhaseProjectionZeroMargin_le_one_sub_re (rho : NontrivialZetaZero) :
    etaPhaseProjectionZeroMargin rho.1.im ≤ 1 - rho.1.re := by
  by_cases hb : 1 / 2 < rho.1.re
  · have h := norm_pairedEtaPhaseBoundaryValue_le_zero_ratio rho hb
    have hm := (le_div_iff₀ (NontrivialZetaZero.zero_lt_re rho)).mp h
    unfold etaPhaseProjectionZeroMargin
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · exact (etaPhaseProjectionZeroMargin_le_half rho.1.im).trans (by linarith)

/-- Completion reflection gives the same actual phase margin at the left boundary. -/
theorem etaPhaseProjectionZeroMargin_le_re (rho : NontrivialZetaZero) :
    etaPhaseProjectionZeroMargin rho.1.im ≤ rho.1.re := by
  have h := etaPhaseProjectionZeroMargin_le_one_sub_re (NontrivialZetaZero.conjugatePartner rho)
  simpa only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re, Complex.one_re,
    Complex.conj_re, Complex.sub_im, Complex.one_im, Complex.conj_im,
    sub_neg_eq_add, zero_add, sub_sub_cancel] using h

/-- Every literal nontrivial zero lies in the strip determined by its actual ordinate's eta boundary value. -/
theorem nontrivialZetaZero_mem_etaPhaseProjection_strip (rho : NontrivialZetaZero) :
    rho.1.re ∈ Icc (etaPhaseProjectionZeroMargin rho.1.im) (1 - etaPhaseProjectionZeroMargin rho.1.im) :=
  ⟨etaPhaseProjectionZeroMargin_le_re rho, by linarith [etaPhaseProjectionZeroMargin_le_one_sub_re rho]⟩

end

end RiemannGaussian
