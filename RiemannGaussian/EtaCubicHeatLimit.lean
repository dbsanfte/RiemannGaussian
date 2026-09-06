import RiemannGaussian.EtaMovingTiltGaussianBound
import RiemannGaussian.EtaCubicHeatProfile
import RiemannGaussian.EtaSupportGapGaussianLimit

/-!
# The joint cubic-phase and moving-tilt heat limit

A phase-uniform integrable majorant permits the actual complex-displacement
limit to pass through Gaussian averaging. The result is identified with the
literal continuous eta support/gap heat, with its normalization checked.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The normalized real Gaussian integrand of the actual cubic-phase
displacement at exponentially small heat width. -/
def pairedEtaCubicScaledHeatKernel (lambda kappa alpha R v : ℝ) : ℝ :=
  Real.exp (-(1 / 4) * v ^ 2) *
    Real.exp (-pairedEtaMovingCriticalTilt lambda R * (Real.exp (-R) * v)) *
    ((pairedEtaPhaseMismatch (pairedEtaMovingCriticalTilt lambda R)
      (pairedEtaCriticalCubicPhase kappa alpha (Real.exp (-R)) R) (Real.exp (-R) * v)).re /
        (Real.exp (-R) * R))

/-- Measurability of the actual normalized integrand in its Gaussian coordinate. -/
theorem measurable_pairedEtaCubicScaledHeatKernel (lambda kappa alpha R : ℝ) :
    Measurable (pairedEtaCubicScaledHeatKernel lambda kappa alpha R) := by
  have hD : Measurable (fun v : ℝ ↦ pairedEtaPhaseMismatch (pairedEtaMovingCriticalTilt lambda R)
      (pairedEtaCriticalCubicPhase kappa alpha (Real.exp (-R)) R) (Real.exp (-R) * v)) :=
    (measurable_pairedEtaPhaseMismatch
    (continuous_pairedEtaCriticalCubicPhase kappa alpha (Real.exp (-R)) R).measurable
    (pairedEtaMovingCriticalTilt lambda R)).comp (measurable_const.mul measurable_id)
  have hg : Measurable (fun v : ℝ ↦ Real.exp (-(1 / 4) * v ^ 2)) := by fun_prop
  have he : Measurable (fun v : ℝ ↦
      Real.exp (-pairedEtaMovingCriticalTilt lambda R * (Real.exp (-R) * v))) := by fun_prop
  exact (hg.mul he).mul ((Complex.continuous_re.measurable.comp hD).div_const (Real.exp (-R) * R))

/-- The actual normalized heat integrand has a Gaussian-integrable bound
independent of the phase parameters and the logarithmic scale. -/
theorem norm_pairedEtaCubicScaledHeatKernel_le {lambda R v : ℝ}
    (hR : 1 ≤ R) (hlarge : 4 * |lambda| ≤ R) (hv : 0 < v) (kappa alpha : ℝ) :
    ‖pairedEtaCubicScaledHeatKernel lambda kappa alpha R v‖ ≤
      Real.exp (-(1 / 4) * v ^ 2) * (Real.exp (4 * |lambda|) * (12 + 11 * v ^ 2)) := by
  let D := pairedEtaPhaseMismatch (pairedEtaMovingCriticalTilt lambda R)
    (pairedEtaCriticalCubicPhase kappa alpha (Real.exp (-R)) R) (Real.exp (-R) * v)
  have hreal : |D.re / (Real.exp (-R) * R)| ≤ Real.exp (4 * |lambda|) * (12 + 11 * v ^ 2) := by
    have h := Complex.abs_re_le_norm ((Real.exp (-R) * R)⁻¹ • D)
    simp only [Complex.smul_re, smul_eq_mul] at h
    rw [show D.re / (Real.exp (-R) * R) = (Real.exp (-R) * R)⁻¹ * D.re by ring]
    exact h.trans (norm_pairedEtaPhaseMismatch_movingTilt_scaled_le hR hlarge hv _)
  have hs : 0 < pairedEtaMovingCriticalTilt lambda R :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4)
      (pairedEtaMovingCriticalTilt_lower (by linarith) hlarge)
  have he : Real.exp (-pairedEtaMovingCriticalTilt lambda R * (Real.exp (-R) * v)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_pos (Real.exp_pos (-R)) hv])
  unfold pairedEtaCubicScaledHeatKernel
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-(1 / 4) * v ^ 2) * (Real.exp (4 * |lambda|) * (12 + 11 * v ^ 2)) :=
      mul_le_mul (mul_le_of_le_one_right (Real.exp_pos _).le he) hreal (abs_nonneg _) (Real.exp_pos _).le

/-- The polynomial majorant remains integrable after Gaussian weighting. -/
theorem integrableOn_etaMovingTiltGaussianBound (lambda : ℝ) :
    IntegrableOn (fun v : ℝ ↦ Real.exp (-(1 / 4) * v ^ 2) *
      (Real.exp (4 * |lambda|) * (12 + 11 * v ^ 2))) (Ioi 0) := by
  have hg : IntegrableOn (fun v : ℝ ↦ Real.exp (-(1 / 4) * v ^ 2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).integrableOn
  apply (((hg.const_mul 12).add (integrableOn_sq_mul_etaHeatGaussian.const_mul 11)).const_mul
    (Real.exp (4 * |lambda|))).congr
  exact Eventually.of_forall fun v ↦ by simp only [Pi.add_apply]; ring

/-- Genuine integrability of the actual normalized cubic heat integrand
throughout the eventual moving-tilt range. -/
theorem integrableOn_pairedEtaCubicScaledHeatKernel {lambda R : ℝ}
    (hR : 1 ≤ R) (hlarge : 4 * |lambda| ≤ R) (kappa alpha : ℝ) :
    IntegrableOn (pairedEtaCubicScaledHeatKernel lambda kappa alpha R) (Ioi 0) := by
  apply (integrableOn_etaMovingTiltGaussianBound lambda).mono'
    (measurable_pairedEtaCubicScaledHeatKernel lambda kappa alpha R).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact norm_pairedEtaCubicScaledHeatKernel_le hR hlarge hv kappa alpha

/-- Pointwise convergence of the actual Gaussian integrand, including its
moving horizontal damping. -/
theorem pairedEtaCubicScaledHeatKernel_tendsto (lambda kappa alpha : ℝ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun R ↦ pairedEtaCubicScaledHeatKernel lambda kappa alpha R v) atTop
      (𝓝 (v * Real.exp (-(1 / 4) * v ^ 2) * pairedEtaCubicBoundaryProfile lambda kappa alpha v)) := by
  have hs : Tendsto (pairedEtaMovingCriticalTilt lambda) atTop (𝓝 (1 / 2)) := by
    change Tendsto (fun R : ℝ ↦ 1 / 2 + lambda / R) atTop (𝓝 (1 / 2))
    have hfrac : Tendsto (fun R : ℝ ↦ lambda / R) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using
        (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ ↦ R⁻¹) atTop (𝓝 0)).const_mul lambda
    simpa only [add_zero] using hfrac.const_add (1 / 2 : ℝ)
  have he : Tendsto (fun R : ℝ ↦
      Real.exp (-pairedEtaMovingCriticalTilt lambda R * (Real.exp (-R) * v))) atTop (𝓝 1) := by
    have hi : Tendsto (fun R : ℝ ↦
        -pairedEtaMovingCriticalTilt lambda R * (Real.exp (-R) * v)) atTop (𝓝 0) := by
      simpa only [zero_mul, mul_zero] using hs.neg.mul (Real.tendsto_exp_neg_atTop_nhds_zero.mul_const v)
    simpa only [Function.comp_def, Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp hi
  have h := (he.const_mul (Real.exp (-(1 / 4) * v ^ 2))).mul
    (pairedEtaPhaseMismatch_cubic_movingTilt_re_tendsto lambda kappa alpha hv)
  simpa only [pairedEtaCubicScaledHeatKernel, mul_one, one_mul, mul_assoc, mul_left_comm, mul_comm] using h

/-- Gaussian dominated convergence for the actual normalized cubic heat
integrand, with all measurability and domination hypotheses discharged. -/
theorem integral_pairedEtaCubicScaledHeatKernel_tendsto (lambda kappa alpha : ℝ) :
    Tendsto (fun R : ℝ ↦ ∫ v in Ioi 0, pairedEtaCubicScaledHeatKernel lambda kappa alpha R v) atTop
      (𝓝 (∫ v in Ioi 0, v * Real.exp (-(1 / 4) * v ^ 2) *
        pairedEtaCubicBoundaryProfile lambda kappa alpha v)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun v ↦ Real.exp (-(1 / 4) * v ^ 2) * (Real.exp (4 * |lambda|) * (12 + 11 * v ^ 2)))
  · exact Eventually.of_forall fun R ↦
      (measurable_pairedEtaCubicScaledHeatKernel lambda kappa alpha R).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (4 * |lambda|)] with R hR hlarge
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact norm_pairedEtaCubicScaledHeatKernel_le hR hlarge hv kappa alpha
  · exact integrableOn_etaMovingTiltGaussianBound lambda
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact pairedEtaCubicScaledHeatKernel_tendsto lambda kappa alpha hv

/-- Rescaling the exact continuous eta heat/displacement identity preserves
an arbitrary measurable phase. -/
theorem pairedEtaSupportGapGaussianLeakage_eq_scaled_displacement {sigma h : ℝ}
    (hsigma : 0 < sigma) (hh : 0 < h) {phi : ℝ → ℝ} (hphi : Measurable phi) :
    pairedEtaSupportGapGaussianLeakage sigma h phi =
      (1 / Real.sqrt Real.pi) * ∫ v in Ioi 0,
        Real.exp (-(1 / 4) * v ^ 2) * Real.exp (-sigma * (h * v)) *
          (pairedEtaPhaseMismatch sigma phi (h * v)).re := by
  rw [pairedEtaSupportGapGaussianLeakage_eq_displacement hsigma hh hphi]
  let f : ℝ → ℝ := fun r ↦ etaNormalizedHeatKernel h r * Real.exp (-sigma * r) *
    (pairedEtaPhaseMismatch sigma phi r).re
  have hscale := integral_comp_mul_left_Ioi' f 0 hh
  simp only [mul_zero, smul_eq_mul] at hscale
  change 2 * (∫ r in Ioi 0, f r) = _
  rw [← hscale, show 2 * (h * ∫ v in Ioi 0, f (h * v)) =
    (2 * h) * ∫ v in Ioi 0, f (h * v) by ring, ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun v ↦ by
    dsimp [f, etaNormalizedHeatKernel]
    rw [show h * v / h = v by field_simp]
    have hsqrt : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    field_simp

/-- The actual continuous cubic heat is exactly the normalized displacement
integral used in the dominated convergence proof. -/
theorem pairedEtaSupportGapGaussianLeakage_cubic_eq_scaled {lambda R : ℝ}
    (hR : 1 ≤ R) (hlarge : 4 * |lambda| ≤ R) (kappa alpha : ℝ) :
    pairedEtaSupportGapGaussianLeakage (pairedEtaMovingCriticalTilt lambda R) (Real.exp (-R))
      (pairedEtaCriticalCubicPhase kappa alpha (Real.exp (-R)) R) / (Real.exp (-R) * R) =
      (1 / Real.sqrt Real.pi) * ∫ v in Ioi 0,
        pairedEtaCubicScaledHeatKernel lambda kappa alpha R v := by
  have hs : 0 < pairedEtaMovingCriticalTilt lambda R :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4)
      (pairedEtaMovingCriticalTilt_lower (by linarith) hlarge)
  rw [pairedEtaSupportGapGaussianLeakage_eq_scaled_displacement hs (Real.exp_pos _)
    (continuous_pairedEtaCriticalCubicPhase kappa alpha (Real.exp (-R)) R).measurable,
    mul_div_assoc]
  simp only [div_eq_mul_inv]
  rw [← integral_mul_const]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun v ↦ by
    simp only [pairedEtaCubicScaledHeatKernel, div_eq_mul_inv, mul_assoc]

/-- The full joint cubic-phase and moving-tilt heat law in logarithmic
coordinates, proved for the actual continuous eta support/gap kernel. -/
theorem pairedEtaSupportGapGaussianLeakage_cubic_movingTilt_exp_tendsto (lambda kappa alpha : ℝ) :
    Tendsto (fun R : ℝ ↦
      pairedEtaSupportGapGaussianLeakage (pairedEtaMovingCriticalTilt lambda R) (Real.exp (-R))
        (pairedEtaCriticalCubicPhase kappa alpha (Real.exp (-R)) R) / (Real.exp (-R) * R)) atTop
      (𝓝 (pairedEtaCubicHeatProfile lambda kappa alpha)) := by
  have h := (integral_pairedEtaCubicScaledHeatKernel_tendsto lambda kappa alpha).const_mul
    (1 / Real.sqrt Real.pi)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (4 * |lambda|)] with R hR hlarge
  exact (pairedEtaSupportGapGaussianLeakage_cubic_eq_scaled hR hlarge kappa alpha).symm

/-- The joint critical cubic-phase and moving-tilt theorem in the original
positive heat width, with the exact `h log(1/h)` normalization. -/
theorem pairedEtaSupportGapGaussianLeakage_cubic_movingTilt_tendsto (lambda kappa alpha : ℝ) :
    Tendsto (fun h : ℝ ↦
      pairedEtaSupportGapGaussianLeakage
        (pairedEtaMovingCriticalTilt lambda (Real.log (1 / h))) h
        (pairedEtaCriticalCubicPhase kappa alpha h (Real.log (1 / h))) /
          (h * Real.log (1 / h))) (𝓝[>] 0) (𝓝 (pairedEtaCubicHeatProfile lambda kappa alpha)) := by
  have h := (pairedEtaSupportGapGaussianLeakage_cubic_movingTilt_exp_tendsto lambda kappa alpha).comp
    tendsto_etaHeatLogScale_atTop
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : 0 < h := hh
  have he : Real.exp (-Real.log (1 / h)) = h := by
    rw [one_div, Real.log_inv, neg_neg, Real.exp_log hh0]
  simp only [Function.comp_def, he]

end

end RiemannGaussian
