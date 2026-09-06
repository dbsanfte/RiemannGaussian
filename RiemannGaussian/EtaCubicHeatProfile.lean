import RiemannGaussian.EtaCubicMismatchLimit
import RiemannGaussian.EtaSupportGapGaussianProfile

/-!
# The limiting cubic-phase and moving-tilt Gaussian profile

The real heat profile is a named downstream projection of the retained
complex boundary test. Its defining integrals are measurable and genuinely
integrable, with bounds independent of the phase parameters.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The real limiting boundary profile at a fixed Gaussian coordinate. -/
def pairedEtaCubicBoundaryProfile (lambda kappa alpha v : ℝ) : ℝ :=
  ∫ z in 0..1, Real.exp (-2 * lambda * z) * Real.cos (v * (kappa + 3 * alpha * z ^ 2))

/-- The predicted joint critical cubic-phase and moving-tilt heat profile. -/
def pairedEtaCubicHeatProfile (lambda kappa alpha : ℝ) : ℝ :=
  (1 / Real.sqrt Real.pi) * ∫ v in Ioi 0,
    v * Real.exp (-(1 / 4) * v ^ 2) * pairedEtaCubicBoundaryProfile lambda kappa alpha v

/-- Taking the real part of the complex test gives exactly its cosine
projection, retaining the full nonlinear phase. -/
theorem pairedEtaCubicBoundaryTest_re (lambda kappa alpha v z : ℝ) :
    (pairedEtaCubicBoundaryTest lambda kappa alpha v z).re =
      Real.exp (-2 * lambda * z) * Real.cos (v * (kappa + 3 * alpha * z ^ 2)) := by
  simp only [pairedEtaCubicBoundaryTest, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, add_zero, mul_one, Real.exp_zero, one_mul]

/-- The real boundary profile is exactly the real part of the genuinely
integrable complex limiting boundary integral. -/
theorem integral_pairedEtaCubicBoundaryTest_re (lambda kappa alpha v : ℝ) :
    (∫ z in 0..1, pairedEtaCubicBoundaryTest lambda kappa alpha v z).re =
      pairedEtaCubicBoundaryProfile lambda kappa alpha v := by
  have h := intervalIntegral.intervalIntegral_re (μ := volume)
    ((contDiff_pairedEtaCubicBoundaryTest lambda kappa alpha v).continuous.intervalIntegrable 0 1)
  rw [RCLike.re_eq_complex_re] at h
  rw [← h]
  simp only [pairedEtaCubicBoundaryProfile, pairedEtaCubicBoundaryTest_re]

/-- The boundary profile is measurable in its Gaussian coordinate. -/
theorem measurable_pairedEtaCubicBoundaryProfile (lambda kappa alpha : ℝ) :
    Measurable (pairedEtaCubicBoundaryProfile lambda kappa alpha) := by
  have hm : Measurable (fun p : ℝ × ℝ ↦
      Real.exp (-2 * lambda * p.2) * Real.cos (p.1 * (kappa + 3 * alpha * p.2 ^ 2))) := by
    fun_prop
  unfold pairedEtaCubicBoundaryProfile
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact hm.stronglyMeasurable.integral_prod_right.measurable

/-- The real boundary profile has a bound independent of both phase
parameters and of the Gaussian coordinate. -/
theorem norm_pairedEtaCubicBoundaryProfile_le (lambda kappa alpha v : ℝ) :
    ‖pairedEtaCubicBoundaryProfile lambda kappa alpha v‖ ≤ Real.exp (4 * |lambda|) := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := fun z ↦
      Real.exp (-2 * lambda * z) * Real.cos (v * (kappa + 3 * alpha * z ^ 2)))
    (C := Real.exp (4 * |lambda|)) (by
      intro z hz
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hz
      rw [← pairedEtaCubicBoundaryTest_re, Real.norm_eq_abs]
      have h := norm_pairedEtaCubicBoundaryTestExtension_le lambda kappa alpha v z
      rw [pairedEtaCubicBoundaryTestExtension_eq ⟨hz.1.le, by linarith [hz.2]⟩] at h
      exact (Complex.abs_re_le_norm _).trans h)
  simpa only [pairedEtaCubicBoundaryProfile, sub_zero, abs_one, mul_one] using hb

/-- Genuine Gaussian integrability of the joint limiting profile. -/
theorem integrableOn_pairedEtaCubicHeatProfile_kernel (lambda kappa alpha : ℝ) :
    IntegrableOn (fun v ↦ v * Real.exp (-(1 / 4) * v ^ 2) *
      pairedEtaCubicBoundaryProfile lambda kappa alpha v) (Ioi 0) := by
  apply (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).integrableOn.mul_bdd
    (measurable_pairedEtaCubicBoundaryProfile lambda kappa alpha).aestronglyMeasurable
  exact Eventually.of_forall (norm_pairedEtaCubicBoundaryProfile_le lambda kappa alpha)

/-- The real part of the actual complex displacement limit is exactly the
real boundary profile used in the joint heat theorem. -/
theorem pairedEtaPhaseMismatch_cubic_movingTilt_re_tendsto (lambda kappa alpha : ℝ)
    {v : ℝ} (hv : 0 < v) :
    Tendsto (fun R : ℝ ↦
      (pairedEtaPhaseMismatch (pairedEtaMovingCriticalTilt lambda R)
        (pairedEtaCriticalCubicPhase kappa alpha (Real.exp (-R)) R) (Real.exp (-R) * v)).re /
          (Real.exp (-R) * R)) atTop (𝓝 (v * pairedEtaCubicBoundaryProfile lambda kappa alpha v)) := by
  have h := (Complex.continuous_re.tendsto _).comp
    (pairedEtaPhaseMismatch_cubic_movingTilt_tendsto lambda kappa alpha hv)
  simpa only [Function.comp_def, Complex.smul_re, smul_eq_mul, integral_pairedEtaCubicBoundaryTest_re,
    div_eq_mul_inv, mul_comm] using h

/-- Zero cubic modulation separates the moving-tilt mass from the original
linear phase profile, checking both the phase and Gaussian normalizations. -/
theorem pairedEtaCubicHeatProfile_linear (lambda kappa : ℝ) :
    pairedEtaCubicHeatProfile lambda kappa 0 =
      (∫ z in 0..1, Real.exp (-2 * lambda * z)) * pairedEtaHeatPhaseProfile kappa := by
  let A := ∫ z in 0..1, Real.exp (-2 * lambda * z)
  have hb (v : ℝ) : pairedEtaCubicBoundaryProfile lambda kappa 0 v = A * Real.cos (kappa * v) := by
    unfold pairedEtaCubicBoundaryProfile
    simp only [mul_zero, zero_mul, add_zero, intervalIntegral.integral_mul_const]
    rw [mul_comm v kappa]
  unfold pairedEtaCubicHeatProfile pairedEtaHeatPhaseProfile
  simp_rw [hb]
  have hfun : (fun v : ℝ ↦ v * Real.exp (-(1 / 4) * v ^ 2) * (A * Real.cos (kappa * v))) =
      (fun v ↦ A * (v * Real.exp (-(1 / 4) * v ^ 2) * Real.cos (kappa * v))) := by funext v; ring
  rw [hfun, integral_const_mul]
  dsimp [A]
  ring

/-- The uncoloured joint profile has the exact weighted critical coefficient. -/
theorem pairedEtaCubicHeatProfile_uncoloured (lambda : ℝ) :
    pairedEtaCubicHeatProfile lambda 0 0 =
      (2 / Real.sqrt Real.pi) * (∫ z in 0..1, Real.exp (-2 * lambda * z)) := by
  rw [pairedEtaCubicHeatProfile_linear, pairedEtaHeatPhaseProfile_zero, mul_comm]

/-- At zero moving tilt and zero cubic modulation, the joint profile
recovers the complete previously checked linear-phase profile. -/
theorem pairedEtaCubicHeatProfile_zero_tilt_linear (kappa : ℝ) :
    pairedEtaCubicHeatProfile 0 kappa 0 = pairedEtaHeatPhaseProfile kappa := by
  rw [pairedEtaCubicHeatProfile_linear]
  norm_num

end

end RiemannGaussian
