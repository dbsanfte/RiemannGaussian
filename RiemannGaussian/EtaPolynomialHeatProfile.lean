import RiemannGaussian.EtaPolynomialMismatchFinitePart
import RiemannGaussian.EtaSupportGapGaussianProfile

/-!
# The polynomial heat profiles and their logarithmic endpoint moment

The leading profile retains the complete phase velocity. Its second-order
coefficient also uses the logarithmic Gaussian cosine moment, which is
proved genuinely integrable before any endpoint integral is separated.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The real limiting boundary profile at a fixed Gaussian coordinate. -/
def pairedEtaPolynomialBoundaryProfile (lambda kappa beta alpha v : ℝ) : ℝ :=
  ∫ z in 0..1, Real.exp (-2 * lambda * z) * Real.cos (v * (pairedEtaPolynomialVelocity kappa beta alpha z))

/-- The predicted joint critical polynomial-phase and moving-tilt heat profile. -/
def pairedEtaPolynomialHeatProfile (lambda kappa beta alpha : ℝ) : ℝ :=
  (1 / Real.sqrt Real.pi) * ∫ v in Ioi 0,
    v * Real.exp (-(1 / 4) * v ^ 2) * pairedEtaPolynomialBoundaryProfile lambda kappa beta alpha v

/-- Taking the real part of the complex test gives exactly its cosine
projection, retaining the full nonlinear phase. -/
theorem pairedEtaPolynomialBoundaryTest_re (lambda kappa beta alpha v z : ℝ) :
    (pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v z).re =
      Real.exp (-2 * lambda * z) * Real.cos (v * (pairedEtaPolynomialVelocity kappa beta alpha z)) := by
  simp only [pairedEtaPolynomialBoundaryTest, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, add_zero, mul_one, Real.exp_zero, one_mul]

/-- The real boundary profile is exactly the real part of the genuinely
integrable complex limiting boundary integral. -/
theorem integral_pairedEtaPolynomialBoundaryTest_re (lambda kappa beta alpha v : ℝ) :
    (∫ z in 0..1, pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v z).re =
      pairedEtaPolynomialBoundaryProfile lambda kappa beta alpha v := by
  have h := intervalIntegral.intervalIntegral_re (μ := volume)
    ((contDiff_pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v).continuous.intervalIntegrable 0 1)
  rw [RCLike.re_eq_complex_re] at h
  rw [← h]
  simp only [pairedEtaPolynomialBoundaryProfile, pairedEtaPolynomialBoundaryTest_re]

/-- The boundary profile is measurable in its Gaussian coordinate. -/
theorem measurable_pairedEtaPolynomialBoundaryProfile (lambda kappa beta alpha : ℝ) :
    Measurable (pairedEtaPolynomialBoundaryProfile lambda kappa beta alpha) := by
  have hm : Measurable (fun p : ℝ × ℝ ↦
      Real.exp (-2 * lambda * p.2) * Real.cos (p.1 * (pairedEtaPolynomialVelocity kappa beta alpha p.2))) := by
    unfold pairedEtaPolynomialVelocity
    fun_prop
  unfold pairedEtaPolynomialBoundaryProfile
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact hm.stronglyMeasurable.integral_prod_right.measurable

/-- The real boundary profile has a bound independent of both phase
parameters and of the Gaussian coordinate. -/
theorem norm_pairedEtaPolynomialBoundaryProfile_le (lambda kappa beta alpha v : ℝ) :
    ‖pairedEtaPolynomialBoundaryProfile lambda kappa beta alpha v‖ ≤ Real.exp (4 * |lambda|) := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := fun z ↦
      Real.exp (-2 * lambda * z) * Real.cos (v * (pairedEtaPolynomialVelocity kappa beta alpha z)))
    (C := Real.exp (4 * |lambda|)) (by
      intro z hz
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hz
      rw [← pairedEtaPolynomialBoundaryTest_re, Real.norm_eq_abs]
      have h := norm_pairedEtaPolynomialBoundaryTestExtension_le lambda kappa beta alpha v z
      rw [pairedEtaPolynomialBoundaryTestExtension_eq ⟨hz.1.le, by linarith [hz.2]⟩] at h
      exact (Complex.abs_re_le_norm _).trans h)
  simpa only [pairedEtaPolynomialBoundaryProfile, sub_zero, abs_one, mul_one] using hb

/-- Genuine Gaussian integrability of the joint limiting profile. -/
theorem integrableOn_pairedEtaPolynomialHeatProfile_kernel (lambda kappa beta alpha : ℝ) :
    IntegrableOn (fun v ↦ v * Real.exp (-(1 / 4) * v ^ 2) *
      pairedEtaPolynomialBoundaryProfile lambda kappa beta alpha v) (Ioi 0) := by
  apply (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).integrableOn.mul_bdd
    (measurable_pairedEtaPolynomialBoundaryProfile lambda kappa beta alpha).aestronglyMeasurable
  exact Eventually.of_forall (norm_pairedEtaPolynomialBoundaryProfile_le lambda kappa beta alpha)

/-- The logarithmic first Gaussian moment is genuinely integrable, including
the singular endpoint at zero. -/
theorem integrableOn_mul_log_etaHeatGaussian :
    IntegrableOn (fun v : ℝ ↦ v * Real.exp (-(1 / 4) * v ^ 2) * Real.log v) (Ioi 0) := by
  have hg := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).integrableOn (s := Ioi 0)
  apply (hg.add integrableOn_sq_mul_etaHeatGaussian).mono'
    (by fun_prop : AEStronglyMeasurable
      (fun v : ℝ ↦ v * Real.exp (-(1 / 4) * v ^ 2) * Real.log v) (volume.restrict (Ioi 0)))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : 0 < v := hv
  have h := mul_le_mul_of_nonneg_left (mul_abs_log_le_one_add_sq hv) (Real.exp_pos (-(1 / 4) * v ^ 2)).le
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_of_pos hv0, abs_of_pos (Real.exp_pos _)]
  nlinarith

/-- The logarithmic Gaussian cosine profile required by the upper endpoint. -/
def pairedEtaLogHeatPhaseProfile (kappa : ℝ) : ℝ :=
  (1 / Real.sqrt Real.pi) * ∫ v in Ioi 0,
    v * Real.exp (-(1 / 4) * v ^ 2) * Real.log v * Real.cos (kappa * v)

/-- Genuine integrability of the logarithmic Gaussian cosine kernel. -/
theorem integrableOn_pairedEtaLogHeatPhaseProfile_kernel (kappa : ℝ) :
    IntegrableOn (fun v : ℝ ↦ v * Real.exp (-(1 / 4) * v ^ 2) * Real.log v *
      Real.cos (kappa * v)) (Ioi 0) := by
  apply integrableOn_mul_log_etaHeatGaussian.mul_bdd (by fun_prop)
  exact Eventually.of_forall fun v ↦ by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (kappa * v)

/-- Reversing the phase leaves the logarithmic cosine profile unchanged. -/
theorem pairedEtaLogHeatPhaseProfile_neg (kappa : ℝ) :
    pairedEtaLogHeatPhaseProfile (-kappa) = pairedEtaLogHeatPhaseProfile kappa := by
  simp only [pairedEtaLogHeatPhaseProfile, neg_mul, Real.cos_neg]

/-- The explicit second-order heat coefficient retains the two different endpoint constants. -/
def pairedEtaPolynomialHeatFinitePart (lambda kappa beta alpha : ℝ) : ℝ :=
  (Real.eulerMascheroniConstant - 1) * pairedEtaHeatPhaseProfile kappa +
    Real.exp (-2 * lambda) * ((1 - Real.log (Real.pi / 2)) *
      pairedEtaHeatPhaseProfile (kappa + beta + 3 * alpha) -
        pairedEtaLogHeatPhaseProfile (kappa + beta + 3 * alpha))

/-- The unintegrated second-order real endpoint profile, including `-log(v)`. -/
def pairedEtaPolynomialEndpointProfile (lambda kappa beta alpha v : ℝ) : ℝ :=
  v * ((Real.eulerMascheroniConstant - 1) * Real.cos (kappa * v) +
    Real.exp (-2 * lambda) * (1 - Real.log (Real.pi / 2) - Real.log v) *
      Real.cos ((kappa + beta + 3 * alpha) * v))

/-- Taking the real part of the exact complex endpoint expression gives
the named endpoint profile, with every phase coefficient retained. -/
theorem pairedEtaPolynomialEndpointProfile_eq_re (lambda kappa beta alpha v : ℝ) :
    (v • ((Real.eulerMascheroniConstant - 1) • pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v 0 +
      (1 - Real.log (Real.pi / 2) - Real.log v) • pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v 1)).re =
      pairedEtaPolynomialEndpointProfile lambda kappa beta alpha v := by
  simp only [Complex.smul_re, smul_eq_mul, Complex.add_re, pairedEtaPolynomialBoundaryTest_re,
    pairedEtaPolynomialVelocity, mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero,
    Real.exp_zero, one_mul, one_pow, mul_one, pairedEtaPolynomialEndpointProfile]
  rw [mul_comm v kappa, mul_comm v (kappa + beta + 3 * alpha)]
  ring

/-- Exact separation of the endpoint Gaussian kernel retains its signed
logarithmic term before any integral is split. -/
theorem pairedEtaPolynomialEndpointProfile_kernel (lambda kappa beta alpha v : ℝ) :
    Real.exp (-(1 / 4) * v ^ 2) * pairedEtaPolynomialEndpointProfile lambda kappa beta alpha v =
      (Real.eulerMascheroniConstant - 1) * (v * Real.exp (-(1 / 4) * v ^ 2) * Real.cos (kappa * v)) +
      Real.exp (-2 * lambda) * ((1 - Real.log (Real.pi / 2)) *
        (v * Real.exp (-(1 / 4) * v ^ 2) * Real.cos ((kappa + beta + 3 * alpha) * v)) -
        v * Real.exp (-(1 / 4) * v ^ 2) * Real.log v * Real.cos ((kappa + beta + 3 * alpha) * v)) := by
  unfold pairedEtaPolynomialEndpointProfile
  ring

/-- The evaluated endpoint profile is genuinely integrable against the Gaussian. -/
theorem integrableOn_pairedEtaPolynomialEndpointProfile_kernel (lambda kappa beta alpha : ℝ) :
    IntegrableOn (fun v : ℝ ↦ Real.exp (-(1 / 4) * v ^ 2) *
      pairedEtaPolynomialEndpointProfile lambda kappa beta alpha v) (Ioi 0) := by
  have h0 := integrableOn_pairedEtaHeatPhaseProfile_kernel kappa
  have h1 := integrableOn_pairedEtaHeatPhaseProfile_kernel (kappa + beta + 3 * alpha)
  have hl := integrableOn_pairedEtaLogHeatPhaseProfile_kernel (kappa + beta + 3 * alpha)
  apply ((h0.const_mul (Real.eulerMascheroniConstant - 1)).add
    (((h1.const_mul (1 - Real.log (Real.pi / 2))).sub hl).const_mul (Real.exp (-2 * lambda)))).congr
  exact Eventually.of_forall fun v ↦ (pairedEtaPolynomialEndpointProfile_kernel lambda kappa beta alpha v).symm

/-- Gaussian integration evaluates the full endpoint coefficient in terms
of the original cosine profile and the logarithmic Gaussian profile. -/
theorem integral_pairedEtaPolynomialEndpointProfile (lambda kappa beta alpha : ℝ) :
    (1 / Real.sqrt Real.pi) * (∫ v in Ioi 0, Real.exp (-(1 / 4) * v ^ 2) *
      pairedEtaPolynomialEndpointProfile lambda kappa beta alpha v) =
      pairedEtaPolynomialHeatFinitePart lambda kappa beta alpha := by
  have h0 := integrableOn_pairedEtaHeatPhaseProfile_kernel kappa
  have h1 := integrableOn_pairedEtaHeatPhaseProfile_kernel (kappa + beta + 3 * alpha)
  have hl := integrableOn_pairedEtaLogHeatPhaseProfile_kernel (kappa + beta + 3 * alpha)
  simp_rw [pairedEtaPolynomialEndpointProfile_kernel]
  have hi := integral_add (h0.const_mul (Real.eulerMascheroniConstant - 1))
    (((h1.const_mul (1 - Real.log (Real.pi / 2))).sub hl).const_mul (Real.exp (-2 * lambda)))
  have hs := integral_sub (h1.const_mul (1 - Real.log (Real.pi / 2))) hl
  simp only [Pi.sub_apply] at hi hs
  rw [hi, integral_const_mul, integral_const_mul, hs, integral_const_mul]
  unfold pairedEtaPolynomialHeatFinitePart pairedEtaHeatPhaseProfile pairedEtaLogHeatPhaseProfile
  ring

/-- The actual polynomial-phase complex finite part has the prescribed real endpoint profile. -/
theorem pairedEtaPhaseMismatch_polynomial_finite_part_re_tendsto (lambda kappa beta alpha : ℝ)
    {v : ℝ} (hv : 0 < v) :
    Tendsto (fun R : ℝ ↦
      (pairedEtaPhaseMismatch (pairedEtaMovingCriticalTilt lambda R)
        (pairedEtaCriticalPolynomialPhase kappa beta alpha (Real.exp (-R)) R) (Real.exp (-R) * v)).re /
          Real.exp (-R) - (v * R) * pairedEtaPolynomialBoundaryProfile lambda kappa beta alpha v)
      atTop (𝓝 (pairedEtaPolynomialEndpointProfile lambda kappa beta alpha v)) := by
  have h := (Complex.continuous_re.tendsto _).comp
    (pairedEtaPhaseMismatch_polynomial_finite_part_tendsto lambda kappa beta alpha hv)
  simp only [Function.comp_def, pairedEtaPolynomialEndpointProfile_eq_re] at h
  simpa only [Complex.sub_re, Complex.smul_re, smul_eq_mul,
    integral_pairedEtaPolynomialBoundaryTest_re,
    div_eq_mul_inv, mul_comm] using h

/-- The leading boundary profile obeys the exact logarithmic reflection identity. -/
theorem pairedEtaPolynomialBoundaryProfile_reflection (lambda kappa beta alpha v : ℝ) :
    pairedEtaPolynomialBoundaryProfile lambda kappa beta alpha v = Real.exp (-2 * lambda) *
      pairedEtaPolynomialBoundaryProfile (-lambda) (kappa + beta + 3 * alpha) (-beta - 6 * alpha) alpha v := by
  have hi := intervalIntegral.integral_comp_sub_left
    (pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v) (a := 0) (b := 1) 1
  simp only [sub_self, sub_zero] at hi
  simp_rw [pairedEtaPolynomialBoundaryTest_reflection] at hi
  rw [intervalIntegral.integral_const_mul] at hi
  have hr := congrArg Complex.re hi
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    integral_pairedEtaPolynomialBoundaryTest_re] at hr
  exact hr.symm

/-- Gaussian integration preserves the exact leading-profile reflection,
providing the cancellation used by the signed second-order law. -/
theorem pairedEtaPolynomialHeatProfile_reflection (lambda kappa beta alpha : ℝ) :
    pairedEtaPolynomialHeatProfile lambda kappa beta alpha = Real.exp (-2 * lambda) *
      pairedEtaPolynomialHeatProfile (-lambda) (kappa + beta + 3 * alpha) (-beta - 6 * alpha) alpha := by
  unfold pairedEtaPolynomialHeatProfile
  simp_rw [pairedEtaPolynomialBoundaryProfile_reflection lambda kappa beta alpha]
  have hid (v : ℝ) : v * Real.exp (-(1 / 4) * v ^ 2) *
      (Real.exp (-2 * lambda) * pairedEtaPolynomialBoundaryProfile (-lambda)
        (kappa + beta + 3 * alpha) (-beta - 6 * alpha) alpha v) =
      Real.exp (-2 * lambda) * (v * Real.exp (-(1 / 4) * v ^ 2) *
        pairedEtaPolynomialBoundaryProfile (-lambda) (kappa + beta + 3 * alpha) (-beta - 6 * alpha) alpha v) := by ring
  simp_rw [hid]
  rw [integral_const_mul]
  ring

end

end RiemannGaussian
