import RiemannGaussian.EtaPolynomialFinitePartDomination
import RiemannGaussian.EtaPolynomialHeatProfile
import RiemannGaussian.EtaCubicHeatLimit

/-!
# The second-order law for actual polynomial-phase eta heat

Dominated convergence applies after subtracting the leading term. The
polynomial majorant includes the actual phase error, the arithmetic tail,
and the moving horizontal damping. The limit is the evaluated pair of
endpoint Gaussian profiles, including its logarithmic moment.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Every nonnegative integral power is integrable against the heat Gaussian. -/
theorem integrableOn_pow_mul_etaHeatGaussian (n : ℕ) :
    IntegrableOn (fun v : ℝ ↦ v ^ n * Real.exp (-(1 / 4) * v ^ 2)) (Ioi 0) := by
  simpa only [Real.rpow_natCast] using
    integrableOn_rpow_mul_exp_neg_mul_sq (b := 1 / 4) (s := (n : ℝ)) (by norm_num)
      (by linarith [Nat.cast_nonneg (α := ℝ) n])

/-- The actual finite-part majorant is Gaussian-integrable, with all phase
and tilt parameters retained in its polynomial coefficients. -/
theorem integrableOn_etaPolynomialFinitePartGaussianBound (lambda beta alpha : ℝ) :
    IntegrableOn (fun v : ℝ ↦ Real.exp (-(1 / 4) * v ^ 2) *
      (pairedEtaPolynomialFinitePartBound lambda beta alpha v + Real.exp (4 * |lambda|) * v ^ 2)) (Ioi 0) := by
  let L := |lambda|
  let P := |beta| + 12 * |alpha|
  have h0 := (integrableOn_pow_mul_etaHeatGaussian 0).const_mul (4 + 8 * L)
  have h1 := (integrableOn_pow_mul_etaHeatGaussian 1).const_mul (12 + 8 * L + 4 * P)
  have h2 := (integrableOn_pow_mul_etaHeatGaussian 2).const_mul (9 + |beta| + 6 * |alpha| + 8 * L + 4 * P)
  have h3 := (integrableOn_pow_mul_etaHeatGaussian 3).const_mul (|alpha| + 4 * P)
  apply (((h0.add h1).add h2).add h3).const_mul (Real.exp (4 * |lambda|)) |>.congr
  exact Eventually.of_forall fun v ↦ by
    dsimp [L, P, pairedEtaPolynomialFinitePartBound]
    ring

/-- The real Gaussian integrand after subtracting the actual leading heat term. -/
def pairedEtaPolynomialHeatFinitePartKernel (lambda kappa beta alpha R v : ℝ) : ℝ :=
  Real.exp (-(1 / 4) * v ^ 2) *
    (Real.exp (-pairedEtaMovingCriticalTilt lambda R * (Real.exp (-R) * v)) *
      ((pairedEtaPhaseMismatch (pairedEtaMovingCriticalTilt lambda R)
        (pairedEtaCriticalPolynomialPhase kappa beta alpha (Real.exp (-R)) R) (Real.exp (-R) * v)).re /
          Real.exp (-R)) - (v * R) * pairedEtaPolynomialBoundaryProfile lambda kappa beta alpha v)

/-- The real integrand is an exact downstream projection of the retained
complex damped finite part. -/
theorem pairedEtaPolynomialHeatFinitePartKernel_eq_re (lambda kappa beta alpha R v : ℝ) :
    pairedEtaPolynomialHeatFinitePartKernel lambda kappa beta alpha R v =
      Real.exp (-(1 / 4) * v ^ 2) * (pairedEtaPolynomialDampedFinitePart lambda kappa beta alpha R v).re := by
  simp only [pairedEtaPolynomialHeatFinitePartKernel, pairedEtaPolynomialDampedFinitePart,
    Complex.sub_re, Complex.smul_re, smul_eq_mul, integral_pairedEtaPolynomialBoundaryTest_re]
  ring

/-- Measurability of the actual subtracted heat integrand in its Gaussian coordinate. -/
theorem measurable_pairedEtaPolynomialHeatFinitePartKernel (lambda kappa beta alpha R : ℝ) :
    Measurable (pairedEtaPolynomialHeatFinitePartKernel lambda kappa beta alpha R) := by
  have hD : Measurable (fun v : ℝ ↦ pairedEtaPhaseMismatch (pairedEtaMovingCriticalTilt lambda R)
      (pairedEtaCriticalPolynomialPhase kappa beta alpha (Real.exp (-R)) R) (Real.exp (-R) * v)) :=
    (measurable_pairedEtaPhaseMismatch
      (continuous_pairedEtaCriticalPolynomialPhase kappa beta alpha (Real.exp (-R)) R).measurable
      (pairedEtaMovingCriticalTilt lambda R)).comp (measurable_const.mul measurable_id)
  have hg : Measurable (fun v : ℝ ↦ Real.exp (-(1 / 4) * v ^ 2)) := by fun_prop
  have he : Measurable (fun v : ℝ ↦
      Real.exp (-pairedEtaMovingCriticalTilt lambda R * (Real.exp (-R) * v))) := by fun_prop
  exact hg.mul ((he.mul ((Complex.continuous_re.measurable.comp hD).div_const (Real.exp (-R)))).sub
    ((measurable_id.mul_const R).mul (measurable_pairedEtaPolynomialBoundaryProfile lambda kappa beta alpha)))

/-- A Gaussian-integrable bound for the actual subtracted heat integrand. -/
theorem norm_pairedEtaPolynomialHeatFinitePartKernel_le {lambda R v : ℝ}
    (hR : 1 ≤ R) (hlarge : 4 * |lambda| ≤ R) (hv : 0 < v) (kappa beta alpha : ℝ) :
    ‖pairedEtaPolynomialHeatFinitePartKernel lambda kappa beta alpha R v‖ ≤
      Real.exp (-(1 / 4) * v ^ 2) * (pairedEtaPolynomialFinitePartBound lambda beta alpha v +
        Real.exp (4 * |lambda|) * v ^ 2) := by
  rw [pairedEtaPolynomialHeatFinitePartKernel_eq_re, norm_mul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans
    (norm_pairedEtaPolynomialDampedFinitePart_le hR hlarge hv kappa beta alpha)) (Real.exp_pos _).le

/-- Genuine integrability of the actual finite-part heat integrand in the eventual range. -/
theorem integrableOn_pairedEtaPolynomialHeatFinitePartKernel {lambda R : ℝ}
    (hR : 1 ≤ R) (hlarge : 4 * |lambda| ≤ R) (kappa beta alpha : ℝ) :
    IntegrableOn (pairedEtaPolynomialHeatFinitePartKernel lambda kappa beta alpha R) (Ioi 0) := by
  apply (integrableOn_etaPolynomialFinitePartGaussianBound lambda beta alpha).mono'
    (measurable_pairedEtaPolynomialHeatFinitePartKernel lambda kappa beta alpha R).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact norm_pairedEtaPolynomialHeatFinitePartKernel_le hR hlarge hv kappa beta alpha

/-- The actual subtracted heat integrand has the evaluated endpoint limit. -/
theorem pairedEtaPolynomialHeatFinitePartKernel_tendsto (lambda kappa beta alpha : ℝ)
    {v : ℝ} (hv : 0 < v) :
    Tendsto (fun R : ℝ ↦ pairedEtaPolynomialHeatFinitePartKernel lambda kappa beta alpha R v) atTop
      (𝓝 (Real.exp (-(1 / 4) * v ^ 2) * pairedEtaPolynomialEndpointProfile lambda kappa beta alpha v)) := by
  have h := (Complex.continuous_re.tendsto _).comp
    (pairedEtaPolynomialDampedFinitePart_tendsto lambda kappa beta alpha hv)
  simp only [Function.comp_def, pairedEtaPolynomialEndpointProfile_eq_re] at h
  simpa only [pairedEtaPolynomialHeatFinitePartKernel_eq_re] using
    h.const_mul (Real.exp (-(1 / 4) * v ^ 2))

/-- Dominated convergence after subtraction yields the complete second-order
Gaussian integral; every domination and measurability premise is discharged. -/
theorem integral_pairedEtaPolynomialHeatFinitePartKernel_tendsto (lambda kappa beta alpha : ℝ) :
    Tendsto (fun R : ℝ ↦ ∫ v in Ioi 0, pairedEtaPolynomialHeatFinitePartKernel lambda kappa beta alpha R v) atTop
      (𝓝 (∫ v in Ioi 0, Real.exp (-(1 / 4) * v ^ 2) * pairedEtaPolynomialEndpointProfile lambda kappa beta alpha v)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun v ↦ Real.exp (-(1 / 4) * v ^ 2) * (pairedEtaPolynomialFinitePartBound lambda beta alpha v +
      Real.exp (4 * |lambda|) * v ^ 2))
  · exact Eventually.of_forall fun R ↦
      (measurable_pairedEtaPolynomialHeatFinitePartKernel lambda kappa beta alpha R).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (4 * |lambda|)] with R hR hlarge
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact norm_pairedEtaPolynomialHeatFinitePartKernel_le hR hlarge hv kappa beta alpha
  · exact integrableOn_etaPolynomialFinitePartGaussianBound lambda beta alpha
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact pairedEtaPolynomialHeatFinitePartKernel_tendsto lambda kappa beta alpha hv

/-- The literal continuous heat finite part is exactly the integral used
by the subtracted dominated convergence argument. -/
theorem pairedEtaSupportGapGaussianLeakage_polynomial_finite_part_eq_scaled {lambda R : ℝ}
    (hR : 1 ≤ R) (hlarge : 4 * |lambda| ≤ R) (kappa beta alpha : ℝ) :
    pairedEtaSupportGapGaussianLeakage (pairedEtaMovingCriticalTilt lambda R) (Real.exp (-R))
      (pairedEtaCriticalPolynomialPhase kappa beta alpha (Real.exp (-R)) R) / Real.exp (-R) -
        R * pairedEtaPolynomialHeatProfile lambda kappa beta alpha =
      (1 / Real.sqrt Real.pi) * ∫ v in Ioi 0,
        pairedEtaPolynomialHeatFinitePartKernel lambda kappa beta alpha R v := by
  let h := Real.exp (-R)
  let sigma := pairedEtaMovingCriticalTilt lambda R
  let phi := pairedEtaCriticalPolynomialPhase kappa beta alpha h R
  let f : ℝ → ℝ := fun v ↦ Real.exp (-(1 / 4) * v ^ 2) * Real.exp (-sigma * (h * v)) *
    (pairedEtaPhaseMismatch sigma phi (h * v)).re
  let g : ℝ → ℝ := fun v ↦ v * Real.exp (-(1 / 4) * v ^ 2) *
    pairedEtaPolynomialBoundaryProfile lambda kappa beta alpha v
  have hg : IntegrableOn g (Ioi 0) := integrableOn_pairedEtaPolynomialHeatProfile_kernel lambda kappa beta alpha
  have hf : IntegrableOn (fun v ↦ h⁻¹ * f v) (Ioi 0) := by
    apply ((integrableOn_pairedEtaPolynomialHeatFinitePartKernel hR hlarge kappa beta alpha).add
      (hg.const_mul R)).congr
    exact Eventually.of_forall fun v ↦ by
      dsimp [pairedEtaPolynomialHeatFinitePartKernel, f, g, h, sigma, phi]
      ring
  have hi : (∫ v in Ioi 0, pairedEtaPolynomialHeatFinitePartKernel lambda kappa beta alpha R v) =
      h⁻¹ * (∫ v in Ioi 0, f v) - R * (∫ v in Ioi 0, g v) := by
    calc
      _ = ∫ v in Ioi 0, h⁻¹ * f v - R * g v := by
        apply integral_congr_ae
        exact Eventually.of_forall fun v ↦ by
          dsimp [pairedEtaPolynomialHeatFinitePartKernel, f, g, h, sigma, phi]
          ring
      _ = _ := by rw [integral_sub hf (hg.const_mul R), integral_const_mul, integral_const_mul]
  have hs : 0 < sigma := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4)
    (pairedEtaMovingCriticalTilt_lower (by linarith) hlarge)
  rw [hi, pairedEtaSupportGapGaussianLeakage_eq_scaled_displacement hs (Real.exp_pos _)
    (continuous_pairedEtaCriticalPolynomialPhase kappa beta alpha h R).measurable]
  dsimp [f, g, h, sigma, phi, pairedEtaPolynomialHeatProfile]
  ring

/-- The full second-order Gaussian heat law for the actual eta support/gap
carrier and the reflection-closed polynomial phase family. -/
theorem pairedEtaSupportGapGaussianLeakage_polynomial_finite_part_exp_tendsto (lambda kappa beta alpha : ℝ) :
    Tendsto (fun R : ℝ ↦
      pairedEtaSupportGapGaussianLeakage (pairedEtaMovingCriticalTilt lambda R) (Real.exp (-R))
        (pairedEtaCriticalPolynomialPhase kappa beta alpha (Real.exp (-R)) R) / Real.exp (-R) -
          R * pairedEtaPolynomialHeatProfile lambda kappa beta alpha) atTop
      (𝓝 (pairedEtaPolynomialHeatFinitePart lambda kappa beta alpha)) := by
  have h := (integral_pairedEtaPolynomialHeatFinitePartKernel_tendsto lambda kappa beta alpha).const_mul
    (1 / Real.sqrt Real.pi)
  rw [integral_pairedEtaPolynomialEndpointProfile] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (4 * |lambda|)] with R hR hlarge
  exact (pairedEtaSupportGapGaussianLeakage_polynomial_finite_part_eq_scaled hR hlarge kappa beta alpha).symm

/-- The second-order heat law in the original positive width: subtracting
the logarithmic leading term leaves the explicit endpoint coefficient. -/
theorem pairedEtaSupportGapGaussianLeakage_polynomial_finite_part_tendsto (lambda kappa beta alpha : ℝ) :
    Tendsto (fun h : ℝ ↦
      pairedEtaSupportGapGaussianLeakage
        (pairedEtaMovingCriticalTilt lambda (Real.log (1 / h))) h
        (pairedEtaCriticalPolynomialPhase kappa beta alpha h (Real.log (1 / h))) / h -
          Real.log (1 / h) * pairedEtaPolynomialHeatProfile lambda kappa beta alpha) (𝓝[>] 0)
      (𝓝 (pairedEtaPolynomialHeatFinitePart lambda kappa beta alpha)) := by
  have h := (pairedEtaSupportGapGaussianLeakage_polynomial_finite_part_exp_tendsto lambda kappa beta alpha).comp
    tendsto_etaHeatLogScale_atTop
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : 0 < h := hh
  have he : Real.exp (-Real.log (1 / h)) = h := by
    rw [one_div, Real.log_inv, neg_neg, Real.exp_log hh0]
  simp only [Function.comp_def, he]

end

end RiemannGaussian
