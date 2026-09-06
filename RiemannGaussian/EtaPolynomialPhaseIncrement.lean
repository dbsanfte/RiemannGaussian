import RiemannGaussian.EtaPolynomialBoundaryTest
import RiemannGaussian.EtaCubicPhaseIncrement

/-!
# A second-order comparison for the actual polynomial phase

The quadratic term closes the velocity family under reflection. The exact
increment is retained before bounding its remainder by `h/R`, which is
strictly smaller than the heat width in the logarithmic limit.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The actual phase includes the quadratic term required by logarithmic reflection. -/
def pairedEtaCriticalPolynomialPhase (kappa beta alpha h R t : ℝ) : ℝ :=
  kappa * t / h + beta * t ^ 2 / (2 * h * R) + alpha * t ^ 3 / (h * R ^ 2)

/-- The full polynomial phase is continuous for every fixed set of parameters. -/
theorem continuous_pairedEtaCriticalPolynomialPhase (kappa beta alpha h R : ℝ) :
    Continuous (pairedEtaCriticalPolynomialPhase kappa beta alpha h R) := by
  unfold pairedEtaCriticalPolynomialPhase
  fun_prop

/-- Setting the quadratic coefficient to zero recovers the original cubic phase exactly. -/
theorem pairedEtaCriticalPolynomialPhase_cubic (kappa alpha h R : ℝ) :
    pairedEtaCriticalPolynomialPhase kappa 0 alpha h R = pairedEtaCriticalCubicPhase kappa alpha h R := by
  funext t
  simp only [pairedEtaCriticalPolynomialPhase, pairedEtaCriticalCubicPhase, zero_mul, zero_div, add_zero]

/-- The exact increment retains both signed quadratic and cubic remainder terms. -/
theorem pairedEtaCriticalPolynomialPhase_increment {h R : ℝ} (hh : h ≠ 0) (hR : R ≠ 0)
    (kappa beta alpha v t : ℝ) :
    pairedEtaCriticalPolynomialPhase kappa beta alpha h R (t + h * v) -
        pairedEtaCriticalPolynomialPhase kappa beta alpha h R t =
      v * pairedEtaPolynomialVelocity kappa beta alpha (t / R) +
        (h / R) * v ^ 2 * (beta / 2 + alpha * (3 * t + h * v) / R) := by
  unfold pairedEtaCriticalPolynomialPhase pairedEtaPolynomialVelocity
  field_simp
  ring

/-- The local phase remainder has a factor `h/R`, preserving the precision
needed to extract a finite part after division by `h`. -/
theorem pairedEtaCriticalPolynomialPhase_increment_error_le {h R v t : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hR : 1 ≤ R) (hv : 0 ≤ v)
    (ht : t ∈ Icc (0 : ℝ) (2 * R)) (kappa beta alpha : ℝ) :
    |pairedEtaCriticalPolynomialPhase kappa beta alpha h R (t + h * v) -
      pairedEtaCriticalPolynomialPhase kappa beta alpha h R t -
        v * pairedEtaPolynomialVelocity kappa beta alpha (t / R)| ≤
      (h / R) * v ^ 2 * (|beta| + |alpha| * (6 + v)) := by
  have hR0 : 0 < R := by linarith
  have hnum : 0 ≤ 3 * t + h * v := by nlinarith [ht.1, mul_nonneg hh.le hv]
  have hfrac : (3 * t + h * v) / R ≤ 6 + v := by
    apply (div_le_iff₀ hR0).2
    have hhv : h * v ≤ v := mul_le_of_le_one_left hv hh1
    have hvR : v ≤ v * R := le_mul_of_one_le_right hv hR
    nlinarith [ht.2]
  have hinner : |beta / 2 + alpha * (3 * t + h * v) / R| ≤ |beta| + |alpha| * (6 + v) := by
    calc
      _ ≤ |beta / 2| + |alpha * (3 * t + h * v) / R| := abs_add_le _ _
      _ = |beta| / 2 + |alpha| * ((3 * t + h * v) / R) := by
        rw [abs_div, abs_div, abs_mul, abs_of_nonneg hnum, abs_of_pos hR0]
        norm_num
        ring
      _ ≤ _ := by
        have hf := mul_le_mul_of_nonneg_left hfrac (abs_nonneg alpha)
        linarith [abs_nonneg beta]
  rw [pairedEtaCriticalPolynomialPhase_increment hh.ne' hR0.ne', add_sub_cancel_left,
    abs_mul, abs_of_nonneg (by positivity : 0 ≤ h / R * v ^ 2)]
  exact mul_le_mul_of_nonneg_left hinner (by positivity)

/-- The complex kernel comparison retains the improved `h/R` factor on
the growing time interval and is uniform in the linear phase coefficient. -/
theorem pairedEtaPolynomialPhaseKernel_local_error_le {h R v t : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hR : 1 ≤ R) (hv : 0 ≤ v)
    (ht : t ∈ Icc (0 : ℝ) (2 * R)) (lambda kappa beta alpha : ℝ) :
    ‖pairedEtaShiftPhaseKernel (pairedEtaMovingCriticalTilt lambda R)
        (pairedEtaCriticalPolynomialPhase kappa beta alpha h R) (h * v) t -
      Real.exp (-t) • pairedEtaPolynomialBoundaryTestExtension lambda kappa beta alpha v (t / R)‖ ≤
      (Real.exp (4 * |lambda|) * ((h / R) * v ^ 2 * (|beta| + |alpha| * (6 + v)))) * Real.exp (-t) := by
  have hR0 : 0 < R := by linarith
  have hz : t / R ∈ Icc (0 : ℝ) 2 :=
    ⟨div_nonneg ht.1 hR0.le, (div_le_iff₀ hR0).2 ht.2⟩
  rw [pairedEtaPolynomialBoundaryTestExtension_eq hz, pairedEtaShiftPhaseKernel,
    pairedEtaPolynomialBoundaryTest, exp_pairedEtaMovingCriticalTilt,
    Complex.real_smul, Complex.ofReal_mul, ← mul_assoc, ← mul_sub,
    norm_mul, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < Real.exp (-t) * Real.exp (-2 * lambda * (t / R)))]
  have hp := (norm_exp_ofReal_mul_I_sub_le
    (pairedEtaCriticalPolynomialPhase kappa beta alpha h R (t + h * v) -
      pairedEtaCriticalPolynomialPhase kappa beta alpha h R t)
    (v * pairedEtaPolynomialVelocity kappa beta alpha (t / R))).trans
      (pairedEtaCriticalPolynomialPhase_increment_error_le hh hh1 hR hv ht kappa beta alpha)
  have he := exp_pairedEtaMovingCriticalTilt_le hR0 ht (lambda := lambda)
  rw [exp_pairedEtaMovingCriticalTilt] at he
  calc
    _ ≤ (Real.exp (4 * |lambda|) * Real.exp (-t)) *
        ((h / R) * v ^ 2 * (|beta| + |alpha| * (6 + v))) :=
      mul_le_mul he hp (norm_nonneg _) (by positivity)
    _ = _ := by ring

end

end RiemannGaussian
