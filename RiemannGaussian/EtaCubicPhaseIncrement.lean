import RiemannGaussian.EtaCubicBoundaryTest

/-!
# The actual cubic phase increment and moving critical tilt

Exact algebra identifies the limiting quadratic-in-logarithmic-time phase.
An explicit remainder controls the true phase on a growing time interval.
The moving tilt keeps its original exponential weight throughout.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- A horizontal tilt moving toward the critical value on logarithmic scale. -/
def pairedEtaMovingCriticalTilt (lambda R : ℝ) : ℝ := 1 / 2 + lambda / R

/-- The literal linear-plus-cubic phase at independent heat width and
logarithmic time scale. -/
def pairedEtaCriticalCubicPhase (kappa alpha h R t : ℝ) : ℝ :=
  kappa * t / h + alpha * t ^ 3 / (h * R ^ 2)

/-- The cubic modulation is a continuous, hence measurable, real phase. -/
theorem continuous_pairedEtaCriticalCubicPhase (kappa alpha h R : ℝ) :
    Continuous (pairedEtaCriticalCubicPhase kappa alpha h R) := by
  unfold pairedEtaCriticalCubicPhase
  fun_prop

/-- The exact cubic phase increment, including its signed remainder. -/
theorem pairedEtaCriticalCubicPhase_increment {h R : ℝ} (hh : h ≠ 0) (hR : R ≠ 0)
    (kappa alpha v t : ℝ) :
    pairedEtaCriticalCubicPhase kappa alpha h R (t + h * v) -
        pairedEtaCriticalCubicPhase kappa alpha h R t =
      v * (kappa + 3 * alpha * (t / R) ^ 2) +
        alpha * h * v ^ 2 * (3 * t + h * v) / R ^ 2 := by
  unfold pairedEtaCriticalCubicPhase
  field_simp
  ring

/-- A uniform phase-increment error on twice the logarithmic time scale.
The error retains its cubic parameter and Gaussian-coordinate dependence. -/
theorem pairedEtaCriticalCubicPhase_increment_error_le {h R v t : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hR : 1 ≤ R) (hv : 0 ≤ v)
    (ht : t ∈ Icc (0 : ℝ) (2 * R)) (kappa alpha : ℝ) :
    |pairedEtaCriticalCubicPhase kappa alpha h R (t + h * v) -
      pairedEtaCriticalCubicPhase kappa alpha h R t -
        v * (kappa + 3 * alpha * (t / R) ^ 2)| ≤
      |alpha| * h * v ^ 2 * (6 + v) := by
  have hR0 : 0 < R := by linarith
  rw [pairedEtaCriticalCubicPhase_increment hh.ne' hR0.ne', add_sub_cancel_left,
    abs_div, abs_mul, abs_mul, abs_mul, abs_of_pos hh, abs_of_nonneg (sq_nonneg v),
    abs_of_nonneg (by nlinarith [ht.1, mul_nonneg hh.le hv] : 0 ≤ 3 * t + h * v),
    abs_of_pos (sq_pos_of_pos hR0)]
  have hR2 : R ≤ R ^ 2 := by nlinarith
  have hR21 : 1 ≤ R ^ 2 := by nlinarith
  have hhv : h * v ≤ v := mul_le_of_le_one_left hv hh1
  have hvR := mul_le_mul_of_nonneg_left hR21 hv
  have hnum : 3 * t + h * v ≤ (6 + v) * R ^ 2 := by nlinarith [ht.2]
  calc
    _ = (|alpha| * h * v ^ 2) * ((3 * t + h * v) / R ^ 2) := by ring
    _ ≤ (|alpha| * h * v ^ 2) * (6 + v) := by
      exact mul_le_mul_of_nonneg_left ((div_le_iff₀ (sq_pos_of_pos hR0)).2 hnum) (by positivity)

/-- The moving tilt is uniformly positive once its logarithmic scale
dominates four times the tilt parameter. -/
theorem pairedEtaMovingCriticalTilt_lower {lambda R : ℝ} (hR : 0 < R)
    (hlarge : 4 * |lambda| ≤ R) : 1 / 4 ≤ pairedEtaMovingCriticalTilt lambda R := by
  have hfrac : -(1 / 4 : ℝ) ≤ lambda / R := by
    apply (le_div_iff₀ hR).2
    linarith [neg_abs_le lambda]
  unfold pairedEtaMovingCriticalTilt
  linarith

/-- Exact factorization of the moving exponential weight relative to the
critical weight, before any estimate or truncation. -/
theorem exp_pairedEtaMovingCriticalTilt (lambda R t : ℝ) :
    Real.exp (-(2 * pairedEtaMovingCriticalTilt lambda R) * t) =
      Real.exp (-t) * Real.exp (-2 * lambda * (t / R)) := by
  rw [← Real.exp_add]
  congr 1
  unfold pairedEtaMovingCriticalTilt
  ring

/-- A uniform tilt envelope on a bounded logarithmic time interval. -/
theorem exp_pairedEtaMovingCriticalTilt_le {lambda R t : ℝ} (hR : 0 < R)
    (ht : t ∈ Icc (0 : ℝ) (2 * R)) :
    Real.exp (-(2 * pairedEtaMovingCriticalTilt lambda R) * t) ≤
      Real.exp (4 * |lambda|) * Real.exp (-t) := by
  rw [exp_pairedEtaMovingCriticalTilt]
  have hz : t / R ∈ Icc (0 : ℝ) 2 :=
    ⟨div_nonneg ht.1 hR.le, (div_le_iff₀ hR).2 ht.2⟩
  have hbound : Real.exp (-2 * lambda * (t / R)) ≤ Real.exp (4 * |lambda|) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (neg_le_abs lambda) hz.1
    have h' := mul_le_mul_of_nonneg_left hz.2 (abs_nonneg lambda)
    nlinarith
  exact (mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le).trans_eq (mul_comm _ _)

/-- The complex phase kernel on the resolved growing interval differs
from the limiting cubic test by an explicit order-width envelope. -/
theorem pairedEtaCubicPhaseKernel_local_error_le {h R v t : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hR : 1 ≤ R) (hv : 0 ≤ v)
    (ht : t ∈ Icc (0 : ℝ) (2 * R)) (lambda kappa alpha : ℝ) :
    ‖pairedEtaShiftPhaseKernel (pairedEtaMovingCriticalTilt lambda R)
        (pairedEtaCriticalCubicPhase kappa alpha h R) (h * v) t -
      Real.exp (-t) • pairedEtaCubicBoundaryTestExtension lambda kappa alpha v (t / R)‖ ≤
      (Real.exp (4 * |lambda|) * (|alpha| * h * v ^ 2 * (6 + v))) * Real.exp (-t) := by
  have hR0 : 0 < R := by linarith
  have hz : t / R ∈ Icc (0 : ℝ) 2 :=
    ⟨div_nonneg ht.1 hR0.le, (div_le_iff₀ hR0).2 ht.2⟩
  rw [pairedEtaCubicBoundaryTestExtension_eq hz, pairedEtaShiftPhaseKernel,
    pairedEtaCubicBoundaryTest, exp_pairedEtaMovingCriticalTilt,
    Complex.real_smul, Complex.ofReal_mul, ← mul_assoc, ← mul_sub,
    norm_mul, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < Real.exp (-t) * Real.exp (-2 * lambda * (t / R)))]
  have hp := (norm_exp_ofReal_mul_I_sub_le
    (pairedEtaCriticalCubicPhase kappa alpha h R (t + h * v) -
      pairedEtaCriticalCubicPhase kappa alpha h R t)
    (v * (kappa + 3 * alpha * (t / R) ^ 2))).trans
      (pairedEtaCriticalCubicPhase_increment_error_le hh hh1 hR hv ht kappa alpha)
  have he := exp_pairedEtaMovingCriticalTilt_le hR0 ht (lambda := lambda)
  rw [exp_pairedEtaMovingCriticalTilt] at he
  calc
    _ ≤ (Real.exp (4 * |lambda|) * Real.exp (-t)) * (|alpha| * h * v ^ 2 * (6 + v)) :=
      mul_le_mul he hp (norm_nonneg _) (by positivity)
    _ = _ := by ring

end

end RiemannGaussian
