import RiemannGaussian.EtaCubicMismatchLimit
import RiemannGaussian.EtaSupportGapGaussianProfile

/-!
# A Gaussian-integrable bound at the moving critical tilt

The normalized actual complex displacement has a quadratic majorant in
the Gaussian coordinate, uniform over every real phase. This supplies the
domination missing from a merely pointwise cubic-phase scaling limit.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The moving-tilt mass is bounded by critical arithmetic mass on the
growing resolved interval and a quadratic-width exponential tail. -/
theorem pairedEtaMismatch_movingTilt_le {lambda R : ℝ} (hR : 1 ≤ R)
    (hlarge : 4 * |lambda| ≤ R) (r : ℝ) :
    pairedEtaMismatch (pairedEtaMovingCriticalTilt lambda R) r ≤
      Real.exp (4 * |lambda|) * pairedEtaMismatch (1 / 2) r +
        2 * Real.exp (-R) ^ 2 * Real.exp (4 * |lambda|) := by
  let sigma := pairedEtaMovingCriticalTilt lambda R
  let B := Real.exp (4 * |lambda|)
  let f : ℝ → ℝ := fun t ↦ pairedEtaLogShiftMismatch r t * Real.exp (-(2 * sigma) * t)
  let g : ℝ → ℝ := fun t ↦ pairedEtaLogShiftMismatch r t * Real.exp (-t)
  have hR0 : 0 < R := by linarith
  have hs : 0 < sigma := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4)
    (pairedEtaMovingCriticalTilt_lower hR0 hlarge)
  have hB : 0 ≤ B := (Real.exp_pos _).le
  have hf : IntegrableOn f (Ioi 0) := integrableOn_pairedEtaMismatchKernel hs r 0
  have hg : IntegrableOn g (Ioi 0) := by
    simpa only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, neg_one_mul] using
      integrableOn_pairedEtaMismatchKernel (sigma := 1 / 2) (by norm_num) r 0
  have hA : 0 ≤ 2 * R := by linarith
  have htail : (∫ t in Ioi (2 * R), f t) ≤ 2 * Real.exp (-R) ^ 2 * B := by
    have hb := pairedEtaPhaseMismatch_movingTilt_tail_le hR0 hlarge (fun _ ↦ 0) r
    simp only [pairedEtaShiftPhaseKernel, sub_self, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, mul_one, ← Complex.ofReal_mul, integral_complex_ofReal,
      Complex.norm_real, Real.norm_eq_abs] at hb
    exact (le_abs_self _).trans hb
  have hlocal : (∫ t in Ioc 0 (2 * R), f t) ≤ B * pairedEtaMismatch (1 / 2) r := by
    have hp : (∫ t in Ioc 0 (2 * R), g t) ≤ pairedEtaMismatch (1 / 2) r := by
      have hb := setIntegral_mono_set (s := Ioc (0 : ℝ) (2 * R)) (t := Ioi (0 : ℝ)) hg
        (Eventually.of_forall fun t ↦ mul_nonneg (pairedEtaLogShiftMismatch_nonneg r t) (Real.exp_pos _).le)
        (Eventually.of_forall fun t ht ↦ ht.1)
      simpa only [g, pairedEtaMismatch, show (2 : ℝ) * (1 / 2) = 1 by norm_num, neg_one_mul] using hb
    calc
      _ ≤ ∫ t in Ioc 0 (2 * R), B * g t := by
        apply integral_mono_ae (hf.mono_set Ioc_subset_Ioi_self)
          ((hg.mono_set Ioc_subset_Ioi_self).const_mul B)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have hb := mul_le_mul_of_nonneg_left
          (exp_pairedEtaMovingCriticalTilt_le hR0 ⟨ht.1.le, ht.2⟩ (lambda := lambda))
          (pairedEtaLogShiftMismatch_nonneg r t)
        dsimp [f, g, sigma, B]
        nlinarith
      _ = B * ∫ t in Ioc 0 (2 * R), g t := integral_const_mul _ _
      _ ≤ B * pairedEtaMismatch (1 / 2) r := mul_le_mul_of_nonneg_left hp hB
  have hi := intervalIntegral.integral_interval_add_Ioi hf (hf.mono_set (Ioi_subset_Ioi hA))
  rw [intervalIntegral.integral_of_le hA] at hi
  change (∫ t in Ioi 0, f t) ≤ _
  rw [← hi]
  exact add_le_add hlocal htail

/-- A global quadratic bound for the critical displacement normalized at
exponentially small width; the Gaussian coordinate need not be small. -/
theorem pairedEtaMismatch_exp_scaled_bound {R v : ℝ} (hR : 1 ≤ R) (hv : 0 < v) :
    pairedEtaMismatch (1 / 2) (Real.exp (-R) * v) ≤
      (Real.exp (-R) * R) * (10 + 11 * v ^ 2) := by
  let h := Real.exp (-R)
  have hh : 0 < h := Real.exp_pos _
  have hh1 : h ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hr : 0 < h * v := mul_pos hh hv
  have hlog : Real.log (1 / (h * v)) = R - Real.log v := by
    dsimp [h]
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one,
      Real.log_mul (Real.exp_ne_zero _) hv.ne', Real.log_exp]
    ring
  have hbase := (le_abs_self (pairedEtaMismatch (1 / 2) (h * v) -
    h * v * Real.log (1 / (h * v)))).trans (pairedEtaMismatch_critical_error_global hr)
  rw [hlog] at hbase
  have hlogv := mul_abs_log_le_one_add_sq hv
  have hlogabs := mul_le_mul_of_nonneg_left (neg_le_abs (Real.log v)) hr.le
  have hquad : (h * v) ^ 2 ≤ h * v ^ 2 := by
    have hh2 : h ^ 2 ≤ h := by nlinarith
    have h := mul_le_mul_of_nonneg_right hh2 (sq_nonneg v)
    nlinarith
  have hmid : pairedEtaMismatch (1 / 2) (h * v) ≤
      h * (R * v + 16 * v + 1 + 2 * v ^ 2) := by
    have hlogh := mul_le_mul_of_nonneg_left hlogv hh.le
    nlinarith
  have hpoly : 17 * v + 1 + 2 * v ^ 2 ≤ 10 + 11 * v ^ 2 := by
    nlinarith [sq_nonneg (v - 1)]
  have hgrowth : 16 * v + 1 + 2 * v ^ 2 ≤ R * (16 * v + 1 + 2 * v ^ 2) :=
    le_mul_of_one_le_left (by positivity) hR
  have hpolyR := mul_le_mul_of_nonneg_left hpoly (show 0 ≤ R by linarith)
  calc
    _ ≤ h * (R * v + 16 * v + 1 + 2 * v ^ 2) := hmid
    _ ≤ h * (R * (10 + 11 * v ^ 2)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hh.le
    _ = _ := by dsimp [h]; ring

/-- Uniform phase-independent domination of the normalized complex
displacement by a quadratic polynomial in the Gaussian coordinate. -/
theorem norm_pairedEtaPhaseMismatch_movingTilt_scaled_le {lambda R v : ℝ}
    (hR : 1 ≤ R) (hlarge : 4 * |lambda| ≤ R) (hv : 0 < v) (phi : ℝ → ℝ) :
    ‖(Real.exp (-R) * R)⁻¹ •
      pairedEtaPhaseMismatch (pairedEtaMovingCriticalTilt lambda R) phi (Real.exp (-R) * v)‖ ≤
      Real.exp (4 * |lambda|) * (12 + 11 * v ^ 2) := by
  let h := Real.exp (-R)
  let B := Real.exp (4 * |lambda|)
  have hh : 0 < h := Real.exp_pos _
  have hR0 : 0 < R := by linarith
  have hh1 : h ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hhR : h ^ 2 ≤ h * R := by nlinarith
  have hB : 0 ≤ B := (Real.exp_pos _).le
  have hb := (norm_pairedEtaPhaseMismatch_le _ (h * v) phi).trans
    (pairedEtaMismatch_movingTilt_le hR hlarge (h * v))
  have hcrit := pairedEtaMismatch_exp_scaled_bound hR hv
  have hmass : ‖pairedEtaPhaseMismatch (pairedEtaMovingCriticalTilt lambda R) phi (h * v)‖ ≤
      (h * R) * (B * (12 + 11 * v ^ 2)) := by
    have hc := mul_le_mul_of_nonneg_left hcrit hB
    have ht := mul_le_mul_of_nonneg_left hhR hB
    change ‖pairedEtaPhaseMismatch (pairedEtaMovingCriticalTilt lambda R) phi (h * v)‖ ≤
      B * pairedEtaMismatch (1 / 2) (h * v) + 2 * h ^ 2 * B at hb
    change B * pairedEtaMismatch (1 / 2) (h * v) ≤ B * (h * R * (10 + 11 * v ^ 2)) at hc
    nlinarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (mul_pos hh hR0))]
  calc
    _ ≤ (h * R)⁻¹ * ((h * R) * (B * (12 + 11 * v ^ 2))) :=
      mul_le_mul_of_nonneg_left hmass (inv_nonneg.mpr (mul_nonneg hh.le hR0.le))
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (mul_ne_zero hh.ne' hR0.ne'), one_mul]

end

end RiemannGaussian
