import RiemannGaussian.EtaPolynomialPhaseIncrement
import RiemannGaussian.EtaCubicMismatchLimit

/-!
# The finite part of actual polynomial-phase eta displacement

A refined comparison retains the true tail at order `h^2` and the local
phase error at order `h/R`. The literal complex displacement therefore has
the evaluated two-endpoint finite part before taking a real part or a
Gaussian average.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The full true phase displacement differs from the limiting complex
boundary test by an explicit second-order error. Both actual tails and the
signed polynomial phase increment are accounted for. -/
theorem pairedEtaPhaseMismatch_polynomial_test_error_le {lambda R v : ℝ}
    (hR : 1 ≤ R) (hlarge : 4 * |lambda| ≤ R) (hv : 0 ≤ v) (kappa beta alpha : ℝ) :
    ‖pairedEtaPhaseMismatch (pairedEtaMovingCriticalTilt lambda R)
        (pairedEtaCriticalPolynomialPhase kappa beta alpha (Real.exp (-R)) R) (Real.exp (-R) * v) -
      pairedEtaWeightedMismatch (Real.exp (-R) * v) R
        (pairedEtaPolynomialBoundaryTestExtension lambda kappa beta alpha v)‖ ≤
      Real.exp (-R) * Real.exp (4 * |lambda|) *
        (v ^ 2 * (|beta| + |alpha| * (6 + v)) / R + 3 * Real.exp (-R)) := by
  let h := Real.exp (-R)
  let sigma := pairedEtaMovingCriticalTilt lambda R
  let phi := pairedEtaCriticalPolynomialPhase kappa beta alpha h R
  let F := pairedEtaPolynomialBoundaryTestExtension lambda kappa beta alpha v
  let B := Real.exp (4 * |lambda|)
  let C := B * ((h / R) * v ^ 2 * (|beta| + |alpha| * (6 + v)))
  let f : ℝ → ℂ := fun t ↦ (pairedEtaLogShiftMismatch (h * v) t : ℂ) *
    pairedEtaShiftPhaseKernel sigma phi (h * v) t
  let g : ℝ → ℂ := fun t ↦ (pairedEtaLogShiftMismatch (h * v) t * Real.exp (-t)) • F (t / R)
  have hR0 : 0 < R := by linarith
  have hh : 0 < h := Real.exp_pos _
  have hh1 : h ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hs : 0 < sigma := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4)
    (pairedEtaMovingCriticalTilt_lower hR0 hlarge)
  have hphi : Measurable phi := (continuous_pairedEtaCriticalPolynomialPhase kappa beta alpha h R).measurable
  have hK := lipschitzWith_pairedEtaPolynomialBoundaryTestExtension lambda kappa beta alpha v
  have hF : Measurable F := hK.continuous.measurable
  have hB : ∀ x, ‖F x‖ ≤ B := norm_pairedEtaPolynomialBoundaryTestExtension_le lambda kappa beta alpha v
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hf : IntegrableOn f (Ioi 0) :=
    integrableOn_pairedEtaLogShiftMismatch_mul (integrableOn_pairedEtaShiftPhaseKernel hs hphi (h * v) 0) _
  have hg : IntegrableOn g (Ioi 0) := integrableOn_pairedEtaWeightedMismatchKernel hF hB _ _ _
  have hA : 0 ≤ 2 * R := by linarith
  have hfTail := hf.mono_set (Ioi_subset_Ioi hA)
  have hgTail := hg.mono_set (Ioi_subset_Ioi hA)
  have he : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi 0) := by
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 0
  have hlocal : ‖∫ t in Ioc 0 (2 * R), f t - g t‖ ≤ C := by
    calc
      _ ≤ ∫ t in Ioc 0 (2 * R), C * Real.exp (-t) := by
        apply norm_integral_le_of_norm_le ((he.mono_set Ioc_subset_Ioi_self).const_mul C)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have ht' : t ∈ Icc (0 : ℝ) (2 * R) := ⟨ht.1.le, ht.2⟩
        have hb := pairedEtaPolynomialPhaseKernel_local_error_le hh hh1 hR hv ht' lambda kappa beta alpha
        change ‖pairedEtaShiftPhaseKernel sigma phi (h * v) t - Real.exp (-t) • F (t / R)‖ ≤
          C * Real.exp (-t) at hb
        have hid : f t - g t = (pairedEtaLogShiftMismatch (h * v) t : ℂ) *
            (pairedEtaShiftPhaseKernel sigma phi (h * v) t - Real.exp (-t) • F (t / R)) := by
          dsimp [f, g]
          simp only [Complex.ofReal_mul]
          ring
        rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (pairedEtaLogShiftMismatch_nonneg _ _)]
        simpa only [one_mul] using mul_le_mul (pairedEtaLogShiftMismatch_le_one _ _) hb
          (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      _ = C * (∫ t in Ioc 0 (2 * R), Real.exp (-t)) := integral_const_mul _ _
      _ ≤ C := by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (integral_exp_neg_Ioc_le_one hA) hC0
  have hftail : ‖∫ t in Ioi (2 * R), f t‖ ≤ 2 * h ^ 2 * B :=
    pairedEtaPhaseMismatch_movingTilt_tail_le hR0 hlarge phi (h * v)
  have hgtail : ‖∫ t in Ioi (2 * R), g t‖ ≤ B * h ^ 2 := by
    have hb := norm_pairedEtaWeightedMismatch_time_tail_le hB (h * v) R (2 * R)
    have hx : Real.exp (-(2 * R)) = h ^ 2 := by
      dsimp [h]
      rw [show -(2 * R) = (-R) + (-R) by ring, Real.exp_add, pow_two]
    simpa only [hx] using hb
  have htail : ‖∫ t in Ioi (2 * R), f t - g t‖ ≤ 3 * B * h ^ 2 := by
    rw [integral_sub hfTail hgTail]
    exact (norm_sub_le _ _).trans ((add_le_add hftail hgtail).trans_eq (by ring))
  have hsplit := intervalIntegral.integral_interval_add_Ioi (hf.sub hg) (hfTail.sub hgTail)
  rw [intervalIntegral.integral_of_le hA] at hsplit
  simp only [Pi.sub_apply] at hsplit
  change ‖(∫ t in Ioi 0, f t) - ∫ t in Ioi 0, g t‖ ≤ _
  rw [← integral_sub hf hg, ← hsplit]
  exact (norm_add_le _ _).trans ((add_le_add hlocal htail).trans_eq (by dsimp [C, B, h]; ring))

/-- The true complex polynomial-phase displacement has the evaluated
finite part at both endpoints. The actual phase and both time tails have
been compared at a precision smaller than the heat width. -/
theorem pairedEtaPhaseMismatch_polynomial_finite_part_tendsto (lambda kappa beta alpha : ℝ)
    {v : ℝ} (hv : 0 < v) :
    Tendsto (fun R : ℝ ↦ (Real.exp (-R))⁻¹ •
      pairedEtaPhaseMismatch (pairedEtaMovingCriticalTilt lambda R)
        (pairedEtaCriticalPolynomialPhase kappa beta alpha (Real.exp (-R)) R) (Real.exp (-R) * v) -
      (v * R) • (∫ z in 0..1, pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v z)) atTop
      (𝓝 (v • ((Real.eulerMascheroniConstant - 1) •
        pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v 0 +
        (1 - Real.log (Real.pi / 2) - Real.log v) •
          pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v 1))) := by
  let B := Real.exp (4 * |lambda|)
  let C := v ^ 2 * (|beta| + |alpha| * (6 + v))
  have hdom : Tendsto (fun R : ℝ ↦ B * (C / R + 3 * Real.exp (-R))) atTop (𝓝 0) := by
    have hfrac : Tendsto (fun R : ℝ ↦ C / R) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using
        (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ ↦ R⁻¹) atTop (𝓝 0)).const_mul C
    simpa only [mul_zero, add_zero] using
      (hfrac.add (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul 3)).const_mul B
  have herror : Tendsto (fun R : ℝ ↦ (Real.exp (-R))⁻¹ •
      (pairedEtaPhaseMismatch (pairedEtaMovingCriticalTilt lambda R)
          (pairedEtaCriticalPolynomialPhase kappa beta alpha (Real.exp (-R)) R) (Real.exp (-R) * v) -
        pairedEtaWeightedMismatch (Real.exp (-R) * v) R
          (pairedEtaPolynomialBoundaryTestExtension lambda kappa beta alpha v))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hdom
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (4 * |lambda|)] with R hR hlarge
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.exp_pos _))]
    calc
      _ ≤ (Real.exp (-R))⁻¹ * (Real.exp (-R) * Real.exp (4 * |lambda|) *
          (v ^ 2 * (|beta| + |alpha| * (6 + v)) / R + 3 * Real.exp (-R))) :=
        mul_le_mul_of_nonneg_left
          (pairedEtaPhaseMismatch_polynomial_test_error_le hR hlarge hv.le kappa beta alpha)
          (inv_nonneg.mpr (Real.exp_pos _).le)
      _ = B * (C / R + 3 * Real.exp (-R)) := by dsimp [B, C]; field_simp
  have h := herror.add (pairedEtaWeightedMismatch_polynomial_finite_part_tendsto lambda kappa beta alpha hv)
  simp only [smul_sub, sub_add_sub_cancel, zero_add] at h
  exact h

end

end RiemannGaussian
