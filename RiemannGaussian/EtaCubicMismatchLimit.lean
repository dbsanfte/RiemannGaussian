import RiemannGaussian.EtaCubicPhaseIncrement
import RiemannGaussian.EtaPhaseMismatchBounds

/-!
# Joint cubic-phase and moving-tilt limit of actual eta displacement

The true modulated eta displacement is compared quantitatively with the
bounded complex test of its logarithmic boundary measure. The growing
time-interval complement is controlled at the moving positive tilt. This
proves the full complex displacement limit before Gaussian integration.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- At twice the logarithmic time scale, the moving-tilt phase tail is
quadratic in the exponentially small width, uniformly over real phases. -/
theorem pairedEtaPhaseMismatch_movingTilt_tail_le {lambda R : ℝ}
    (hR : 0 < R) (hlarge : 4 * |lambda| ≤ R) (phi : ℝ → ℝ) (r : ℝ) :
    ‖∫ t in Ioi (2 * R), (pairedEtaLogShiftMismatch r t : ℂ) *
      pairedEtaShiftPhaseKernel (pairedEtaMovingCriticalTilt lambda R) phi r t‖ ≤
      2 * Real.exp (-R) ^ 2 * Real.exp (4 * |lambda|) := by
  have hs := pairedEtaMovingCriticalTilt_lower hR hlarge
  have hs0 : 0 < pairedEtaMovingCriticalTilt lambda R := by linarith
  have hi : 1 / (2 * pairedEtaMovingCriticalTilt lambda R) ≤ 2 := by
    apply (div_le_iff₀ (by positivity)).2
    linarith
  have he : Real.exp (-(2 * pairedEtaMovingCriticalTilt lambda R) * (2 * R)) =
      Real.exp (-R) ^ 2 * Real.exp (-4 * lambda) := by
    have hx : -(2 * pairedEtaMovingCriticalTilt lambda R) * (2 * R) =
        (-R) + (-R) + (-4 * lambda) := by
      unfold pairedEtaMovingCriticalTilt
      field_simp
      ring
    rw [hx, Real.exp_add, Real.exp_add, pow_two]
  have hle : Real.exp (-4 * lambda) ≤ Real.exp (4 * |lambda|) := by
    apply Real.exp_le_exp.mpr
    linarith [neg_le_abs lambda]
  calc
    _ ≤ Real.exp (-(2 * pairedEtaMovingCriticalTilt lambda R) * (2 * R)) /
        (2 * pairedEtaMovingCriticalTilt lambda R) :=
      norm_pairedEtaPhaseMismatch_time_tail_le hs0 phi r (2 * R)
    _ = (Real.exp (-R) ^ 2 * Real.exp (-4 * lambda)) *
        (1 / (2 * pairedEtaMovingCriticalTilt lambda R)) := by rw [he]; ring
    _ ≤ (Real.exp (-R) ^ 2 * Real.exp (4 * |lambda|)) * 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hle (sq_nonneg _)) hi (by positivity) (by positivity)
    _ = _ := by ring

/-- The full true phase displacement differs from the limiting complex
boundary test by an explicit order-width error. Both actual tails and the
signed cubic phase increment are accounted for. -/
theorem pairedEtaPhaseMismatch_cubic_test_error_le {lambda R v : ℝ}
    (hR : 1 ≤ R) (hlarge : 4 * |lambda| ≤ R) (hv : 0 ≤ v) (kappa alpha : ℝ) :
    ‖pairedEtaPhaseMismatch (pairedEtaMovingCriticalTilt lambda R)
        (pairedEtaCriticalCubicPhase kappa alpha (Real.exp (-R)) R) (Real.exp (-R) * v) -
      pairedEtaWeightedMismatch (Real.exp (-R) * v) R
        (pairedEtaCubicBoundaryTestExtension lambda kappa alpha v)‖ ≤
      Real.exp (-R) * Real.exp (4 * |lambda|) * (|alpha| * v ^ 2 * (6 + v) + 3) := by
  let h := Real.exp (-R)
  let sigma := pairedEtaMovingCriticalTilt lambda R
  let phi := pairedEtaCriticalCubicPhase kappa alpha h R
  let F := pairedEtaCubicBoundaryTestExtension lambda kappa alpha v
  let B := Real.exp (4 * |lambda|)
  let C := B * (|alpha| * h * v ^ 2 * (6 + v))
  let f : ℝ → ℂ := fun t ↦ (pairedEtaLogShiftMismatch (h * v) t : ℂ) *
    pairedEtaShiftPhaseKernel sigma phi (h * v) t
  let g : ℝ → ℂ := fun t ↦ (pairedEtaLogShiftMismatch (h * v) t * Real.exp (-t)) • F (t / R)
  have hR0 : 0 < R := by linarith
  have hh : 0 < h := Real.exp_pos _
  have hh1 : h ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hs : 0 < sigma := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4)
    (pairedEtaMovingCriticalTilt_lower hR0 hlarge)
  have hphi : Measurable phi := (continuous_pairedEtaCriticalCubicPhase kappa alpha h R).measurable
  obtain ⟨K, hK⟩ := exists_lipschitzWith_pairedEtaCubicBoundaryTestExtension lambda kappa alpha v
  have hF : Measurable F := hK.continuous.measurable
  have hB : ∀ x, ‖F x‖ ≤ B := norm_pairedEtaCubicBoundaryTestExtension_le lambda kappa alpha v
  have hB0 : 0 ≤ B := (Real.exp_pos _).le
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
        have hb := pairedEtaCubicPhaseKernel_local_error_le hh hh1 hR hv ht' lambda kappa alpha
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
  have htail : ‖∫ t in Ioi (2 * R), f t - g t‖ ≤ 3 * B * h := by
    rw [integral_sub hfTail hgTail]
    have hh2 : h ^ 2 ≤ h := by nlinarith
    have hBh := mul_le_mul_of_nonneg_left hh2 hB0
    exact (norm_sub_le _ _).trans ((add_le_add hftail hgtail).trans (by nlinarith))
  have hsplit := intervalIntegral.integral_interval_add_Ioi (hf.sub hg) (hfTail.sub hgTail)
  rw [intervalIntegral.integral_of_le hA] at hsplit
  simp only [Pi.sub_apply] at hsplit
  change ‖(∫ t in Ioi 0, f t) - ∫ t in Ioi 0, g t‖ ≤ _
  rw [← integral_sub hf hg, ← hsplit]
  exact (norm_add_le _ _).trans ((add_le_add hlocal htail).trans (by dsimp [C, B, h]; ring_nf; rfl))

/-- The true complex eta displacement has the joint cubic-phase and
moving-tilt limit, prior to taking any real part or Gaussian average. -/
theorem pairedEtaPhaseMismatch_cubic_movingTilt_tendsto (lambda kappa alpha : ℝ)
    {v : ℝ} (hv : 0 < v) :
    Tendsto (fun R : ℝ ↦ (Real.exp (-R) * R)⁻¹ •
      pairedEtaPhaseMismatch (pairedEtaMovingCriticalTilt lambda R)
        (pairedEtaCriticalCubicPhase kappa alpha (Real.exp (-R)) R) (Real.exp (-R) * v)) atTop
      (𝓝 (v • (∫ z in 0..1, pairedEtaCubicBoundaryTest lambda kappa alpha v z))) := by
  let C := Real.exp (4 * |lambda|) * (|alpha| * v ^ 2 * (6 + v) + 3)
  have hdom : Tendsto (fun R : ℝ ↦ C / R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ ↦ R⁻¹) atTop (𝓝 0)).const_mul C
  have herror : Tendsto (fun R : ℝ ↦ (Real.exp (-R) * R)⁻¹ •
      (pairedEtaPhaseMismatch (pairedEtaMovingCriticalTilt lambda R)
          (pairedEtaCriticalCubicPhase kappa alpha (Real.exp (-R)) R) (Real.exp (-R) * v) -
        pairedEtaWeightedMismatch (Real.exp (-R) * v) R
          (pairedEtaCubicBoundaryTestExtension lambda kappa alpha v))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hdom
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (4 * |lambda|)] with R hR hlarge
    have hR0 : 0 < R := by linarith
    have hden : 0 < Real.exp (-R) * R := mul_pos (Real.exp_pos _) hR0
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hden)]
    calc
      _ ≤ (Real.exp (-R) * R)⁻¹ *
          (Real.exp (-R) * Real.exp (4 * |lambda|) * (|alpha| * v ^ 2 * (6 + v) + 3)) :=
        mul_le_mul_of_nonneg_left
          (pairedEtaPhaseMismatch_cubic_test_error_le hR hlarge hv.le kappa alpha)
          (inv_nonneg.mpr hden.le)
      _ = C / R := by dsimp [C]; field_simp
  have h := herror.add (pairedEtaWeightedMismatch_cubic_test_tendsto lambda kappa alpha hv)
  simp only [smul_sub, sub_add_cancel, zero_add] at h
  exact h

end

end RiemannGaussian
