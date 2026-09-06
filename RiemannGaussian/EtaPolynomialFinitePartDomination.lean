import RiemannGaussian.EtaWeightedFinitePartBound
import RiemannGaussian.EtaPolynomialMismatchFinitePart

/-!
# Domination of the actual polynomial-phase finite part

The actual phase comparison and the global weighted bound combine into a
polynomial majorant after subtracting the leading complex term. The moving
horizontal heat damping is retained with a separate quantitative estimate.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The polynomial majorant for the undamped complex finite part. -/
def pairedEtaPolynomialFinitePartBound (lambda beta alpha v : ℝ) : ℝ :=
  Real.exp (4 * |lambda|) * (4 + 12 * v + 8 * v ^ 2 +
    v ^ 2 * (|beta| + |alpha| * (6 + v)) +
    4 * (2 * |lambda| + v * (|beta| + 12 * |alpha|)) * (1 + v + v ^ 2))

/-- A uniform bound for the actual complex finite part on every positive
Gaussian coordinate; the linear phase coefficient does not affect it. -/
theorem norm_pairedEtaPhaseMismatch_polynomial_finite_part_le {lambda R v : ℝ}
    (hR : 1 ≤ R) (hlarge : 4 * |lambda| ≤ R) (hv : 0 < v) (kappa beta alpha : ℝ) :
    ‖(Real.exp (-R))⁻¹ • pairedEtaPhaseMismatch (pairedEtaMovingCriticalTilt lambda R)
        (pairedEtaCriticalPolynomialPhase kappa beta alpha (Real.exp (-R)) R) (Real.exp (-R) * v) -
      (v * R) • (∫ z in 0..1, pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v z)‖ ≤
      pairedEtaPolynomialFinitePartBound lambda beta alpha v := by
  let h := Real.exp (-R)
  let B := Real.exp (4 * |lambda|)
  let C := v ^ 2 * (|beta| + |alpha| * (6 + v))
  let F := pairedEtaPolynomialBoundaryTestExtension lambda kappa beta alpha v
  let D := pairedEtaPhaseMismatch (pairedEtaMovingCriticalTilt lambda R)
    (pairedEtaCriticalPolynomialPhase kappa beta alpha h R) (h * v)
  let W := pairedEtaWeightedMismatch (h * v) R F
  have hh : 0 < h := Real.exp_pos _
  have hh1 : h ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hR0 : 0 < R := by linarith
  have hB : 0 ≤ B := (Real.exp_pos _).le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hphase : ‖h⁻¹ • D - h⁻¹ • W‖ ≤ B * (C + 3) := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
    have hfrac : C / R ≤ C := (div_le_self hC hR)
    calc
      _ ≤ h⁻¹ * (h * B * (C / R + 3 * h)) :=
        mul_le_mul_of_nonneg_left
          (pairedEtaPhaseMismatch_polynomial_test_error_le hR hlarge hv.le kappa beta alpha)
          (inv_nonneg.mpr hh.le)
      _ = B * (C / R + 3 * h) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hB
  have hw := norm_pairedEtaWeightedMismatch_finite_part_le hR hv
    (lipschitzWith_pairedEtaPolynomialBoundaryTestExtension lambda kappa beta alpha v)
    (norm_pairedEtaPolynomialBoundaryTestExtension_le lambda kappa beta alpha v)
  simp only [integral_pairedEtaPolynomialBoundaryTestExtension] at hw
  have hK : (pairedEtaPolynomialBoundaryLipschitz lambda beta alpha v : ℝ) =
      B * (2 * |lambda| + v * (|beta| + 12 * |alpha|)) := by
    change B * (2 * |lambda| + |v| * (|beta| + 12 * |alpha|)) = _
    rw [abs_of_pos hv]
  rw [hK] at hw
  have ht := (norm_sub_le_norm_sub_add_norm_sub (h⁻¹ • D) (h⁻¹ • W)
    ((v * R) • (∫ z in 0..1, pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v z))).trans
      (add_le_add hphase hw)
  exact ht.trans_eq (by dsimp [B, C, pairedEtaPolynomialFinitePartBound]; ring)

/-- The moving tilt also has a uniform upper bound in the eventual range. -/
theorem pairedEtaMovingCriticalTilt_upper {lambda R : ℝ} (hR : 0 < R)
    (hlarge : 4 * |lambda| ≤ R) : pairedEtaMovingCriticalTilt lambda R ≤ 3 / 4 := by
  have hfrac : lambda / R ≤ 1 / 4 := by
    apply (div_le_iff₀ hR).2
    linarith [le_abs_self lambda]
  unfold pairedEtaMovingCriticalTilt
  linarith

/-- Heat damping lies in `(0,1]` and differs from one by at most the displacement. -/
theorem pairedEtaMovingCriticalTilt_damping_bounds {lambda R v : ℝ}
    (hR : 1 ≤ R) (hlarge : 4 * |lambda| ≤ R) (hv : 0 ≤ v) :
    let e := Real.exp (-pairedEtaMovingCriticalTilt lambda R * (Real.exp (-R) * v))
    e ∈ Icc (0 : ℝ) 1 ∧ |e - 1| ≤ Real.exp (-R) * v := by
  dsimp only
  have hs := pairedEtaMovingCriticalTilt_lower (by linarith) hlarge
  have hs' := pairedEtaMovingCriticalTilt_upper (by linarith) hlarge
  have hr : 0 ≤ Real.exp (-R) * v := mul_nonneg (Real.exp_pos _).le hv
  have he : Real.exp (-pairedEtaMovingCriticalTilt lambda R * (Real.exp (-R) * v)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  refine ⟨⟨(Real.exp_pos _).le, he⟩, ?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr he)]
  have hx := Real.add_one_le_exp (-pairedEtaMovingCriticalTilt lambda R * (Real.exp (-R) * v))
  nlinarith

/-- The actual complex heat finite part retains its moving horizontal damping. -/
def pairedEtaPolynomialDampedFinitePart (lambda kappa beta alpha R v : ℝ) : ℂ :=
  Real.exp (-pairedEtaMovingCriticalTilt lambda R * (Real.exp (-R) * v)) •
    ((Real.exp (-R))⁻¹ • pairedEtaPhaseMismatch (pairedEtaMovingCriticalTilt lambda R)
      (pairedEtaCriticalPolynomialPhase kappa beta alpha (Real.exp (-R)) R) (Real.exp (-R) * v)) -
    (v * R) • (∫ z in 0..1, pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v z)

/-- Damping the leading term has an explicit exponentially vanishing error. -/
theorem norm_pairedEtaPolynomial_damping_main_error_le {lambda R v : ℝ}
    (hR : 1 ≤ R) (hlarge : 4 * |lambda| ≤ R) (hv : 0 < v) (kappa beta alpha : ℝ) :
    ‖(Real.exp (-pairedEtaMovingCriticalTilt lambda R * (Real.exp (-R) * v)) - 1) •
      ((v * R) • (∫ z in 0..1, pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v z))‖ ≤
      Real.exp (4 * |lambda|) * v ^ 2 * (Real.exp (-R) * R) := by
  have hJ : ‖∫ z in 0..1, pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v z‖ ≤ Real.exp (4 * |lambda|) := by
    rw [← integral_pairedEtaPolynomialBoundaryTestExtension]
    simpa only [sub_zero, abs_one, mul_one] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
        (fun z _ ↦ norm_pairedEtaPolynomialBoundaryTestExtension_le lambda kappa beta alpha v z))
  have he := (pairedEtaMovingCriticalTilt_damping_bounds hR hlarge hv.le).2
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (show 0 < v * R by positivity)]
  exact (mul_le_mul he (mul_le_mul_of_nonneg_left hJ (by positivity))
    (by positivity) (by positivity)).trans_eq (by ring)

/-- The damped actual finite part has one polynomial majorant, uniform in
the logarithmic scale and suitable for Gaussian dominated convergence. -/
theorem norm_pairedEtaPolynomialDampedFinitePart_le {lambda R v : ℝ}
    (hR : 1 ≤ R) (hlarge : 4 * |lambda| ≤ R) (hv : 0 < v) (kappa beta alpha : ℝ) :
    ‖pairedEtaPolynomialDampedFinitePart lambda kappa beta alpha R v‖ ≤
      pairedEtaPolynomialFinitePartBound lambda beta alpha v + Real.exp (4 * |lambda|) * v ^ 2 := by
  let e := Real.exp (-pairedEtaMovingCriticalTilt lambda R * (Real.exp (-R) * v))
  let X := (Real.exp (-R))⁻¹ • pairedEtaPhaseMismatch (pairedEtaMovingCriticalTilt lambda R)
    (pairedEtaCriticalPolynomialPhase kappa beta alpha (Real.exp (-R)) R) (Real.exp (-R) * v)
  let Y := (v * R) • (∫ z in 0..1, pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v z)
  have he := (pairedEtaMovingCriticalTilt_damping_bounds hR hlarge hv.le).1
  have hfirst : ‖e • (X - Y)‖ ≤ pairedEtaPolynomialFinitePartBound lambda beta alpha v := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg he.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) he.2).trans
      (norm_pairedEtaPhaseMismatch_polynomial_finite_part_le hR hlarge hv kappa beta alpha)
  have hsecond : ‖(e - 1) • Y‖ ≤ Real.exp (4 * |lambda|) * v ^ 2 := by
    exact (norm_pairedEtaPolynomial_damping_main_error_le hR hlarge hv kappa beta alpha).trans
      (mul_le_of_le_one_right (by positivity) (etaHeatWidth_mul_scale_le_one R))
  change ‖e • X - Y‖ ≤ _
  rw [show e • X - Y = e • (X - Y) + (e - 1) • Y by simp only [smul_sub, sub_smul, one_smul]; abel]
  exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)

/-- Heat width times logarithmic scale vanishes in the heat limit. -/
theorem etaHeatWidth_mul_scale_tendsto_zero :
    Tendsto (fun R : ℝ ↦ Real.exp (-R) * R) atTop (𝓝 0) := by
  simpa only [pow_one, mul_comm] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1

/-- The moving damping tends to one at each fixed positive Gaussian coordinate. -/
theorem pairedEtaMovingCriticalTilt_damping_tendsto (lambda : ℝ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun R : ℝ ↦ Real.exp (-pairedEtaMovingCriticalTilt lambda R * (Real.exp (-R) * v)))
      atTop (𝓝 1) := by
  have he : Tendsto (fun R : ℝ ↦
      Real.exp (-pairedEtaMovingCriticalTilt lambda R * (Real.exp (-R) * v)) - 1) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa only [zero_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.mul_const v)
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (4 * |lambda|)] with R hR hlarge
    simpa only [Real.norm_eq_abs] using (pairedEtaMovingCriticalTilt_damping_bounds hR hlarge hv.le).2
  simpa only [sub_add_cancel, zero_add] using he.add_const 1

/-- The full actual complex heat finite part has the evaluated endpoint
limit, with the moving damping included and its error discharged. -/
theorem pairedEtaPolynomialDampedFinitePart_tendsto (lambda kappa beta alpha : ℝ)
    {v : ℝ} (hv : 0 < v) :
    Tendsto (fun R : ℝ ↦ pairedEtaPolynomialDampedFinitePart lambda kappa beta alpha R v) atTop
      (𝓝 (v • ((Real.eulerMascheroniConstant - 1) •
        pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v 0 +
        (1 - Real.log (Real.pi / 2) - Real.log v) •
          pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v 1))) := by
  have hmain := (pairedEtaMovingCriticalTilt_damping_tendsto lambda hv).smul
    (pairedEtaPhaseMismatch_polynomial_finite_part_tendsto lambda kappa beta alpha hv)
  have herror : Tendsto (fun R : ℝ ↦
      (Real.exp (-pairedEtaMovingCriticalTilt lambda R * (Real.exp (-R) * v)) - 1) •
        ((v * R) • (∫ z in 0..1, pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v z)))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa only [mul_zero] using
      etaHeatWidth_mul_scale_tendsto_zero.const_mul (Real.exp (4 * |lambda|) * v ^ 2))
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (4 * |lambda|)] with R hR hlarge
    exact norm_pairedEtaPolynomial_damping_main_error_le hR hlarge hv kappa beta alpha
  convert hmain.add herror using 1
  · funext R
    simp only [pairedEtaPolynomialDampedFinitePart, smul_sub, sub_smul, one_smul]
    abel
  · simp only [one_smul, add_zero]

end

end RiemannGaussian
