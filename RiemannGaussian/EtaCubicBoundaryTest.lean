import RiemannGaussian.EtaLogWeightedBoundaryLimit
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Complex cubic-phase tests on the limiting eta boundary interval

The joint moving-tilt and cubic-phase profile has a bounded Lipschitz
extension from the relevant logarithmic interval. Its complex phase is
retained, and the extension agrees exactly with the intended test on
`[0,2]`, which contains the limiting interval `[0,1]`.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- A one-Lipschitz retraction to a fixed logarithmic interval containing
the full limiting eta boundary distribution. -/
def etaLogScaleClamp (z : ℝ) : ℝ := max 0 (min 2 z)

/-- The auxiliary logarithmic retraction always belongs to `[0,2]`. -/
theorem etaLogScaleClamp_mem (z : ℝ) : etaLogScaleClamp z ∈ Icc (0 : ℝ) 2 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- The retraction preserves the entire relevant logarithmic interval. -/
theorem etaLogScaleClamp_eq_self {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 2) :
    etaLogScaleClamp z = z := by
  simp only [etaLogScaleClamp, min_eq_right hz.2, max_eq_right hz.1]

/-- The auxiliary retraction is globally one-Lipschitz. -/
theorem lipschitzWith_etaLogScaleClamp : LipschitzWith 1 etaLogScaleClamp := by
  exact (LipschitzWith.id.const_min 2).const_max 0

/-- The complex test predicted by simultaneous cubic phase and moving tilt. -/
def pairedEtaCubicBoundaryTest (lambda kappa alpha v z : ℝ) : ℂ :=
  (Real.exp (-2 * lambda * z) : ℂ) *
    Complex.exp (((v * (kappa + 3 * alpha * z ^ 2) : ℝ) : ℂ) * Complex.I)

/-- A bounded extension used only to apply the global complex-test theorem. -/
def pairedEtaCubicBoundaryTestExtension (lambda kappa alpha v z : ℝ) : ℂ :=
  pairedEtaCubicBoundaryTest lambda kappa alpha v (etaLogScaleClamp z)

/-- The complex cubic phase has unit norm, leaving precisely the moving
tilt weight in the test norm. -/
theorem norm_pairedEtaCubicBoundaryTest (lambda kappa alpha v z : ℝ) :
    ‖pairedEtaCubicBoundaryTest lambda kappa alpha v z‖ = Real.exp (-2 * lambda * z) := by
  rw [pairedEtaCubicBoundaryTest, norm_mul, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_one]

/-- The test is smooth in its logarithmic coordinate. -/
theorem contDiff_pairedEtaCubicBoundaryTest (lambda kappa alpha v : ℝ) :
    ContDiff ℝ 1 (pairedEtaCubicBoundaryTest lambda kappa alpha v) := by
  unfold pairedEtaCubicBoundaryTest
  have hc : ContDiff ℝ 1 (fun x : ℝ ↦ (x : ℂ)) := Complex.ofRealCLM.contDiff
  exact (hc.comp (by fun_prop : ContDiff ℝ 1 (fun z : ℝ ↦ Real.exp (-2 * lambda * z)))).mul
    (((hc.comp (by fun_prop : ContDiff ℝ 1 (fun z : ℝ ↦ v * (kappa + 3 * alpha * z ^ 2)))).mul
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ ↦ Complex.I))).cexp)

/-- The extension agrees with the original complex test on `[0,2]`. -/
theorem pairedEtaCubicBoundaryTestExtension_eq {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 2)
    (lambda kappa alpha v : ℝ) :
    pairedEtaCubicBoundaryTestExtension lambda kappa alpha v z =
      pairedEtaCubicBoundaryTest lambda kappa alpha v z := by
  rw [pairedEtaCubicBoundaryTestExtension, etaLogScaleClamp_eq_self hz]

/-- A uniform bound for the test extension, independent of both phase
parameters and the Gaussian coordinate. -/
theorem norm_pairedEtaCubicBoundaryTestExtension_le (lambda kappa alpha v z : ℝ) :
    ‖pairedEtaCubicBoundaryTestExtension lambda kappa alpha v z‖ ≤ Real.exp (4 * |lambda|) := by
  rw [pairedEtaCubicBoundaryTestExtension, norm_pairedEtaCubicBoundaryTest]
  apply Real.exp_le_exp.mpr
  obtain ⟨hz0, hz2⟩ := etaLogScaleClamp_mem z
  have h := mul_le_mul_of_nonneg_right (neg_le_abs lambda) hz0
  have h' := mul_le_mul_of_nonneg_left hz2 (abs_nonneg lambda)
  nlinarith

/-- For each fixed phase profile the bounded extension is globally
Lipschitz; no regularity hypothesis is left to a downstream caller. -/
theorem exists_lipschitzWith_pairedEtaCubicBoundaryTestExtension
    (lambda kappa alpha v : ℝ) :
    ∃ K, LipschitzWith K (pairedEtaCubicBoundaryTestExtension lambda kappa alpha v) := by
  obtain ⟨K, hK⟩ := (contDiff_pairedEtaCubicBoundaryTest lambda kappa alpha v).contDiffOn
    |>.exists_lipschitzOnWith (by norm_num) (convex_Icc (0 : ℝ) 2) isCompact_Icc
  refine ⟨K, lipschitzWith_iff_dist_le_mul.mpr fun x y ↦ ?_⟩
  have hxy := lipschitzOnWith_iff_dist_le_mul.mp hK
    (etaLogScaleClamp x) (etaLogScaleClamp_mem x) (etaLogScaleClamp y) (etaLogScaleClamp_mem y)
  have hc := lipschitzWith_etaLogScaleClamp.dist_le_mul x y
  simp only [NNReal.coe_one, one_mul] at hc
  exact hxy.trans (mul_le_mul_of_nonneg_left hc K.coe_nonneg)

/-- The bounded extension and original test have the same limiting
boundary integral, with its complex phase retained. -/
theorem integral_pairedEtaCubicBoundaryTestExtension (lambda kappa alpha v : ℝ) :
    (∫ z in 0..1, pairedEtaCubicBoundaryTestExtension lambda kappa alpha v z) =
      ∫ z in 0..1, pairedEtaCubicBoundaryTest lambda kappa alpha v z := by
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hz
  exact pairedEtaCubicBoundaryTestExtension_eq ⟨hz.1, by linarith [hz.2]⟩ _ _ _ _

/-- The actual eta boundary distribution has the full complex cubic-test
limit. The remaining phase-increment comparison is separate from this theorem. -/
theorem pairedEtaWeightedMismatch_cubic_test_tendsto (lambda kappa alpha : ℝ)
    {v : ℝ} (hv : 0 < v) :
    Tendsto (fun R : ℝ ↦ (Real.exp (-R) * R)⁻¹ •
      pairedEtaWeightedMismatch (Real.exp (-R) * v) R
        (pairedEtaCubicBoundaryTestExtension lambda kappa alpha v)) atTop
      (𝓝 (v • (∫ z in 0..1, pairedEtaCubicBoundaryTest lambda kappa alpha v z))) := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_pairedEtaCubicBoundaryTestExtension lambda kappa alpha v
  simpa only [integral_pairedEtaCubicBoundaryTestExtension] using
    pairedEtaWeightedMismatch_exp_scaled_tendsto hv hK
      (norm_pairedEtaCubicBoundaryTestExtension_le lambda kappa alpha v)

/-- The unit complex phase is one-Lipschitz in its real argument. -/
theorem norm_exp_ofReal_mul_I_sub_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a - b| := by
  have heq : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I) =
      Complex.exp ((b : ℂ) * Complex.I) *
        (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [heq, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa only [Real.norm_eq_abs] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b))

end

end RiemannGaussian
