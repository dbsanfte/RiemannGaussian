import RiemannGaussian.EtaCubicBoundaryTest
import RiemannGaussian.EtaLogTwoEndpointLimit
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Boundary tests for the reflection-closed cubic phase family

The velocity includes a linear term in logarithmic time. Its exact
reflection remains in the same family. A bounded extension has an explicit
Lipschitz constant, linear in the Gaussian coordinate, for the subsequent
second-order dominated convergence argument.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The velocity of the linear, quadratic, and cubic phase on logarithmic time. -/
def pairedEtaPolynomialVelocity (kappa beta alpha z : ℝ) : ℝ :=
  kappa + beta * z + 3 * alpha * z ^ 2

/-- Logarithmic reflection preserves the complete polynomial velocity family. -/
theorem pairedEtaPolynomialVelocity_reflection (kappa beta alpha z : ℝ) :
    pairedEtaPolynomialVelocity (kappa + beta + 3 * alpha) (-beta - 6 * alpha) alpha z =
      pairedEtaPolynomialVelocity kappa beta alpha (1 - z) := by
  unfold pairedEtaPolynomialVelocity
  ring

/-- The complex slow test retains the tilt and all three phase coefficients. -/
def pairedEtaPolynomialBoundaryTest (lambda kappa beta alpha v z : ℝ) : ℂ :=
  (Real.exp (-2 * lambda * z) : ℂ) *
    Complex.exp (((v * pairedEtaPolynomialVelocity kappa beta alpha z : ℝ) : ℂ) * Complex.I)

/-- The bounded extension agrees with the actual test through twice the limiting scale. -/
def pairedEtaPolynomialBoundaryTestExtension (lambda kappa beta alpha v z : ℝ) : ℂ :=
  pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v (etaLogScaleClamp z)

/-- Reflection preserves the exact complex test with its logarithmic tilt weight. -/
theorem pairedEtaPolynomialBoundaryTest_reflection (lambda kappa beta alpha v z : ℝ) :
    pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v (1 - z) =
      (Real.exp (-2 * lambda) : ℂ) *
        pairedEtaPolynomialBoundaryTest (-lambda) (kappa + beta + 3 * alpha)
          (-beta - 6 * alpha) alpha v z := by
  simp only [pairedEtaPolynomialBoundaryTest, pairedEtaPolynomialVelocity_reflection]
  rw [show -2 * lambda * (1 - z) = -2 * lambda + -2 * (-lambda) * z by ring,
    Real.exp_add, Complex.ofReal_mul, mul_assoc]

/-- The phase contributes unit norm to the exact complex test. -/
theorem norm_pairedEtaPolynomialBoundaryTest (lambda kappa beta alpha v z : ℝ) :
    ‖pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v z‖ = Real.exp (-2 * lambda * z) := by
  rw [pairedEtaPolynomialBoundaryTest, norm_mul, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_one]

/-- The polynomial complex test is continuously differentiable. -/
theorem contDiff_pairedEtaPolynomialBoundaryTest (lambda kappa beta alpha v : ℝ) :
    ContDiff ℝ 1 (pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v) := by
  unfold pairedEtaPolynomialBoundaryTest pairedEtaPolynomialVelocity
  have hc : ContDiff ℝ 1 (fun x : ℝ ↦ (x : ℂ)) := Complex.ofRealCLM.contDiff
  exact (hc.comp (by fun_prop : ContDiff ℝ 1 (fun z : ℝ ↦ Real.exp (-2 * lambda * z)))).mul
    (((hc.comp (by fun_prop : ContDiff ℝ 1 (fun z : ℝ ↦ v * (kappa + beta * z + 3 * alpha * z ^ 2)))).mul
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ ↦ Complex.I))).cexp)

/-- The extension preserves the entire interval used by the phase comparison. -/
theorem pairedEtaPolynomialBoundaryTestExtension_eq {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 2)
    (lambda kappa beta alpha v : ℝ) :
    pairedEtaPolynomialBoundaryTestExtension lambda kappa beta alpha v z =
      pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v z := by
  rw [pairedEtaPolynomialBoundaryTestExtension, etaLogScaleClamp_eq_self hz]

/-- A phase-independent uniform bound for the complex extension. -/
theorem norm_pairedEtaPolynomialBoundaryTestExtension_le (lambda kappa beta alpha v z : ℝ) :
    ‖pairedEtaPolynomialBoundaryTestExtension lambda kappa beta alpha v z‖ ≤ Real.exp (4 * |lambda|) := by
  rw [pairedEtaPolynomialBoundaryTestExtension, norm_pairedEtaPolynomialBoundaryTest]
  apply Real.exp_le_exp.mpr
  obtain ⟨hz0, hz2⟩ := etaLogScaleClamp_mem z
  have h := mul_le_mul_of_nonneg_right (neg_le_abs lambda) hz0
  have h' := mul_le_mul_of_nonneg_left hz2 (abs_nonneg lambda)
  nlinarith

/-- The exact derivative retains its complex phase and signed velocity derivative. -/
theorem hasDerivAt_pairedEtaPolynomialBoundaryTest (lambda kappa beta alpha v z : ℝ) :
    HasDerivAt (pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v)
      ((((-2 * lambda : ℝ) : ℂ) + ((v * (beta + 6 * alpha * z) : ℝ) : ℂ) * Complex.I) *
        pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v z) z := by
  have hw := (((hasDerivAt_id z).const_mul (-2 * lambda)).exp).ofReal_comp
  have hp : HasDerivAt (fun x : ℝ ↦ v * pairedEtaPolynomialVelocity kappa beta alpha x)
      (v * (beta + 6 * alpha * z)) z := by
    convert ((((hasDerivAt_id z).const_mul beta).const_add kappa).add
      (((hasDerivAt_id z).pow 2).const_mul (3 * alpha))).const_mul v using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  have hd := hw.mul ((hp.ofReal_comp.mul_const Complex.I).cexp)
  simp only [id_eq, mul_one] at hd
  convert hd using 1 <;>
    first | rfl | (dsimp [pairedEtaPolynomialBoundaryTest]; push_cast; ring)

/-- An explicit Lipschitz constant with its Gaussian-coordinate dependence retained. -/
def pairedEtaPolynomialBoundaryLipschitz (lambda beta alpha v : ℝ) : ℝ≥0 :=
  ⟨Real.exp (4 * |lambda|) * (2 * |lambda| + |v| * (|beta| + 12 * |alpha|)), by positivity⟩

/-- The bounded polynomial test has the explicit Lipschitz constant needed
for domination of its finite part, without any regularity premise. -/
theorem lipschitzWith_pairedEtaPolynomialBoundaryTestExtension (lambda kappa beta alpha v : ℝ) :
    LipschitzWith (pairedEtaPolynomialBoundaryLipschitz lambda beta alpha v)
      (pairedEtaPolynomialBoundaryTestExtension lambda kappa beta alpha v) := by
  let K := pairedEtaPolynomialBoundaryLipschitz lambda beta alpha v
  have hb (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 2) :
      ‖(((-2 * lambda : ℝ) : ℂ) + ((v * (beta + 6 * alpha * z) : ℝ) : ℂ) * Complex.I) *
        pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v z‖ ≤ (K : ℝ) := by
    have hvel : |beta + 6 * alpha * z| ≤ |beta| + 12 * |alpha| := by
      calc
        _ ≤ |beta| + |6 * alpha * z| := abs_add_le _ _
        _ = |beta| + 6 * |alpha| * z := by rw [abs_mul, abs_mul, abs_of_nonneg hz.1]; norm_num
        _ ≤ _ := by nlinarith [hz.2, abs_nonneg alpha]
    have hfac : ‖((-2 * lambda : ℝ) : ℂ) + ((v * (beta + 6 * alpha * z) : ℝ) : ℂ) * Complex.I‖ ≤
        2 * |lambda| + |v| * (|beta| + 12 * |alpha|) := by
      calc
        _ ≤ ‖((-2 * lambda : ℝ) : ℂ)‖ + ‖((v * (beta + 6 * alpha * z) : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = 2 * |lambda| + |v| * |beta + 6 * alpha * z| := by
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
          norm_num [abs_mul]
        _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hvel (abs_nonneg v))
    have htest := norm_pairedEtaPolynomialBoundaryTestExtension_le lambda kappa beta alpha v z
    rw [pairedEtaPolynomialBoundaryTestExtension_eq hz] at htest
    rw [norm_mul]
    exact (mul_le_mul hfac htest (norm_nonneg _) (by positivity)).trans_eq (mul_comm _ _)
  have hK : LipschitzOnWith K (pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v) (Icc 0 2) :=
    (convex_Icc (0 : ℝ) 2).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun z _ ↦ (hasDerivAt_pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v z).hasDerivWithinAt)
      (fun z hz ↦ by exact_mod_cast hb z hz)
  refine lipschitzWith_iff_dist_le_mul.mpr fun x y ↦ ?_
  have hxy := lipschitzOnWith_iff_dist_le_mul.mp hK
    (etaLogScaleClamp x) (etaLogScaleClamp_mem x) (etaLogScaleClamp y) (etaLogScaleClamp_mem y)
  have hc := lipschitzWith_etaLogScaleClamp.dist_le_mul x y
  simp only [NNReal.coe_one, one_mul] at hc
  exact hxy.trans (mul_le_mul_of_nonneg_left hc K.coe_nonneg)

/-- The extension has the same complex boundary integral as the raw test. -/
theorem integral_pairedEtaPolynomialBoundaryTestExtension (lambda kappa beta alpha v : ℝ) :
    (∫ z in 0..1, pairedEtaPolynomialBoundaryTestExtension lambda kappa beta alpha v z) =
      ∫ z in 0..1, pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v z := by
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hz
  exact pairedEtaPolynomialBoundaryTestExtension_eq ⟨hz.1, by linarith [hz.2]⟩ _ _ _ _ _

/-- The actual arithmetic two-endpoint finite part for the complete
polynomial test, including the scale offset at every positive Gaussian coordinate. -/
theorem pairedEtaWeightedMismatch_polynomial_finite_part_tendsto (lambda kappa beta alpha : ℝ)
    {v : ℝ} (hv : 0 < v) :
    Tendsto (fun R : ℝ ↦ (Real.exp (-R))⁻¹ •
      pairedEtaWeightedMismatch (Real.exp (-R) * v) R
        (pairedEtaPolynomialBoundaryTestExtension lambda kappa beta alpha v) -
      (v * R) • (∫ z in 0..1, pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v z)) atTop
      (𝓝 (v • ((Real.eulerMascheroniConstant - 1) •
        pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v 0 +
        (1 - Real.log (Real.pi / 2) - Real.log v) •
          pairedEtaPolynomialBoundaryTest lambda kappa beta alpha v 1))) := by
  simpa only [integral_pairedEtaPolynomialBoundaryTestExtension,
    pairedEtaPolynomialBoundaryTestExtension_eq (show (0 : ℝ) ∈ Icc 0 2 by norm_num),
    pairedEtaPolynomialBoundaryTestExtension_eq (show (1 : ℝ) ∈ Icc 0 2 by norm_num)] using
    pairedEtaWeightedMismatch_exp_scaled_finite_part_tendsto hv
      (lipschitzWith_pairedEtaPolynomialBoundaryTestExtension lambda kappa beta alpha v)
      (norm_pairedEtaPolynomialBoundaryTestExtension_le lambda kappa beta alpha v)

end

end RiemannGaussian
