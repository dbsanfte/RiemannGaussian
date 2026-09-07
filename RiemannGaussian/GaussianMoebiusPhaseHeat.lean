import RiemannGaussian.GaussianMoebiusPhaseAtom
import RiemannGaussian.GaussianMoebiusNormalized

/-!
# Exact heat transport of the full complex-weighted Möbius sum

The original normalized signed unit-time sum is convolved against the
integrable complex heat kernel. Absolute convergence of the norm integrals
justifies the infinite arithmetic exchange. The result retains the complete
Mellin phase at heat time two, before any estimate or limiting operation.
-/

open Complex Filter MeasureTheory

namespace RiemannGaussian

noncomputable section

/-- The whole arithmetic heat source is exactly the series of its signed phase atoms. -/
theorem tsum_complexGaussianMoebiusHeatTerm (s : ℂ) (a v : ℝ) :
    (∑' n : ℕ, complexGaussianMoebiusHeatTerm s a n v) =
      (normalizedGaussianMoebius (a + v) : ℂ) * complexGaussianMoebiusHeatKernel s v := by
  unfold complexGaussianMoebiusHeatTerm normalizedGaussianMoebius gaussianMoebiusSum
  simp_rw [Complex.ofReal_div]
  rw [tsum_mul_right, tsum_div_const, Complex.ofReal_tsum]

/-- The full complex heat source is measurable at every actual arithmetic center. -/
theorem aestronglyMeasurable_normalizedGaussianMoebius_heat (s : ℂ) (a : ℝ) :
    AEStronglyMeasurable (fun v : ℝ ↦
      (normalizedGaussianMoebius (a + v) : ℂ) * complexGaussianMoebiusHeatKernel s v) := by
  convert (aestronglyMeasurable_normalizedGaussianMoebius_add a).mul
    (integrable_complexGaussianMoebiusHeatKernel s).aestronglyMeasurable using 1
  rfl

/-- The proved global arithmetic bound supplies an integrable dominator for each fixed full complex phase. -/
theorem integrable_normalizedGaussianMoebius_heat (s : ℂ) (a : ℝ) :
    Integrable (fun v : ℝ ↦
      (normalizedGaussianMoebius (a + v) : ℂ) * complexGaussianMoebiusHeatKernel s v) := by
  obtain ⟨C, _, hC⟩ := exists_bound_normalizedGaussianMoebius
  apply ((integrable_complexGaussianMoebiusHeatKernel s).norm.const_mul C).mono'
    (aestronglyMeasurable_normalizedGaussianMoebius_heat s a)
  exact Eventually.of_forall fun v ↦ by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC (a + v)) (norm_nonneg _)

/-- Integrating the complete signed arithmetic source gives the actual complex-weighted Gaussian sum, with exact phase and normalization. -/
theorem integral_normalizedGaussianMoebius_heat (s : ℂ) (a : ℝ) :
    (∫ v : ℝ, (normalizedGaussianMoebius (a + v) : ℂ) *
      complexGaussianMoebiusHeatKernel s v) =
      ((Real.sqrt (2 * Real.pi) : ℂ) * Complex.exp ((s - 1) * (a : ℂ) + 2 * s ^ 2)) *
        complexGaussianMoebiusSum s a 2 := by
  simp_rw [← tsum_complexGaussianMoebiusHeatTerm]
  rw [← integral_tsum_of_summable_integral_norm (integrable_complexGaussianMoebiusHeatTerm s a)
    (summable_integral_norm_complexGaussianMoebiusHeatTerm s a)]
  simp_rw [integral_complexGaussianMoebiusHeatTerm]
  rw [tsum_mul_left, complexGaussianMoebiusSum]

/-- The normalization isolates a fixed complex heat multiplier, independent of the arithmetic center. -/
theorem complexGaussianMoebiusSum_two_normalized_heat_identity (s : ℂ) (a : ℝ) :
    Complex.exp ((s - 1) * (a : ℂ)) * complexGaussianMoebiusSum s a 2 =
      ((Real.sqrt (2 * Real.pi) : ℂ) * Complex.exp (2 * s ^ 2))⁻¹ *
        ∫ v : ℝ, (normalizedGaussianMoebius (a + v) : ℂ) *
          complexGaussianMoebiusHeatKernel s v := by
  have hsq : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < 2 * Real.pi)).ne'
  rw [integral_normalizedGaussianMoebius_heat, Complex.exp_add]
  field_simp

end

end RiemannGaussian
