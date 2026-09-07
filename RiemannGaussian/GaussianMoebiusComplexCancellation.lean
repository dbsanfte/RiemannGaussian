import RiemannGaussian.GaussianMoebiusPhaseHeat

/-!
# Cancellation for the actual complex-weighted Gaussian Möbius sum

Exact heat composition transfers the proved unit-time signed cancellation
to every fixed complex Mellin weight at heat time two. A proved global
arithmetic bound and an integrable fixed-phase kernel discharge dominated
convergence. The normalization retains its full complex phase. This is an
infinite Gaussian sum; estimates for the original divided finite cutoffs
and their completed reflected current remain separate obligations.
-/

open Complex Filter MeasureTheory
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The complete phase-preserving heat integral of the actual normalized Möbius source tends to zero. -/
theorem normalizedGaussianMoebius_heat_integral_tendsto_zero (s : ℂ) :
    Tendsto (fun a : ℝ ↦ ∫ v : ℝ,
      (normalizedGaussianMoebius (a + v) : ℂ) * complexGaussianMoebiusHeatKernel s v)
      atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_bound_normalizedGaussianMoebius
  have h := tendsto_integral_filter_of_dominated_convergence
    (F := fun a v : ℝ ↦ (normalizedGaussianMoebius (a + v) : ℂ) * complexGaussianMoebiusHeatKernel s v)
    (f := fun _ : ℝ ↦ (0 : ℂ))
    (fun v : ℝ ↦ C * ‖complexGaussianMoebiusHeatKernel s v‖)
    (Eventually.of_forall (aestronglyMeasurable_normalizedGaussianMoebius_heat s))
    (Eventually.of_forall fun a ↦ Eventually.of_forall fun v ↦ by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hC (a + v)) (norm_nonneg _))
    ((integrable_complexGaussianMoebiusHeatKernel s).norm.const_mul C)
    (Eventually.of_forall fun v ↦ by
      have hshift : Tendsto (fun a : ℝ ↦ a + v) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_id
      simpa using (normalizedGaussianMoebius_tendsto_zero.comp hshift).ofReal.mul_const
        (complexGaussianMoebiusHeatKernel s v))
  simpa using h

/-- Every fixed complex Mellin weight has actual signed Gaussian cancellation at heat time two, with full complex normalization. -/
theorem complexGaussianMoebiusSum_two_normalized_tendsto_zero (s : ℂ) :
    Tendsto (fun a : ℝ ↦ Complex.exp ((s - 1) * (a : ℂ)) * complexGaussianMoebiusSum s a 2)
      atTop (𝓝 0) := by
  simp_rw [complexGaussianMoebiusSum_two_normalized_heat_identity]
  simpa using (normalizedGaussianMoebius_heat_integral_tendsto_zero s).const_mul
    (((Real.sqrt (2 * Real.pi) : ℂ) * Complex.exp (2 * s ^ 2))⁻¹)

/-- Taking norms preserves the precise real arithmetic scale of the checked complex cancellation. -/
theorem complexGaussianMoebiusSum_two_norm_ratio_tendsto_zero (s : ℂ) :
    Tendsto (fun a : ℝ ↦ ‖complexGaussianMoebiusSum s a 2‖ / Real.exp ((1 - s.re) * a))
      atTop (𝓝 0) := by
  have h := (complexGaussianMoebiusSum_two_normalized_tendsto_zero s).norm
  simp only [norm_mul, Complex.norm_exp, norm_zero] at h
  have hre (a : ℝ) : (((s - 1) * (a : ℂ))).re = (s.re - 1) * a := by
    simp
  simp_rw [hre] at h
  convert h using 1
  funext a
  rw [div_eq_mul_inv, ← Real.exp_neg, mul_comm]
  congr 2
  ring

/-- On the multiplicative scale, the original complex powers multiply the actual weighted arithmetic sum and converge to zero. -/
theorem complexGaussianMoebiusSum_log_two_normalized_tendsto_zero (s : ℂ) :
    Tendsto (fun X : ℝ ↦ (X : ℂ) ^ (s - 1) * complexGaussianMoebiusSum s (Real.log X) 2)
      atTop (𝓝 0) := by
  have h := (complexGaussianMoebiusSum_two_normalized_tendsto_zero s).comp Real.tendsto_log_atTop
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  dsimp only [Function.comp_apply]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hX.ne'),
    Complex.ofReal_log hX.le]
  congr 2
  ring

/-- The norm of the actual complex-weighted Gaussian Möbius sum is o(X^(1-Re(s))) for each fixed complex s. -/
theorem complexGaussianMoebiusSum_log_two_norm_ratio_tendsto_zero (s : ℂ) :
    Tendsto (fun X : ℝ ↦ ‖complexGaussianMoebiusSum s (Real.log X) 2‖ / X ^ (1 - s.re))
      atTop (𝓝 0) := by
  have h := (complexGaussianMoebiusSum_two_norm_ratio_tendsto_zero s).comp Real.tendsto_log_atTop
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  dsimp only [Function.comp_apply]
  rw [Real.rpow_def_of_pos hX]
  congr 2
  ring

end

end RiemannGaussian
