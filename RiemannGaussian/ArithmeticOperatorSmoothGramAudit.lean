/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorGramAudit
import RiemannGaussian.ZetaRieszPhaseDensityAudit

/-!
# A positive smooth density is coherent and satisfies every free Gram bound

The earlier exact resonant density model is reused, not asserted for primes.
Its FULL density factorial transform (including the continuous pole mode)
converges to any chosen negative integer at a campaign height. The density
is eventually positive and its relative error is smaller than every fixed
inverse logarithmic power. Every deterministic finite Gram feature lift
still satisfies the free PSD inequality on its positive-scale tail.

This rejects positivity/PNT-envelope/Gram arguments alone. The model does
NOT satisfy the complete exact integer Gamma observations; finite-prefix
uniqueness separately proves that these determine actual Mangoldt weights.
-/

namespace RiemannGaussian.ArithmeticOperatorSmoothGramAudit
noncomputable section
open Complex Filter MeasureTheory Set
open GaussianSimplePoleHeat ZetaRieszPhaseDensityAudit ArithmeticOperatorGramAudit
open scoped Topology BigOperators

/-- Positive-tail smooth control with the conjugate resonant pair retained. -/
def modelDensity (m : ℕ) (u y T : ℝ) : ℝ := 1+densityError (-(2*m : ℝ)) u y T

/-- Full factorial moment, not merely the bias with its pole omitted. -/
def modelMoment (m : ℕ) (u y : ℝ) (N : ℕ) : ℂ :=
  (u : ℂ)^(N+1)*∫ T : ℝ in Ioi 0,
    (modelDensity m u y T : ℂ)*laplace N (1/2+I*y) T

theorem base_norm_lt_one {u y : ℝ} (hu : 0 < u) (hu1 : u < 1) (hy : 54 ≤ |y|) :
    ‖(u : ℂ)/(1/2+I*y)‖ < 1 := by
  have hz : (1/2+I*(y : ℂ)) ≠ 0 := by
    intro hz
    have hh := congrArg Complex.re hz
    norm_num at hh
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hz), Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hu]
  apply (sq_lt_sq₀ hu.le (norm_nonneg _)).mp
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply]
  simp
  have hh : 54^2 ≤ y^2 := by nlinarith [sq_abs y]
  nlinarith

/-- Exact density-plus-resonance decomposition before any norm estimate. -/
theorem modelMoment_eq (m : ℕ) {u : ℝ} (hu : 0 < u) (y : ℝ) (N : ℕ) :
    modelMoment m u y N =
      ((u : ℂ)/(1/2+I*y))^(N+1)-
        (m : ℂ)*(1+((u : ℂ)/((u : ℂ)+2*I*y))^(N+1)) := by
  have hi : IntegrableOn (fun T : ℝ =>
      (densityError (-(2*m : ℝ)) u y T : ℂ)*laplace N (1/2+I*y) T) (Ioi 0) := by
    simp_rw [error_atom_eq]
    exact ((integrableOn_laplace N (by simpa using hu)).add
      (integrableOn_laplace N (by simpa using hu))).const_mul _
  unfold modelMoment modelDensity
  simp only [Complex.ofReal_add, Complex.ofReal_one, add_mul, one_mul]
  rw [integral_add (integrableOn_laplace N (by norm_num)) hi, mul_add,
    integral_laplace N (by norm_num), integral_error N hu]
  push_cast
  rw [div_pow]
  simp only [div_eq_mul_inv]
  ring

/-- Arbitrary fixed negative-integer coherence is compatible with a
positive smooth density and the unchanged full complex factorial phase. -/
theorem tendsto_modelMoment (m : ℕ) {u y : ℝ} (hu : 1/2 < u)
    (hu1 : u < 1) (hy : 54 ≤ |y|) :
    Tendsto (modelMoment m u y) atTop (𝓝 (-(m : ℂ))) := by
  have hu0 : 0 < u := by linarith
  have hy0 : y ≠ 0 := by intro h; norm_num [h] at hy
  change Tendsto (fun N => modelMoment m u y N) atTop (𝓝 (-(m : ℂ)))
  simp_rw [modelMoment_eq m hu0]
  have hb := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    (base_norm_lt_one hu0 hu1 hy)).comp (tendsto_add_atTop_nat 1)
  have ha := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    (alias_norm_lt_one hu0 hy0)).comp (tendsto_add_atTop_nat 1)
  simpa using hb.sub ((ha.const_add 1).const_mul (m : ℂ))

/-- The model satisfies every fixed inverse-logarithmic PNT envelope. -/
theorem model_relative_error_small (m : ℕ) {u : ℝ} (hu : 1/2 < u) (y : ℝ) (b : ℕ) :
    Tendsto (fun T : ℝ => T^b*(modelDensity m u y T-1)) atTop (𝓝 0) := by
  simpa only [modelDensity, add_sub_cancel_left] using
    densityError_faster_than_inverse_power hu (-(2*m : ℝ)) y b

/-- Uniform collapse audit over ALL deterministic finite feature matrices.
On the model's positive tail, divisor/quotient/modular/Gaussian feature
Grams are nonnegative while its factorial moments remain coherent.
No complete exact integer Gamma observation is claimed for this model. -/
theorem model_satisfies_all_tail_grams (m : ℕ) {u : ℝ} (hu : 1/2 < u) (y : ℝ) :
    ∃ T0 : ℝ, ∀ (ι κ : Type*) (S : Finset ι) (D : Finset κ)
      (alpha : ι → ℂ) (feature : ι → κ → ℂ) (time : κ → ℝ),
      (∀ d ∈ D, T0 ≤ time d) →
      0 ≤ (joinedGram S D alpha feature
        (fun d => (modelDensity m u y (time d) : ℂ))).re := by
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp
    (eventually_density_positive hu (-(2*m : ℝ)) y)
  refine ⟨T0, ?_⟩
  intro ι κ S D alpha feature time htime
  exact joinedGram_nonnegative_for_arbitrary_weights S D alpha feature
    (fun d => modelDensity m u y (time d))
    (fun d hd => (hT0 (time d) (htime d hd)).le)

end
end RiemannGaussian.ArithmeticOperatorSmoothGramAudit
