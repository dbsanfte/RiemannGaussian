/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovIntervalResonance
import RiemannGaussian.VinogradovCriticalKorobov

/-!
# Explicit resonance and both critical moments in the actual product sum

The original polynomial product sum is bounded by its proved critical
moments, quartered Gaussian smoothing cost and an explicit finite resonance
allowance. Exact logarithmic coefficients include the Fourier normalization.
This general bound is not a uniform zeta-growth theorem. Quantitative costs
and a useful parameter regime must still be checked downstream.
-/

namespace RiemannGaussian.VinogradovExplicitKorobov
noncomputable section
open scoped BigOperators
open VinogradovGaussianBounds VinogradovGaussianKernel
open VinogradovIntervalResonance

/-- The exact logarithmic polynomial coefficient has its literal magnitude, including the Fourier normalization. -/
theorem abs_phaseCoefficients (k : ℕ) (t : ℝ) {z : ℝ} (hz : 0 < z) (j : Fin k) :
    |VinogradovKorobovMoment.phaseCoefficients k t z j| =
      |t| / ((j.val + 1) * z ^ (j.val + 1)) / (2 * Real.pi) := by
  have hd : 0 < ((j.val : ℝ) + 1) * z ^ (j.val + 1) := by positivity
  have hp : 0 < 2 * Real.pi := by positivity
  simp only [VinogradovKorobovMoment.phaseCoefficients, abs_div]
  rw [abs_of_pos hd, abs_of_pos hp, abs_mul]
  simp

/-- Both critical high moments and the actual joint resonance factor in the Korobov product sum are bounded by proved finite expressions. -/
theorem exists_critical_explicit_product_bound (k u v : ℕ) (hk : 2 ≤ k) (hu : k ≤ u) (hv : k ≤ v)
    (eps : ℝ) (heps : 0 < eps) :
    let r := (u + 1) * k
    let s := (v + 1) * k
    let lamr := 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 + eps
    let lams := 2 * (k : ℝ) * ((v : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 + eps
    ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℕ, ∃ D : ℝ, 0 < D ∧ ∃ Y₀ : ℕ,
      ∀ M Y : ℕ, M₀ ≤ M → Y₀ ≤ Y → ∀ (t z : ℝ) (B : Finset ℕ),
      (∀ b ∈ B, 1 ≤ b ∧ b ≤ Y) → ∀ a : Fin k → ℝ, (∀ j, 0 < a j) →
      ‖∑ b : Fin M, ∑ c ∈ B,
          VinogradovKorobovBilinearPhase.polynomialPhase k t z ((b.val + 1 : ℕ) : ℝ) c‖ ^ (2 * r * s) ≤
        (B.card : ℝ) ^ ((r - 1) * (2 * s)) * (M : ℝ) ^ (r * (2 * s - 2)) *
          (C * (M : ℝ) ^ lamr) *
          Real.exp (VinogradovGaussianKernel.supportCost a
            (VinogradovMomentReduction.frequencySupport (VinogradovShiftedMoment.tupleFrequency r
              (fun b : Fin M => VinogradovMeanValue.monomialFrequency k (b.val + 1)))) / 4) *
          (D * (Y : ℝ) ^ lams) *
          intervalResonanceAllowance s Y a (VinogradovKorobovMoment.phaseCoefficients k t z) := by
  obtain ⟨C, hC, M₀, D, hD, Y₀, h⟩ :=
    VinogradovCriticalKorobov.exists_critical_product_bound k u v hk hu hv eps heps
  refine ⟨C, hC, M₀, D, hD, Y₀, ?_⟩
  intro M Y hM hY t z B hB a ha
  apply (h M Y hM hY t z B hB a ha).trans
  apply mul_le_mul_of_nonneg_left
    (actual_resonance_le_allowance k ((v + 1) * k) Y B (fun b hb => (hB b hb).2) ha
      (VinogradovKorobovMoment.phaseCoefficients k t z))
  positivity

end
end RiemannGaussian.VinogradovExplicitKorobov
