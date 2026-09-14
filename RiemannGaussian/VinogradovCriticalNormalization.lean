/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovCriticalExponent

/-!
# The actual critical moment budget at all padded quotient scales

The proved critical high-moment exponent plus any positive epsilon gives
one common constant and finite threshold for every eligible actual padded
quotient. Rounding is paid by the existing exact factor. No homogeneous
moment budget is assumed; the terminal supplies it from the global proof.
-/

namespace RiemannGaussian.VinogradovCriticalNormalization
noncomputable section
open scoped Classical BigOperators
open VinogradovMeanValue VinogradovConditioningRemainder VinogradovConditioningPowerSaving
open VinogradovNormalizedIteration VinogradovCongruencingScaling
open VinogradovProfileIteration VinogradovProfileSaving

/-- The independently proved critical exponent plus any positive epsilon pays every actual padded quotient with one common constant and threshold. -/
theorem exists_critical_rounded_budget (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u)
    (eps : ℝ) (heps : 0 < eps) :
    let lam := 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 + eps
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N₀ : ℕ, ∀ p a X : ℕ,
      0 < p → p ^ a ≤ X → N₀ ≤ X / p ^ a + 1 →
        meanValue ((u + 1) * k) k (X / p ^ a + 1) ≤
          C * ((X : ℝ) / (p : ℝ) ^ a) ^ lam := by
  let lam := 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 + eps
  have hlam : 0 ≤ lam := by
    have hc := VinogradovExponentBootstrap.critical_exponent_gt_one hk hu
    unfold lam
    linarith
  obtain ⟨C, hC, N₀, hJ⟩ :=
    VinogradovCriticalExponent.exists_global_critical_exponent k u hk hu eps heps
  refine ⟨max 1 (C * (2 : ℝ) ^ lam), le_max_left _ _, N₀, ?_⟩
  intro p a X hp hX hN
  have he := VinogradovImprovedNormalization.rounded_actual_meanValue hC.le hlam hp hX hN hJ
  exact he.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end
end RiemannGaussian.VinogradovCriticalNormalization
