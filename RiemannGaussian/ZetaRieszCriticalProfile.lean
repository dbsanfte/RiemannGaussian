/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszNegativeProfile
import RiemannGaussian.VinogradovCriticalNormalization

/-!
# The original Riesz carrier at the critical homogeneous exponent

For every positive epsilon, the actual original carrier at a=0,b=1 uses
the critical homogeneous exponent plus epsilon and an independently proved
negative initial-energy profile. All homogeneous and descendant-energy
premises are discharged. The original signed complex fibre averages,
attained-frequency and residue costs, and positive lower block mass remain.

Prime-size and coupled actual cutoff conditions remain explicit. Constants,
negative exponent and thresholds are unevaluated. A net saving after the
remaining correlation and sampling costs, RH and a wider zero-free region
are not proved here.
-/

namespace RiemannGaussian.ZetaRieszCriticalProfile
noncomputable section
open scoped Classical BigOperators
open VinogradovMeanValue VinogradovConditioningRemainder VinogradovConditioningPowerSaving
open VinogradovNormalizedIteration VinogradovCongruencingScaling
open VinogradovProfileIteration VinogradovProfileSaving
open ZetaRieszConditionedEnergy ZetaRieszBlockMass ZetaRieszConditioningTransfer

open VinogradovCriticalNormalization

/-- The original Riesz carrier has an independent negative initial-energy profile at the critical homogeneous exponent plus any positive epsilon. -/
theorem exists_original_band_critical_profile (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u)
    (eps : ℝ) (heps : 0 < eps) :
    let lam := 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 + eps
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N₀ : ℕ, ∃ beta : ℝ, -(1 / 2 : ℝ) ≤ beta ∧ beta < 0 ∧
      ∃ S : ℕ, 2 ≤ S ∧ ∃ B : ℝ, 1 ≤ B ∧ ∀ (p N : ℕ) [Fact p.Prime],
      p ^ S ≤ 2 ^ (32 * N) → N₀ ≤ 2 ^ (32 * N) / p ^ S + 1 →
      (C * iterationConstant k u) ^ 2 ≤ (p : ℝ) →
      ∀ (colour : Fin k → Bool) (L : ℝ) (P : Polynomial ℂ) (y : ℝ),
        ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y‖ ^ (2 * (k * u)) ≤
          (correlatedSamplingCost p k 0 1 (k * u) 0 colour L P N y *
            (momentScale ((2 ^ (32 * N) : ℕ) : ℝ) p k u 0 1 lam *
              (B * (p : ℝ) ^ beta))) / (lowerBlockMass p k 0 N : ℝ) ^ 2 := by
  let lam := 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 + eps
  have hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 < lam := by
    unfold lam
    linarith
  obtain ⟨C, hC, N₀, hbudget⟩ := exists_critical_rounded_budget k u hk hu eps heps
  obtain ⟨beta, hbetalow, hbeta, S, hS, B, hB, hallow⟩ := exists_initial_allowance_saving hk hu hC hlam hbudget
  refine ⟨C, hC, N₀, beta, hbetalow, hbeta, S, hS, B, hB, ?_⟩
  intro p N inst hX hN hp colour L P y
  have hp0 := Nat.Prime.pos (Fact.out : p.Prime)
  have hXpos : 0 < 2 ^ (32 * N) := by positivity
  obtain ⟨hX0, hN0⟩ := quotient_budget_mono hp0 (show 0 ≤ S by omega) hX hN
  obtain ⟨hX2, hN2⟩ := quotient_budget_mono hp0 hS hX hN
  have hiteration := mixed_le_scale_allowance_of_scaled_bounds (a := 0) (b := 1) (xi := 0)
    (H := 1) hk hu (by omega) (by omega) (by omega) hXpos hC hlam.le hp
    (hbudget p 0 (2 ^ (32 * N)) hp0 hX0 hN0) (hbudget p 2 (2 ^ (32 * N)) hp0 hX2 hN2) colour
  have hscale := momentScale_pos (show (0 : ℝ) < (2 ^ (32 * N) : ℕ) by positivity)
    (show (0 : ℝ) < p by exact_mod_cast hp0) (k : ℝ) (u : ℝ) 0 1 lam
  have hI := hiteration.trans (mul_le_mul_of_nonneg_left
    (hallow p 0 (2 ^ (32 * N)) hX hN hp colour)
      (by simpa only [Nat.cast_zero, Nat.cast_one] using hscale.le))
  have hkp := degree_lt_of_budget hk hu hC hp
  have hXa : p ^ (0 + 1) ≤ 2 ^ (32 * N) :=
    (Nat.pow_le_pow_right (by omega : 1 ≤ p) (by omega : 0 + 1 ≤ S)).trans hX
  have hmass : 0 < (lowerBlockMass p k 0 N : ℝ) := by exact_mod_cast lowerBlockMass_pos hkp hXa
  have hcount : (lowerBlockMass p k 0 N : ℝ) ≤ (blockCount p k 0 0 N : ℝ) := by
    exact_mod_cast (lowerBlockMass_le_blockCount (p := p) (k := k) (a := 0) (N := N))
  rw [le_div_iff₀ (sq_pos_of_pos hmass), mul_comm]
  calc
    _ ≤ (blockCount p k 0 0 N : ℝ) ^ 2 *
        ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y‖ ^ (2 * (k * u)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hmass.le hcount 2) (by positivity)
    _ ≤ correlatedSamplingCost p k 0 1 (k * u) 0 colour L P N y *
        levelMixedMaximum p k 0 1 0 (2 ^ (32 * N)) u colour :=
      actual_band_le_correlated_level (Nat.mul_pos (by omega) (by omega)) colour L P N y
    _ ≤ _ := by
      simpa only [Nat.cast_zero, Nat.cast_one] using mul_le_mul_of_nonneg_left hI
        (correlatedSamplingCost_nonneg p k 0 1 (k * u) 0 colour L P N y)

end
end RiemannGaussian.ZetaRieszCriticalProfile
