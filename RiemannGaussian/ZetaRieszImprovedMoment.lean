/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszConditioningTransfer
import RiemannGaussian.VinogradovImprovedNormalization

/-!
# The improved global moment exponent in the original signed Riesz carrier

The independently proved exponent k(2u+1)-1/(3k) bounds both actual padded
quotient moments. It supplies a direct two-scale bound and the complete
finite conditioned-energy recurrence for the original Riesz band. No
homogeneous or weighted moment estimate is assumed. The quotient threshold
and every finite-scale condition remain explicit.

The actual complex fibre averages, attained-frequency sampling cost,
residue factor, and positive lower block mass are retained. The full
intermediate energy sum is preserved in the terminal iteration theorem.
A net arithmetic saving after all costs, RH, and a larger zero-free region
remain open. Constants and thresholds depend on k,u and are not evaluated.
-/

namespace RiemannGaussian.ZetaRieszImprovedMoment
noncomputable section
open scoped Classical BigOperators
open VinogradovMeanValue VinogradovConditioningRemainder VinogradovConditioningPowerSaving
open VinogradovNormalizedIteration VinogradovCongruencingScaling
open ZetaRieszConditionedEnergy ZetaRieszBlockMass ZetaRieszConditioningTransfer
open VinogradovImprovedNormalization

/-- The first independently proved global moment exponent bounds the original Riesz carrier, retaining its complete actual complex correlation and sampling cost. -/
theorem exists_original_band_improved_moment_bound (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N₀ : ℕ, ∀ (p a b N : ℕ),
      k < p → a ≤ b → p ^ (a + 1) ≤ 2 ^ (32 * N) → p ^ b ≤ 2 ^ (32 * N) →
      N₀ ≤ 2 ^ (32 * N) / p ^ b + 1 →
      ∀ (colour : Fin k → Bool) (L : ℝ) (P : Polynomial ℂ) (y : ℝ),
        ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y‖ ^ (2 * (k * u)) ≤
          (correlatedSamplingCost p k a b (k * u) 0 colour L P N y * C *
            ((((2 ^ (32 * N) : ℕ) : ℝ) / (p : ℝ) ^ a) ^
              (((((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ)))) / ((u + 1 : ℕ) : ℝ)) *
             (((2 ^ (32 * N) : ℕ) : ℝ) / (p : ℝ) ^ b) ^
              (((((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ)))) * u / ((u + 1 : ℕ) : ℝ)))) /
                (lowerBlockMass p k a N : ℝ) ^ 2 := by
  obtain ⟨C, hC, N₀, hbudget⟩ := exists_improved_rounded_budget k u hk hu
  refine ⟨C, hC, N₀, ?_⟩
  intro p a b N hkp hab hXa hXb hN colour L P y
  have hp : 0 < p := by omega
  let : NeZero p := ⟨hp.ne'⟩
  have hpow : p ^ a ≤ p ^ b := Nat.pow_le_pow_right (by omega : 1 ≤ p) hab
  have hquot : 2 ^ (32 * N) / p ^ b ≤ 2 ^ (32 * N) / p ^ a :=
    (Nat.le_div_iff_mul_le (Nat.pow_pos hp)).mpr
      ((Nat.mul_le_mul_left _ hpow).trans (Nat.div_mul_le_self (2 ^ (32 * N)) (p ^ b)))
  have hJ := hbudget p a (2 ^ (32 * N)) hp (hpow.trans hXb) (by omega)
  have hJb := hbudget p b (2 ^ (32 * N)) hp hXb hN
  have hI : levelMixedMaximum p k a b 0 (2 ^ (32 * N)) u colour ≤ C *
      ((((2 ^ (32 * N) : ℕ) : ℝ) / (p : ℝ) ^ a) ^
        (((((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ)))) / ((u + 1 : ℕ) : ℝ)) *
       (((2 ^ (32 * N) : ℕ) : ℝ) / (p : ℝ) ^ b) ^
        (((((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ)))) * u / ((u + 1 : ℕ) : ℝ))) := by
    unfold levelMixedMaximum
    apply Finset.sup'_le Finset.univ_nonempty
    intro eta heta
    exact mixed_le_of_scaled_bounds (by omega) hC hJ hJb colour
  have hmass : 0 < (lowerBlockMass p k a N : ℝ) := by
    exact_mod_cast lowerBlockMass_pos hkp hXa
  have hcount : (lowerBlockMass p k a N : ℝ) ≤ (blockCount p k a 0 N : ℝ) := by
    exact_mod_cast (lowerBlockMass_le_blockCount (p := p) (k := k) (a := a) (N := N))
  rw [le_div_iff₀ (sq_pos_of_pos hmass), mul_comm]
  calc
    _ ≤ (blockCount p k a 0 N : ℝ) ^ 2 *
        ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y‖ ^ (2 * (k * u)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hmass.le hcount 2) (by positivity)
    _ ≤ correlatedSamplingCost p k a b (k * u) 0 colour L P N y *
        levelMixedMaximum p k a b 0 (2 ^ (32 * N)) u colour :=
      actual_band_le_correlated_level (Nat.mul_pos (by omega) (by omega)) colour L P N y
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hI
        (correlatedSamplingCost_nonneg p k a b (k * u) 0 colour L P N y)


/-- The original Riesz carrier receives the full improved-exponent conditioning bound with both homogeneous moment premises discharged and all intermediate energies retained. -/
theorem exists_original_band_improved_iteration (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N₀ : ℕ, ∀ (p a b N H : ℕ) [NeZero p],
      a ≤ b → 1 ≤ H → b - a ≤ 2 * H → p ^ (b + H) ≤ 2 ^ (32 * N) →
      N₀ ≤ 2 ^ (32 * N) / p ^ (b + H) + 1 →
      (C * iterationConstant k u) ^ 2 ≤ (p : ℝ) →
      ∀ (colour : Fin k → Bool) (L : ℝ) (P : Polynomial ℂ) (y : ℝ),
        ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y‖ ^ (2 * (k * u)) ≤
          (correlatedSamplingCost p k a b (k * u) 0 colour L P N y *
            (momentScale ((2 ^ (32 * N) : ℕ) : ℝ) p k u a b
              ((((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ)))) *
            conditioningAllowance p k a b 0 (2 ^ (32 * N)) u H colour
              ((((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ)))))) /
                (lowerBlockMass p k a N : ℝ) ^ 2 := by
  obtain ⟨C, hC, N₀, hbound⟩ := exists_improved_mixed_iteration k u hk hu
  refine ⟨C, hC, N₀, ?_⟩
  intro p a b N H inst hab hH hgap hX hN hp colour L P y
  have hkp := degree_lt_of_budget hk hu hC hp
  have hXa : p ^ (a + 1) ≤ 2 ^ (32 * N) :=
    (Nat.pow_le_pow_right (by omega : 1 ≤ p) (by omega : a + 1 ≤ b + H)).trans hX
  have hmass : 0 < (lowerBlockMass p k a N : ℝ) := by exact_mod_cast lowerBlockMass_pos hkp hXa
  have hcount : (lowerBlockMass p k a N : ℝ) ≤ (blockCount p k a 0 N : ℝ) := by
    exact_mod_cast (lowerBlockMass_le_blockCount (p := p) (k := k) (a := a) (N := N))
  rw [le_div_iff₀ (sq_pos_of_pos hmass), mul_comm]
  calc
    _ ≤ (blockCount p k a 0 N : ℝ) ^ 2 *
        ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y‖ ^ (2 * (k * u)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hmass.le hcount 2) (by positivity)
    _ ≤ correlatedSamplingCost p k a b (k * u) 0 colour L P N y *
        levelMixedMaximum p k a b 0 (2 ^ (32 * N)) u colour :=
      actual_band_le_correlated_level (Nat.mul_pos (by omega) (by omega)) colour L P N y
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hbound p a b 0 (2 ^ (32 * N)) H hab hH hgap hX hN hp colour)
      (correlatedSamplingCost_nonneg p k a b (k * u) 0 colour L P N y)

end
end RiemannGaussian.ZetaRieszImprovedMoment
