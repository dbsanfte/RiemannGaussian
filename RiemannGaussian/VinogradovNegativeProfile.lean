/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovProfileIteration

/-!
# Independent negative profiles for actual conditioned energies

For any homogeneous moment budget above the critical exponent, the affine
profile becomes negative after finitely many checked congruencing steps.
The independently proved first global moment theorem supplies that budget
unconditionally. Hence the entire initial conditioned level, including
all residues and colours, has a negative prime-power profile under the
explicit coupled prime/cutoff conditions. All later-energy and homogeneous
moment premises are discharged in the two improved-exponent terminals.

The constants and finite depth are existential and not numerically evaluated.
This is a conditioned-energy estimate, not yet weighted Riesz decay or a
new zero-free region.
-/

namespace RiemannGaussian.VinogradovNegativeProfile
noncomputable section
open scoped Classical BigOperators
open VinogradovProfileIteration
open VinogradovMeanValue VinogradovConditioningRemainder VinogradovConditioningPowerSaving
open VinogradovNormalizedIteration VinogradovCongruencingScaling VinogradovNonsingularConditioning

/-- Any rounded homogeneous budget strictly above the critical exponent yields an actual negative conditioned profile after finitely many steps. -/
theorem exists_negative_profile {k u N₀ : ℕ} {C lam : ℝ}
    (hk : 2 ≤ k) (hu : k ≤ u) (hC : 1 ≤ C)
    (hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 < lam)
    (hbudget : ∀ p e X : ℕ, 0 < p → p ^ e ≤ X → N₀ ≤ X / p ^ e + 1 →
      meanValue ((u + 1) * k) k (X / p ^ e + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ e) ^ lam) :
    let delta := lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2
    ∃ beta : ℝ, beta < 0 ∧ ∃ T : ℕ, 1 ≤ T ∧ ∃ B : ℝ, 1 ≤ B ∧
      ∀ (p a b xi eta X : ℕ) [Fact p.Prime],
      a < b → p ^ (T * b) ≤ X → N₀ ≤ X / p ^ (T * b) + 1 →
      (C * iterationConstant k u) ^ 2 ≤ (p : ℝ) → eta < p ^ b →
      ∀ colourA colourB : Fin k → Bool,
      conditionedMoment p k a b xi eta X u colourA colourB / momentScale X p k u a b lam ≤
        B * (p : ℝ) ^ (delta * a + beta * b) := by
  let delta := lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2
  have hd : 0 < delta := by unfold delta; linarith
  have hu1 : (1 : ℝ) < u := by exact_mod_cast (by omega : 1 < u)
  have hr : (k : ℝ) / u ≤ 1 := (div_le_one (by linarith)).mpr (by exact_mod_cast hu)
  have hc : 0 < (1 - 1 / (u : ℝ)) * delta := by
    have he : 1 / (u : ℝ) < 1 := (div_lt_one (by linarith)).mpr hu1
    exact mul_pos (by linarith) hd
  obtain ⟨n, hn⟩ := exists_negative_affineProfile (B := (k : ℝ) * u) hr hc
  obtain ⟨T, hT, B, hB, he⟩ := uniform_profile_iteration k u hk hu hC hlam.le hbudget n
  exact ⟨_, hn, T, hT, B, hB, he⟩

/-- The independently proved first exponent has strictly positive defect above the critical mean-value exponent. -/
theorem first_exponent_gt_critical {k u : ℕ} (hk : 2 ≤ k) :
    2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 <
      (((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ))) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hfrac : 1 / (3 * (k : ℝ)) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hgap : 1 ≤ (k : ℝ) * ((k : ℝ) - 1) / 2 := by nlinarith
  push_cast
  nlinarith

/-- The actual improved global moment theorem supplies every homogeneous premise of a negative conditioned profile, uniformly in all original residues and colours. -/
theorem exists_improved_negative_profile (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u) :
    let lam : ℝ := (((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ)))
    let delta := lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N₀ : ℕ, ∃ beta : ℝ, beta < 0 ∧
      ∃ T : ℕ, 1 ≤ T ∧ ∃ B : ℝ, 1 ≤ B ∧
      ∀ (p a b xi eta X : ℕ) [Fact p.Prime],
      a < b → p ^ (T * b) ≤ X → N₀ ≤ X / p ^ (T * b) + 1 →
      (C * iterationConstant k u) ^ 2 ≤ (p : ℝ) → eta < p ^ b →
      ∀ colourA colourB : Fin k → Bool,
      conditionedMoment p k a b xi eta X u colourA colourB / momentScale X p k u a b lam ≤
        B * (p : ℝ) ^ (delta * a + beta * b) := by
  obtain ⟨C, hC, N₀, hbudget⟩ :=
    VinogradovImprovedNormalization.exists_improved_rounded_budget k u hk hu
  obtain ⟨beta, hbeta, T, hT, B, hB, he⟩ :=
    exists_negative_profile hk hu hC (first_exponent_gt_critical hk) hbudget
  exact ⟨C, hC, N₀, beta, hbeta, T, hT, B, hB, he⟩

/-- The entire initial conditioned level has an independent negative prime-power profile, with every residue and colour included and the actual cutoff depth retained. -/
theorem exists_improved_initial_level_decay (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u) :
    let lam : ℝ := (((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ)))
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N₀ : ℕ, ∃ beta : ℝ, beta < 0 ∧
      ∃ T : ℕ, 1 ≤ T ∧ ∃ B : ℝ, 1 ≤ B ∧
      ∀ (p b xi X : ℕ) [Fact p.Prime],
      0 < b → p ^ (T * b) ≤ X → N₀ ≤ X / p ^ (T * b) + 1 →
      (C * iterationConstant k u) ^ 2 ≤ (p : ℝ) →
      ∀ colour : Fin k → Bool,
      normalizedLevel p k 0 b xi X u colour lam ≤ B * (p : ℝ) ^ (beta * b) := by
  obtain ⟨C, hC, N₀, beta, hbeta, T, hT, B, hB, he⟩ :=
    exists_improved_negative_profile k u hk hu
  refine ⟨C, hC, N₀, beta, hbeta, T, hT, B, hB, ?_⟩
  intro p b xi X inst hb hX hN hp colour
  have hp0 := Nat.Prime.pos (Fact.out : p.Prime)
  apply normalized_level_le_of_all ((Nat.pow_pos hp0).trans_le hX) colour _ _
  intro eta heta colourB
  have hactual := he p 0 b xi eta X hb hX hN hp heta colour colourB
  simpa only [Nat.cast_zero, mul_zero, zero_add] using hactual

end
end RiemannGaussian.VinogradovNegativeProfile
