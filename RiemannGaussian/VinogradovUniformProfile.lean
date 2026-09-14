/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovProfileIteration

/-!
# One finite profile depth uniform over source exponents

Fix a nonnegative lower exponent defect and a finite iteration count. The
same depth pays every descendant cutoff for all source exponents above
that defect, all homogeneous moment constants and all quotient thresholds.
The original residues, both colours and full intermediate sums survive.
Only the profile constant depends on the homogeneous constant. This uniform
quantifier order is needed by the critical-exponent infimum argument.
-/

namespace RiemannGaussian.VinogradovUniformProfile
noncomputable section
open scoped Classical BigOperators
open VinogradovMeanValue VinogradovConditioningRemainder VinogradovConditioningPowerSaving
open VinogradovNormalizedIteration VinogradovCongruencingScaling VinogradovNonsingularConditioning
open VinogradovProfileIteration

/-- A fixed lower exponent defect gives one finite depth uniformly over all source exponents, homogeneous constants and quotient thresholds. -/
theorem uniform_defect_profile_iteration (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u)
    (defect : ℝ) (hdefect0 : 0 ≤ defect) (n : ℕ) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ C : ℝ, 1 ≤ C → ∃ B : ℝ, 1 ≤ B ∧
      ∀ (lam : ℝ) (N₀ : ℕ),
      defect ≤ lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2 →
      (∀ p e X : ℕ, 0 < p → p ^ e ≤ X → N₀ ≤ X / p ^ e + 1 →
        meanValue ((u + 1) * k) k (X / p ^ e + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ e) ^ lam) →
      let delta := lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2
      ∀ (p a b xi eta X : ℕ) [Fact p.Prime],
      a < b → p ^ (T * b) ≤ X → N₀ ≤ X / p ^ (T * b) + 1 →
      (C * iterationConstant k u) ^ 2 ≤ (p : ℝ) → eta < p ^ b →
      ∀ colourA colourB : Fin k → Bool,
      conditionedMoment p k a b xi eta X u colourA colourB / momentScale X p k u a b lam ≤
        B * (p : ℝ) ^ (delta * a +
          affineProfile ((k : ℝ) / u) ((1 - 1 / (u : ℝ)) * defect) ((k : ℝ) * u) n * b) := by
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  have hr0 : (0 : ℝ) ≤ (k : ℝ) / u := by positivity
  have hr1 : (k : ℝ) / u ≤ 1 := (div_le_one hu0).mpr (by exact_mod_cast hu)
  have hf : 0 ≤ 1 - 1 / (u : ℝ) := by
    have ht : 1 / (u : ℝ) ≤ 1 := (div_le_one hu0).mpr (by exact_mod_cast (by omega : 1 ≤ u))
    linarith
  have hc : 0 ≤ (1 - 1 / (u : ℝ)) * defect := mul_nonneg hf hdefect0
  induction n with
  | zero =>
    refine ⟨1, by omega, ?_⟩
    intro C hC
    refine ⟨C, hC, ?_⟩
    intro lam N₀ hdefect hbudget
    dsimp only
    intro p a b xi eta X inst hab hX hN hp heta colourA colourB
    have hp0 := Nat.Prime.pos (Fact.out : p.Prime)
    have hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 ≤ lam := by linarith
    simp only [one_mul] at hX hN
    obtain ⟨hXa, hNa⟩ := quotient_budget_mono hp0 hab.le hX hN
    have he := initial_profile (xi := xi) (eta := eta) hk hu hab.le
      ((Nat.pow_pos hp0).trans_le hX) hC hlam
      (hbudget p a X hp0 hXa hNa) (hbudget p b X hp0 hX hN) colourA colourB
    simpa only [affineProfile] using he
  | succ n ih =>
    obtain ⟨T, hT, hprev⟩ := ih
    let beta := affineProfile ((k : ℝ) / u) ((1 - 1 / (u : ℝ)) * defect) ((k : ℝ) * u) n
    have hbeta : beta ≤ (k : ℝ) * u := affineProfile_le hr0 hr1 hc (by positivity) n
    obtain ⟨d, hdsize⟩ := exists_nat_ge (max (k : ℝ) (-2 * (defect + (k : ℝ) * beta)))
    have hdk : k ≤ d := by exact_mod_cast (le_max_left _ _).trans hdsize
    have hddepth : -(d : ℝ) / 2 ≤ defect + (k : ℝ) * beta := by
      have he := (le_max_right (k : ℝ) (-2 * (defect + (k : ℝ) * beta))).trans hdsize
      linarith only [he]
    refine ⟨T * (k + d), by nlinarith, ?_⟩
    intro C hC
    obtain ⟨B, hB, hprev⟩ := hprev C hC
    let Bnext : ℝ := max 1 ((k.factorial : ℝ) * C ^ (1 - 1 / (u : ℝ)) *
      (1 + 2 * selectionCost k u * B) ^ (1 / (u : ℝ)))
    refine ⟨Bnext, le_max_left _ _, ?_⟩
    intro lam N₀ hdefect hbudget
    let delta := lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2
    have hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 ≤ lam := by linarith
    dsimp only
    intro p a b xi eta X inst hab hX hN hp heta colourA colourB
    have hp0 := Nat.Prime.pos (Fact.out : p.Prime)
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.Prime.one_lt (Fact.out : p.Prime)).le
    have hXpos : 0 < X := (Nat.pow_pos hp0).trans_le hX
    have hdeepExp : k * b + d * b ≤ (T * (k + d)) * b := by
      have he := Nat.mul_le_mul_right ((k + d) * b) hT
      nlinarith
    obtain ⟨hXd, hNd⟩ := quotient_budget_mono hp0 hdeepExp hX hN
    obtain ⟨hXb, hNb⟩ := quotient_budget_mono hp0 (by nlinarith : b ≤ k * b + d * b) hXd hNd
    have hH : 1 ≤ d * b := by
      have hd1 : 1 ≤ d := by omega
      have hb1 : 1 ≤ b := by omega
      nlinarith
    have hgap : k * b - b ≤ 2 * (d * b) := by
      have he := Nat.mul_le_mul_right b hdk
      omega
    have hdeep : -(((d * b : ℕ) : ℝ) / 2) ≤ (delta + (k : ℝ) * beta) * b := by
      have hdd : -(d : ℝ) / 2 ≤ delta + (k : ℝ) * beta := by dsimp only [delta]; linarith
      have he := mul_le_mul_of_nonneg_right hdd (Nat.cast_nonneg b)
      push_cast
      nlinarith
    have hnext : ∀ h < d * b, normalizedLevel p k b (k * b + h) eta X u colourB lam ≤
        B * (p : ℝ) ^ (delta * b + beta * ((k * b + h : ℕ) : ℝ)) := by
      intro h hh
      apply normalized_level_le_of_all hXpos colourB lam
      intro eta' heta' colourC
      have he : T * (k * b + h) ≤ (T * (k + d)) * b := by
        have hs : k * b + h ≤ (k + d) * b := by nlinarith
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left T hs
      obtain ⟨hXnext, hNnext⟩ := quotient_budget_mono hp0 he hX hN
      have hbb : b < k * b + h := by nlinarith [Nat.mul_le_mul_right b hk]
      exact hprev lam N₀ hdefect hbudget p b (k * b + h) eta eta' X
        hbb hXnext hNnext hp heta' colourB colourC
    have he := conditioned_profile_step (xi := xi) hk hu hab hH hgap hXpos hC (by linarith : 0 ≤ B)
      hlam hp (hbudget p b X hp0 hXb hNb) (hbudget p (k * b + d * b) X hp0 hXd hNd)
      heta colourA colourB hbeta hdeep hnext
    have hcoef : (VinogradovSignedCongruence.colourFactorial colourA : ℝ) * C ^ (1 - 1 / (u : ℝ)) *
        (1 + 2 * selectionCost k u * B) ^ (1 / (u : ℝ)) ≤ Bnext := by
      apply le_trans _ (le_max_right _ _)
      apply mul_le_mul_of_nonneg_right _ (by unfold selectionCost; positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast VinogradovCoarseCongruence.colourFactorial_le_factorial colourA
    have he' := he.trans (mul_le_mul_of_nonneg_right hcoef (by positivity))
    have hbeta_next : affineProfile ((k : ℝ) / u) ((1 - 1 / (u : ℝ)) * defect) ((k : ℝ) * u) (n + 1) =
        -(1 - 1 / (u : ℝ)) * defect + (k : ℝ) / u * beta := by
      change (k : ℝ) / u * beta - (1 - 1 / (u : ℝ)) * defect = _
      ring
    have hslope : -(1 - 1 / (u : ℝ)) * delta + (k : ℝ) / u * beta ≤
        -(1 - 1 / (u : ℝ)) * defect + (k : ℝ) / u * beta := by
      have hd := mul_le_mul_of_nonneg_left hdefect hf
      change (1 - 1 / (u : ℝ)) * defect ≤ (1 - 1 / (u : ℝ)) * delta at hd
      linarith only [hd]
    have hexp := add_le_add (le_refl (delta * a)) (mul_le_mul_of_nonneg_right hslope (Nat.cast_nonneg b))
    change _ ≤ Bnext * (p : ℝ) ^ (delta * a +
      affineProfile ((k : ℝ) / u) ((1 - 1 / (u : ℝ)) * defect) ((k : ℝ) * u) (n + 1) * b)
    rw [hbeta_next]
    exact he'.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp1 hexp)
      (le_trans zero_le_one (le_max_left _ _)))

end
end RiemannGaussian.VinogradovUniformProfile
