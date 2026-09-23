/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovLinearSaving

/-!
# Explicit conditioning depth at the critical high moment

For `u = k` and exponent defect at least one half, exactly
`2*k*(k+1)+4` profile steps suffice. Every intermediate profile is above
minus one, so a common descendant extension `d = 2*k` pays all cutoffs.
The resulting actual depth is `(3*k)^(2*k*(k+1)+4)`, with multiplier at
most `(2*k*k)^(7*k)` and no source-constant dependence in the prime budget.
The original conditioned moments, initial allowance and global prime packet
retain these evaluated costs. This is not yet a quantitative all-endpoint
global moment or a new zero-free region.
-/

namespace RiemannGaussian.VinogradovQuantitativeProfile
noncomputable section
open scoped BigOperators
open VinogradovMeanValue VinogradovConditioningRemainder VinogradovRemainderScaling
open VinogradovConditioningPowerSaving VinogradovSingularConditioning
open VinogradovNormalizedIteration VinogradovCongruencingScaling
open VinogradovNonsingularConditioning VinogradovProfileIteration
open VinogradovFirstExponent VinogradovExponentBootstrap
open VinogradovDefectRemainder VinogradovConstantPreservation VinogradovLinearProfile

/-- The fixed number of conditioning steps for defect one half. -/
def halfDefectSteps (k : ℕ) : ℕ := 2 * k * (k + 1) + 4

/-- The complete original quotient-depth budget at defect one half. -/
def halfDefectDepth (k : ℕ) : ℕ := (3 * k) ^ halfDefectSteps k

/-- At ratio one the affine conditioning recurrence is exactly linear. -/
theorem affineProfile_one (c B : ℝ) (n : ℕ) :
    affineProfile 1 c B n = B - n * c := by
  induction n with
  | zero => simp [affineProfile]
  | succ n ih => simp only [affineProfile, ih, one_mul, Nat.cast_add, Nat.cast_one]; ring

/-- The chosen stopping count has an evaluated negative profile. -/
theorem half_defect_profile_at_count (k : ℕ) (hk : 0 < k) :
    affineProfile ((k : ℝ) / k) ((1 - 1 / (k : ℝ)) * (1 / 2))
      ((k : ℝ) * k) (halfDefectSteps k) = -1 + 2 / (k : ℝ) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  rw [div_self hk0, affineProfile_one]
  unfold halfDefectSteps
  push_cast
  field_simp
  ring

/-- No intermediate profile needs a deeper extension than `2*k`. -/
theorem half_defect_prefix_lower (k j : ℕ) (hk : 2 ≤ k)
    (hj : j ≤ halfDefectSteps k) :
    -1 ≤ affineProfile ((k : ℝ) / k) ((1 - 1 / (k : ℝ)) * (1 / 2))
      ((k : ℝ) * k) j := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hc : 0 ≤ (1 - 1 / (k : ℝ)) * (1 / 2) := by
    have h := (div_le_one hk0).mpr (show (1 : ℝ) ≤ k by exact_mod_cast (by omega : 1 ≤ k))
    positivity
  have hcount := half_defect_profile_at_count k (by omega)
  rw [div_self (ne_of_gt hk0), affineProfile_one] at hcount ⊢
  have hm := mul_le_mul_of_nonneg_right (show (j : ℝ) ≤ halfDefectSteps k by exact_mod_cast hj) hc
  have hp : 0 ≤ 2 / (k : ℝ) := by positivity
  linarith only [hcount, hm, hp]

/-- The explicit depth always includes the initial two quotient levels. -/
theorem halfDefectDepth_ge_two (k : ℕ) (hk : 2 ≤ k) : 2 ≤ halfDefectDepth k := by
  apply (show 2 ≤ 3 * k by omega).trans
  exact Nat.le_pow (by unfold halfDefectSteps; omega)

/-- The actual conditioned moments gain a half power with fully explicit
depth and multiplier bounds at every degree `k >= 4`. All quotient moment
premises remain explicit; the global descent supplies them separately. -/
theorem half_defect_conditioned_bound (k : ℕ) (hk : 4 ≤ k) :
    ∃ B : ℝ, 1 ≤ B ∧ B ≤ (2 * (k : ℝ) * k) ^ (7 * k) ∧
      ∀ C : ℝ, 1 ≤ C → ∀ (lam : ℝ) (N₀ : ℕ),
      (1 / 2 : ℝ) ≤ lam - 2 * (k : ℝ) * ((k : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2 →
      (∀ p e X : ℕ, 0 < p → p ^ e ≤ X → N₀ ≤ X / p ^ e + 1 →
        meanValue ((k + 1) * k) k (X / p ^ e + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ e) ^ lam) →
      let delta := lam - 2 * (k : ℝ) * ((k : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2
      ∀ (p a b xi eta X : ℕ) [Fact p.Prime],
      a < b → p ^ (halfDefectDepth k * b) ≤ X → N₀ ≤ X / p ^ (halfDefectDepth k * b) + 1 →
      iterationConstant k k ^ 2 ≤ (p : ℝ) → eta < p ^ b →
      ∀ colourA colourB : Fin k → Bool,
      conditionedMoment p k a b xi eta X k colourA colourB / momentScale X p k k a b lam ≤
        (C * B) * (p : ℝ) ^ (delta * a - (b : ℝ) / 2) := by
  have hk2 : 2 ≤ k := by omega
  have hdepth (j : ℕ) (hj : j < halfDefectSteps k) :
      -((2 * k : ℕ) : ℝ) / 2 ≤ (1 / 2 : ℝ) + (k : ℝ) *
      affineProfile ((k : ℝ) / k) ((1 - 1 / (k : ℝ)) * (1 / 2)) ((k : ℝ) * k) j := by
    have h := mul_le_mul_of_nonneg_left (half_defect_prefix_lower k j hk2 hj.le) (Nat.cast_nonneg k)
    push_cast
    linarith only [h]
  obtain ⟨B, hB, hcap, h⟩ := bounded_depth_profile_iteration k k hk2 le_rfl
    (1 / 2) (by norm_num) (halfDefectSteps k) (2 * k) (by omega) hdepth
  refine ⟨B, hB, hcap.trans (profile_ceiling_le k k hk2 le_rfl), ?_⟩
  intro C hC lam N₀ hdef hbudget delta p a b xi eta X inst hab hX hN hp heta colourA colourB
  have hpow : (k + 2 * k) ^ halfDefectSteps k = halfDefectDepth k := by
    unfold halfDefectDepth
    congr 1
    omega
  have he := h C hC lam N₀ hdef hbudget p a b xi eta X hab
    (by simpa only [hpow] using hX) (by simpa only [hpow] using hN) hp heta colourA colourB
  rw [half_defect_profile_at_count k (by omega)] at he
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hslope : -1 + 2 / (k : ℝ) ≤ -(1 / 2 : ℝ) := by
    have htwo : 2 / (k : ℝ) ≤ 1 / 2 := (div_le_iff₀ hk0).mpr (by
      have h := (show (4 : ℝ) ≤ k by exact_mod_cast hk)
      linarith only [h])
    linarith
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (zero_le_one.trans hC) (zero_le_one.trans hB))
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Nat.Prime.one_lt (Fact.out : p.Prime)).le)
  have hscaled := mul_le_mul_of_nonneg_right hslope (Nat.cast_nonneg b)
  dsimp only [delta]
  linarith only [hscaled]

/-- The complete initial allowance has a fixed half-power saving with an
evaluated coefficient and descendant cutoff. No homogeneous constant is
absorbed into the prime-size requirement. -/
theorem half_defect_initial_allowance (k : ℕ) (hk : 4 ≤ k)
    (C : ℝ) (hC : 1 ≤ C) (lam : ℝ) (N₀ : ℕ)
    (hdef : (1 / 2 : ℝ) ≤ lam - 2 * (k : ℝ) * ((k : ℝ) + 1) +
      (k : ℝ) * ((k : ℝ) + 1) / 2)
    (hbudget : ∀ p e X : ℕ, 0 < p → p ^ e ≤ X → N₀ ≤ X / p ^ e + 1 →
      meanValue ((k + 1) * k) k (X / p ^ e + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ e) ^ lam)
    (p xi X : ℕ) [Fact p.Prime]
    (hX : p ^ halfDefectDepth k ≤ X) (hN : N₀ ≤ X / p ^ halfDefectDepth k + 1)
    (hp : iterationConstant k k ^ 2 ≤ (p : ℝ)) (colour : Fin k → Bool) :
    constantAllowance C p k 0 1 xi X k 1 colour lam ≤
      C * (1 + selectionCost k k * (2 * (k : ℝ) * k) ^ (7 * k)) *
        (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨B, hB, hcap, h⟩ := half_defect_conditioned_bound k hk
  have hp0 := Nat.Prime.pos (Fact.out : p.Prime)
  have hn : normalizedLevel p k 0 1 xi X k colour lam ≤ (C * B) * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
    apply normalized_level_le_of_all ((Nat.pow_pos hp0).trans_le hX) colour lam
    intro eta heta colourB
    have he := h C hC lam N₀ hdef hbudget p 0 1 xi eta X (by omega)
      (by simpa only [mul_one] using hX) (by simpa only [mul_one] using hN) hp heta colour colourB
    simpa only [Nat.cast_zero, Nat.cast_one, mul_zero, zero_sub] using he
  have hcap' : (C * B) * (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      (C * (2 * (k : ℝ) * k) ^ (7 * k)) * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcap (zero_le_one.trans hC)) (by positivity)
  unfold constantAllowance
  simp only [Finset.sum_range_one, pow_zero, Nat.cast_zero, mul_zero,
    Real.rpow_zero, one_mul, add_zero, Nat.cast_one]
  have hE : 0 ≤ selectionCost k k := by unfold selectionCost; positivity
  calc
    _ ≤ C * (p : ℝ) ^ (-(1 / 2 : ℝ)) + selectionCost k k *
        ((C * (2 * (k : ℝ) * k) ^ (7 * k)) * (p : ℝ) ^ (-(1 / 2 : ℝ))) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (hn.trans hcap') hE)
    _ = _ := by ring

/-- The actual global mean value inherits the explicit half-defect depth
and coefficient through the original prime packet. The displayed quotient
budgets must still be supplied by a global exponent descent. -/
theorem half_defect_global_bound (k : ℕ) (hk : 4 ≤ k)
    (C : ℝ) (hC : 1 ≤ C) (lam : ℝ) (N₀ : ℕ)
    (hdef : (1 / 2 : ℝ) ≤ lam - 2 * (k : ℝ) * ((k : ℝ) + 1) +
      (k : ℝ) * ((k : ℝ) + 1) / 2)
    (hbudget : ∀ p e X : ℕ, 0 < p → p ^ e ≤ X → N₀ ≤ X / p ^ e + 1 →
      meanValue ((k + 1) * k) k (X / p ^ e + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ e) ^ lam)
    (M R X : ℕ) (hM : 0 < M) (hR : 0 < R)
    (hpacket : X ^ (k * (k - 1)) < M ^ R) (hsize : 4 * k ^ 4 ≤ X)
    (hcutoff : (2 ^ R * M) ^ halfDefectDepth k ≤ X)
    (hN : N₀ ≤ X / (2 ^ R * M) ^ halfDefectDepth k + 1)
    (hprime : iterationConstant k k ^ 2 ≤ (M : ℝ)) :
    meanValue ((k + 1) * k) k X ≤
      (2 * (R : ℝ)) ^ 2 * (C * (1 + selectionCost k k * (2 * (k : ℝ) * k) ^ (7 * k))) *
        (X : ℝ) ^ lam * (M : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hB : 1 ≤ 1 + selectionCost k k * (2 * (k : ℝ) * k) ^ (7 * k) := by
    apply le_add_of_nonneg_right
    unfold selectionCost
    positivity
  apply VinogradovLinearSaving.global_meanValue_of_initial_allowance k k (by omega) le_rfl
    C hC lam N₀ (by linarith) hbudget (-(1 / 2)) (by norm_num)
    (halfDefectDepth k) (halfDefectDepth_ge_two k (by omega)) _ hB
    ?_ M R X hM hR hpacket hsize hcutoff hN hprime
  intro p xi Y inst hY hNY hp colour
  exact half_defect_initial_allowance k hk C hC lam N₀ hdef hbudget p xi Y hY hNY hp colour

end
end RiemannGaussian.VinogradovQuantitativeProfile
