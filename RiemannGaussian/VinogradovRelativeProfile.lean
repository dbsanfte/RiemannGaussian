/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovQuantitativeProfile

/-!
# Polynomial conditioning depth for a relative exponent allowance

An exponent allowance `k^2/q` needs only `2*q` conditioning steps, independent
of the degree. The actual descendant depth `(k+2*k^3)^(2*q)` is polynomial
in degree for fixed `q`. Both colours, all residues and the original quotient
moment hypotheses survive. A later Gaussian budget pays the two exponent
allowances before taking norms. No uniform zeta or zero-free claim is made.
-/

namespace RiemannGaussian.VinogradovRelativeProfile
noncomputable section
open scoped BigOperators
open VinogradovMeanValue VinogradovConditioningRemainder VinogradovRemainderScaling
open VinogradovConditioningPowerSaving VinogradovSingularConditioning
open VinogradovNormalizedIteration VinogradovCongruencingScaling
open VinogradovNonsingularConditioning VinogradovProfileIteration
open VinogradovFirstExponent VinogradovExponentBootstrap
open VinogradovDefectRemainder VinogradovConstantPreservation VinogradovLinearProfile
open VinogradovQuantitativeProfile

/-- The moment exponent allowance as a fixed fraction of the degree square. -/
def relativeDefect (k q : ℕ) : ℝ := (k : ℝ) ^ 2 / q

/-- The complete descendant depth after the fixed number `2*q` of steps. -/
def relativeDepth (k q : ℕ) : ℕ := (k + 2 * k ^ 3) ^ (2 * q)

/-- A fixed number of steps gives a negative profile at every degree. -/
theorem relative_profile_at_count (k q : ℕ) (hk : 0 < k) (hq : 0 < q) :
    affineProfile ((k : ℝ) / k) ((1 - 1 / (k : ℝ)) * relativeDefect k q)
      ((k : ℝ) * k) (2 * q) = -(k : ℝ) ^ 2 + 2 * k := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  rw [div_self hk0, affineProfile_one]
  unfold relativeDefect
  push_cast
  field_simp
  ring

/-- Every earlier profile remains above minus the degree square. -/
theorem relative_profile_prefix_lower (k q j : ℕ) (hk : 2 ≤ k) (hq : 0 < q)
    (hj : j ≤ 2 * q) :
    -(k : ℝ) ^ 2 ≤ affineProfile ((k : ℝ) / k) ((1 - 1 / (k : ℝ)) * relativeDefect k q)
      ((k : ℝ) * k) j := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hc : 0 ≤ (1 - 1 / (k : ℝ)) * relativeDefect k q := by
    have h := (div_le_one hk0).mpr (show (1 : ℝ) ≤ k by exact_mod_cast (by omega : 1 ≤ k))
    unfold relativeDefect
    positivity
  have hcount := relative_profile_at_count k q (by omega) hq
  rw [div_self (ne_of_gt hk0), affineProfile_one] at hcount ⊢
  have hm := mul_le_mul_of_nonneg_right (show (j : ℝ) ≤ (2 * q : ℕ) by exact_mod_cast hj) hc
  linarith only [hcount, hm, Nat.cast_nonneg (α := ℝ) k]

/-- The polynomial depth includes both initial quotient levels. -/
theorem relativeDepth_ge_two (k q : ℕ) (hk : 2 ≤ k) (hq : 0 < q) :
    2 ≤ relativeDepth k q := by
  apply (show 2 ≤ k + 2 * k ^ 3 by omega).trans
  exact Nat.le_pow (by omega)

/-- The actual conditioned moments gain a half power with polynomial
descendant depth for every fixed relative accuracy denominator. All quotient moment
premises remain explicit; the global descent supplies them separately. -/
theorem relative_defect_conditioned_bound (k q : ℕ) (hk : 4 ≤ k) (hq : 0 < q) :
    ∃ B : ℝ, 1 ≤ B ∧ B ≤ (2 * (k : ℝ) * k) ^ (7 * k) ∧
      ∀ C : ℝ, 1 ≤ C → ∀ (lam : ℝ) (N₀ : ℕ),
      relativeDefect k q ≤ lam - 2 * (k : ℝ) * ((k : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2 →
      (∀ p e X : ℕ, 0 < p → p ^ e ≤ X → N₀ ≤ X / p ^ e + 1 →
        meanValue ((k + 1) * k) k (X / p ^ e + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ e) ^ lam) →
      let delta := lam - 2 * (k : ℝ) * ((k : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2
      ∀ (p a b xi eta X : ℕ) [Fact p.Prime],
      a < b → p ^ (relativeDepth k q * b) ≤ X → N₀ ≤ X / p ^ (relativeDepth k q * b) + 1 →
      iterationConstant k k ^ 2 ≤ (p : ℝ) → eta < p ^ b →
      ∀ colourA colourB : Fin k → Bool,
      conditionedMoment p k a b xi eta X k colourA colourB / momentScale X p k k a b lam ≤
        (C * B) * (p : ℝ) ^ (delta * a - (b : ℝ) / 2) := by
  have hk2 : 2 ≤ k := by omega
  have hdepth (j : ℕ) (hj : j < 2 * q) :
      -((2 * k ^ 3 : ℕ) : ℝ) / 2 ≤ relativeDefect k q + (k : ℝ) *
      affineProfile ((k : ℝ) / k) ((1 - 1 / (k : ℝ)) * relativeDefect k q)
        ((k : ℝ) * k) j := by
    have h := mul_le_mul_of_nonneg_left (relative_profile_prefix_lower k q j hk2 hq hj.le)
      (Nat.cast_nonneg k)
    have hd : 0 ≤ relativeDefect k q := by unfold relativeDefect; positivity
    push_cast
    nlinarith only [h, hd]
  have hdk : k ≤ 2 * k ^ 3 := by
    have hp : k ≤ k ^ 3 := Nat.le_pow (by norm_num)
    omega
  obtain ⟨B, hB, hcap, h⟩ := bounded_depth_profile_iteration k k hk2 le_rfl
    (relativeDefect k q) (by unfold relativeDefect; positivity) (2 * q) (2 * k ^ 3) hdk hdepth
  refine ⟨B, hB, hcap.trans (profile_ceiling_le k k hk2 le_rfl), ?_⟩
  intro C hC lam N₀ hdef hbudget delta p a b xi eta X inst hab hX hN hp heta colourA colourB
  have he := h C hC lam N₀ hdef hbudget p a b xi eta X hab hX hN hp heta colourA colourB
  rw [relative_profile_at_count k q (by omega) hq] at he
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hslope : -(k : ℝ)^2 + 2 * k ≤ -(1 / 2 : ℝ) := by
    nlinarith only [hkR, sq_nonneg ((k : ℝ) - 2)]
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (zero_le_one.trans hC) (zero_le_one.trans hB))
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Nat.Prime.one_lt (Fact.out : p.Prime)).le)
  have hscaled := mul_le_mul_of_nonneg_right hslope (Nat.cast_nonneg b)
  dsimp only [delta]
  linarith only [hscaled]

/-- The complete initial allowance has a fixed half-power saving with an
evaluated coefficient and polynomial descendant cutoff. No homogeneous constant is
absorbed into the prime-size requirement. -/
theorem relative_defect_initial_allowance (k q : ℕ) (hk : 4 ≤ k) (hq : 0 < q)
    (C : ℝ) (hC : 1 ≤ C) (lam : ℝ) (N₀ : ℕ)
    (hdef : relativeDefect k q ≤ lam - 2 * (k : ℝ) * ((k : ℝ) + 1) +
      (k : ℝ) * ((k : ℝ) + 1) / 2)
    (hbudget : ∀ p e X : ℕ, 0 < p → p ^ e ≤ X → N₀ ≤ X / p ^ e + 1 →
      meanValue ((k + 1) * k) k (X / p ^ e + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ e) ^ lam)
    (p xi X : ℕ) [Fact p.Prime]
    (hX : p ^ relativeDepth k q ≤ X) (hN : N₀ ≤ X / p ^ relativeDepth k q + 1)
    (hp : iterationConstant k k ^ 2 ≤ (p : ℝ)) (colour : Fin k → Bool) :
    constantAllowance C p k 0 1 xi X k 1 colour lam ≤
      C * (1 + selectionCost k k * (2 * (k : ℝ) * k) ^ (7 * k)) *
        (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨B, hB, hcap, h⟩ := relative_defect_conditioned_bound k q hk hq
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

/-- The actual global mean value inherits the explicit relative-defect depth
and coefficient through the original prime packet. The displayed quotient
budgets must still be supplied by a global exponent descent. -/
theorem relative_defect_global_bound (k q : ℕ) (hk : 4 ≤ k) (hq : 0 < q)
    (C : ℝ) (hC : 1 ≤ C) (lam : ℝ) (N₀ : ℕ)
    (hdef : relativeDefect k q ≤ lam - 2 * (k : ℝ) * ((k : ℝ) + 1) +
      (k : ℝ) * ((k : ℝ) + 1) / 2)
    (hbudget : ∀ p e X : ℕ, 0 < p → p ^ e ≤ X → N₀ ≤ X / p ^ e + 1 →
      meanValue ((k + 1) * k) k (X / p ^ e + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ e) ^ lam)
    (M R X : ℕ) (hM : 0 < M) (hR : 0 < R)
    (hpacket : X ^ (k * (k - 1)) < M ^ R) (hsize : 4 * k ^ 4 ≤ X)
    (hcutoff : (2 ^ R * M) ^ relativeDepth k q ≤ X)
    (hN : N₀ ≤ X / (2 ^ R * M) ^ relativeDepth k q + 1)
    (hprime : iterationConstant k k ^ 2 ≤ (M : ℝ)) :
    meanValue ((k + 1) * k) k X ≤
      (2 * (R : ℝ)) ^ 2 * (C * (1 + selectionCost k k * (2 * (k : ℝ) * k) ^ (7 * k))) *
        (X : ℝ) ^ lam * (M : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hd : 0 < relativeDefect k q := by unfold relativeDefect; positivity
  have hB : 1 ≤ 1 + selectionCost k k * (2 * (k : ℝ) * k) ^ (7 * k) := by
    apply le_add_of_nonneg_right
    unfold selectionCost
    positivity
  apply VinogradovLinearSaving.global_meanValue_of_initial_allowance k k (by omega) le_rfl
    C hC lam N₀ (by linarith) hbudget (-(1 / 2)) (by norm_num)
    (relativeDepth k q) (relativeDepth_ge_two k q (by omega) hq) _ hB
    ?_ M R X hM hR hpacket hsize hcutoff hN hprime
  intro p xi Y inst hY hNY hp colour
  exact relative_defect_initial_allowance k q hk hq C hC lam N₀ hdef hbudget p xi Y hY hNY hp colour

end
end RiemannGaussian.VinogradovRelativeProfile
