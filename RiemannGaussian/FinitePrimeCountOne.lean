/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FinitePrimeSquareOverlap

/-!
# The complete one-prime pattern with all overlaps retained

The last selected-prime pattern is isolated by subtracting the exact
zero-prime and at-least-two-prime patterns from the full response.
Its signed transform has a product bound for every nonnegative prime
weight. The same identity transports arbitrary physical phases and
genuinely convergent arithmetic series.
-/

open Complex
open scoped Classical

namespace RiemannGaussian
noncomputable section

private theorem prod_bool (S : Finset ℕ) (b : ℕ → Prop) [DecidablePred b] :
    (∏ p ∈ S, if b p then (1 : ℂ) else 0) = if ∀ p ∈ S, b p then 1 else 0 := by
  by_cases h : ∀ p ∈ S, b p
  · rw [if_pos h]
    exact Finset.prod_eq_one (fun p hp ↦ if_pos (h p hp))
  · rw [if_neg h]
    push Not at h
    obtain ⟨p, hp, hb⟩ := h
    exact Finset.prod_eq_zero hp (if_neg hb)

/-- The full signed first-power inclusion-exclusion is exactly
avoidance of every selected prime, for arbitrary complex physical weights. -/
theorem primeAvoidance_eq_signed_subsets (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (F : ℕ → ℂ) (n : ℕ) :
    (∑ U ∈ S.powerset, (-1 : ℂ) ^ U.card *
      (if (∏ p ∈ U, p) ∣ n then F n else 0)) =
        if ∃ p ∈ S, p ∣ n then 0 else F n := by
  let b : ℕ → ℂ := fun p ↦ if p ∣ n then 1 else 0
  have he (U : Finset ℕ) (hU : U ∈ S.powerset) :
      (if (∏ p ∈ U, p) ∣ n then F n else 0) = (∏ p ∈ U, b p) * F n := by
    rw [show (∏ p ∈ U, b p) = if (∏ p ∈ U, p) ∣ n then 1 else 0 by
      rw [prod_bool]
      simp only [← prod_primes_dvd_iff U (fun p hp ↦ hS p (Finset.mem_powerset.mp hU hp))]]
    split_ifs <;> simp
  have hc (p : ℕ) : 1 - b p = if ¬p ∣ n then (1 : ℂ) else 0 := by
    by_cases hp : p ∣ n <;> simp [b, hp]
  calc
    _ = (∑ U ∈ S.powerset, (-1 : ℂ) ^ U.card * ∏ p ∈ U, b p) * F n := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun U hU ↦ by rw [he U hU]; ring)
    _ = (∏ p ∈ S, (1 - b p)) * F n := by
      rw [Finset.prod_sub]
      simp only [Finset.prod_const_one, mul_one]
    _ = _ := by
      simp_rw [hc]
      rw [prod_bool]
      by_cases h : ∃ p ∈ S, p ∣ n
      · have hn : ¬∀ p ∈ S, ¬p ∣ n := by
          obtain ⟨p, hp, hpn⟩ := h
          exact fun hh ↦ hh p hp hpn
        simp [h]
      · have hn : ∀ p ∈ S, ¬p ∣ n := fun p hp hpn ↦ h ⟨p, hp, hpn⟩
        simp [h]

/-- The exact single-prime transform, with every first-power
intersection and inclusion-exclusion sign still present. -/
def primeCountOneTransform (F : Finset ℕ → ℂ) (S : Finset ℕ) : ℂ :=
  F ∅ - (∑ T ∈ S.powerset.filter (fun T ↦ 2 ≤ T.card), ∑ U ∈ (S \ T).powerset,
    (-1 : ℂ) ^ U.card * F (T ∪ U)) - ∑ U ∈ S.powerset, (-1 : ℂ) ^ U.card * F U

/-- The transform is exactly the physical pattern with one selected
prime divisor; no selected prime or overlap is singled out or lost. -/
theorem primeCountOneTransform_indicator (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (F : ℕ → ℂ) (n : ℕ) :
    primeCountOneTransform (fun W ↦ if (∏ p ∈ W, p) ∣ n then F n else 0) S =
      if (S.filter (fun p ↦ p ∣ n)).card = 1 then F n else 0 := by
  unfold primeCountOneTransform
  rw [← primePairSieve_eq_signed_patterns S hS F n, primeAvoidance_eq_signed_subsets S hS F n]
  simp only [Finset.prod_empty, one_dvd, if_true]
  have hz : (S.filter (fun p ↦ p ∣ n)).card = 0 ↔ ¬∃ p ∈ S, p ∣ n := by
    simp [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  by_cases h : (S.filter (fun p ↦ p ∣ n)).card = 0
  · simp [h, hz.mp h]
  · have he : ∃ p ∈ S, p ∣ n := by simpa using not_congr hz |>.mp h
    by_cases h1 : (S.filter (fun p ↦ p ∣ n)).card = 1
    · simp [h1, he]
    · simp [h1, he, show 2 ≤ (S.filter (fun p ↦ p ∣ n)).card by omega]

/-- The exact transform keeps arbitrary complex kernel factors
outside the finite intersection sum without taking a norm. -/
theorem primeCountOneTransform_mul_right (F : Finset ℕ → ℂ) (S : Finset ℕ) (a : ℂ) :
    primeCountOneTransform (fun W ↦ F W * a) S = primeCountOneTransform F S * a := by
  unfold primeCountOneTransform
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  ring

/-- Every series in the one-prime transform is genuinely convergent;
the exact finite pattern commutes with the entire arithmetic sum. -/
theorem hasSum_primeCountOneTransform (f : Finset ℕ → ℕ → ℂ)
    (F : Finset ℕ → ℂ) (S : Finset ℕ)
    (h : ∀ W : Finset ℕ, W ⊆ S → HasSum (f W) (F W)) :
    HasSum (fun n ↦ primeCountOneTransform (fun W ↦ f W n) S) (primeCountOneTransform F S) := by
  apply ((h ∅ (Finset.empty_subset _)).sub ?_).sub
  · apply hasSum_sum
    intro U hU
    exact (h U (Finset.mem_powerset.mp hU)).mul_left _
  · apply hasSum_sum
    intro T hT
    apply hasSum_sum
    intro U hU
    apply (h (T ∪ U) ?_).mul_left
    exact Finset.union_subset (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1)
      (fun p hp ↦ (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hU hp)).1)

/-- The full one-prime transform has a uniform product budget for
every nonnegative prime weight, with all signed patterns retained upstream. -/
theorem norm_primeCountOneTransform_le (F : Finset ℕ → ℂ) (S : Finset ℕ)
    (w : ℕ → ℝ) (hw : ∀ p, 0 ≤ w p) {A : ℝ} (hA : 0 ≤ A)
    (hF : ∀ W : Finset ℕ, W ⊆ S → ‖F W‖ ≤ A * ∏ p ∈ W, w p) :
    ‖primeCountOneTransform F S‖ ≤ 3 * A * ∏ p ∈ S, (1 + 2 * w p) := by
  let B := ∏ p ∈ S, (1 + 2 * w p)
  have hB : 1 ≤ B := by
    change 1 ≤ ∏ p ∈ S, (1 + 2 * w p)
    exact Finset.one_le_prod (fun p _ ↦ by linarith [hw p])
  have hbase : ‖F ∅‖ ≤ A * B := by
    have h0 : ‖F ∅‖ ≤ A := by simpa using hF ∅ (Finset.empty_subset S)
    exact h0.trans
      (by simpa using mul_le_mul_of_nonneg_left hB hA)
  have hpair : ‖∑ T ∈ S.powerset.filter (fun T ↦ 2 ≤ T.card), ∑ U ∈ (S \ T).powerset,
      (-1 : ℂ) ^ U.card * F (T ∪ U)‖ ≤ A * B := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ T ∈ S.powerset.filter (fun T ↦ 2 ≤ T.card), ∑ U ∈ (S \ T).powerset,
          A * ∏ p ∈ T ∪ U, w p := by
        apply Finset.sum_le_sum
        intro T hT
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro U hU
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        exact hF (T ∪ U) (Finset.union_subset
          (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1)
          (fun p hp ↦ (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hU hp)).1))
      _ = A * ∑ T ∈ S.powerset.filter (fun T ↦ 2 ≤ T.card), ∑ U ∈ (S \ T).powerset,
          ∏ p ∈ T ∪ U, w p := by simp_rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_prime_patterns_product_le S w hw) hA
  have hnone : ‖∑ U ∈ S.powerset, (-1 : ℂ) ^ U.card * F U‖ ≤ A * B := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ U ∈ S.powerset, A * ∏ p ∈ U, w p := by
        apply Finset.sum_le_sum
        intro U hU
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        exact hF U (Finset.mem_powerset.mp hU)
      _ = A * ∏ p ∈ S, (1 + w p) := by rw [Finset.prod_one_add, Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.prod_le_prod
        (fun p _ ↦ by linarith [hw p]) (fun p _ ↦ by linarith [hw p])) hA
  unfold primeCountOneTransform
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) le_rfl).trans
  exact (add_le_add (add_le_add hbase hpair) hnone).trans_eq (by dsimp [B]; ring)

end
end RiemannGaussian
