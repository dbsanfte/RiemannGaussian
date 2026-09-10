/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FinitePrimeSquareOverlap

/-!
# Exact square deletion inside the surviving prime pattern

The masks describe literal physical integers. Every square intersection
is expanded with its original sign, and the at-most-one-small-prime
condition is kept simultaneously. The resulting exact identities apply
to arbitrary complex physical weights.
-/

open Complex
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The physical mask on multiples of a first-power prime factor
that also contain at least one selected prime square. -/
def primeSquareMultipleMask (W Q : Finset ℕ) (n : ℕ) : ℂ :=
  if (∏ p ∈ W, p) ∣ n ∧ (∃ p ∈ Q, p ^ 2 ∣ n) then 1 else 0

/-- The physical mask for repeated-prime terms surviving the entire
first-power prime-pattern sieve. -/
def primeSquareSurvivorMask (S Q : Finset ℕ) (n : ℕ) : ℂ :=
  if (S.filter (fun p ↦ p ∣ n)).card ≤ 1 ∧ (∃ p ∈ Q, p ^ 2 ∣ n) then 1 else 0

private theorem prod_bool (S : Finset ℕ) (b : ℕ → Prop) [DecidablePred b] :
    (∏ p ∈ S, if b p then (1 : ℂ) else 0) = if ∀ p ∈ S, b p then 1 else 0 := by
  by_cases h : ∀ p ∈ S, b p
  · rw [if_pos h]
    exact Finset.prod_eq_one (fun p hp ↦ if_pos (h p hp))
  · rw [if_neg h]
    push Not at h
    obtain ⟨p, hp, hb⟩ := h
    exact Finset.prod_eq_zero hp (if_neg hb)

private theorem square_complement (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (n : ℕ) :
    (∑ V ∈ Q.powerset, (-1 : ℂ) ^ V.card * (if (∏ p ∈ V, p) ^ 2 ∣ n then 1 else 0)) =
      if ∃ p ∈ Q, p ^ 2 ∣ n then 0 else 1 := by
  have he (V : Finset ℕ) (hV : V ∈ Q.powerset) :
      (if (∏ p ∈ V, p) ^ 2 ∣ n then (1 : ℂ) else 0) =
        ∏ p ∈ V, if p ^ 2 ∣ n then (1 : ℂ) else 0 := by
    rw [prod_bool]
    simp only [prod_primes_sq_dvd_iff V (fun p hp ↦ hQ p (Finset.mem_powerset.mp hV hp)) n]
  have hc (p : ℕ) : (1 - if p ^ 2 ∣ n then (1 : ℂ) else 0) =
      if ¬p ^ 2 ∣ n then 1 else 0 := by by_cases h : p ^ 2 ∣ n <;> simp [h]
  calc
    _ = ∑ V ∈ Q.powerset, (-1 : ℂ) ^ V.card * ∏ p ∈ V, if p ^ 2 ∣ n then (1 : ℂ) else 0 :=
      Finset.sum_congr rfl (fun V hV ↦ by rw [he V hV])
    _ = ∏ p ∈ Q, (1 - if p ^ 2 ∣ n then (1 : ℂ) else 0) := by
      rw [Finset.prod_sub]
      simp only [Finset.prod_const_one, mul_one]
    _ = _ := by
      simp_rw [hc]
      rw [prod_bool]
      by_cases h : ∃ p ∈ Q, p ^ 2 ∣ n
      · have hf : ¬∀ p ∈ Q, ¬p ^ 2 ∣ n := by
          obtain ⟨p, hp, hpn⟩ := h
          exact fun hh ↦ hh p hp hpn
        rw [if_neg hf, if_pos h]
      · have hf : ∀ p ∈ Q, ¬p ^ 2 ∣ n := fun p hp hpn ↦ h ⟨p, hp, hpn⟩
        rw [if_pos hf, if_neg h]

/-- Exact signed inclusion-exclusion for every selected square inside
an arbitrary first-power prime multiple, retaining all shared primes. -/
theorem primeSquareMultipleMask_mul_eq (W Q : Finset ℕ)
    (hW : ∀ p ∈ W, p.Prime) (hQ : ∀ p ∈ Q, p.Prime) (F : ℕ → ℂ) (n : ℕ) :
    primeSquareMultipleMask W Q n * F n =
      (if (∏ p ∈ W, p) ∣ n then F n else 0) -
        ∑ V ∈ Q.powerset, (-1 : ℂ) ^ V.card *
          (if primeSquareIntersection W V ∣ n then F n else 0) := by
  have hi (V : Finset ℕ) (hV : V ∈ Q.powerset) :
      (if primeSquareIntersection W V ∣ n then F n else 0) =
        (if (∏ p ∈ W, p) ∣ n then F n else 0) *
          (if (∏ p ∈ V, p) ^ 2 ∣ n then 1 else 0) := by
    simp only [primeSquareIntersection_dvd_iff W V hW
      (fun p hp ↦ hQ p (Finset.mem_powerset.mp hV hp)) n]
    split_ifs <;> simp_all
  have he : (∑ V ∈ Q.powerset, (-1 : ℂ) ^ V.card *
        (if primeSquareIntersection W V ∣ n then F n else 0)) =
      (if (∏ p ∈ W, p) ∣ n then F n else 0) *
        (if ∃ p ∈ Q, p ^ 2 ∣ n then 0 else 1) := by
    rw [← square_complement Q hQ n, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro V hV
    rw [hi V hV]
    ring
  rw [he]
  by_cases hw : (∏ p ∈ W, p) ∣ n <;>
    by_cases hq : ∃ p ∈ Q, p ^ 2 ∣ n <;> simp [primeSquareMultipleMask, hw, hq]

/-- The repeated-prime survivor is exactly its full square union minus
all first-power prime-pattern deletions, with every sign and intersection
retained for arbitrary complex physical weights. -/
theorem primeSquareSurvivorMask_mul_eq (S Q : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (F : ℕ → ℂ) (n : ℕ) :
    primeSquareSurvivorMask S Q n * F n = primeSquareMultipleMask ∅ Q n * F n -
      ∑ T ∈ S.powerset.filter (fun T ↦ 2 ≤ T.card), ∑ U ∈ (S \ T).powerset,
        (-1 : ℂ) ^ U.card * (primeSquareMultipleMask (T ∪ U) Q n * F n) := by
  by_cases hq : ∃ p ∈ Q, p ^ 2 ∣ n
  · simp only [primeSquareSurvivorMask, primeSquareMultipleMask, hq, and_true,
      Finset.prod_empty, one_dvd, if_true, ite_mul, one_mul, zero_mul]
    rw [← primePairSieve_eq_signed_patterns S hS F n]
    by_cases hc : (S.filter (fun p ↦ p ∣ n)).card ≤ 1
    · rw [if_pos hc, if_neg (by omega), sub_zero]
    · rw [if_neg hc, if_pos (by omega), sub_self]
  · simp [primeSquareSurvivorMask, primeSquareMultipleMask, hq]

/-- A selected repeated-prime term is not squarefree. -/
theorem primeSquareSurvivorMask_eq_zero_of_squarefree (S Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) {n : ℕ} (hn : Squarefree n) :
    primeSquareSurvivorMask S Q n = 0 := by
  have hq : ¬∃ p ∈ Q, p ^ 2 ∣ n := by
    rintro ⟨p, hp, hpn⟩
    exact (Nat.squarefree_iff_prime_squarefree.mp hn p (hQ p hp)) (by simpa only [pow_two] using hpn)
  simp [primeSquareSurvivorMask, hq]

/-- When every prime divisor of the physical index is selected
for square detection, absence of a selected square is exactly squarefreeness. -/
theorem squarefree_iff_no_selected_prime_square (Q : Finset ℕ) (n : ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (hall : ∀ p, p.Prime → p ∣ n → p ∈ Q) :
    Squarefree n ↔ ¬∃ p ∈ Q, p ^ 2 ∣ n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  constructor
  · intro h
    rintro ⟨p, hp, hpn⟩
    exact h p (hQ p hp) (by simpa only [pow_two] using hpn)
  · intro h p hp hpn
    have hd : p ∣ n := (Nat.dvd_mul_right p p).trans hpn
    exact h ⟨p, hall p hp hd, by simpa only [pow_two] using hpn⟩

end
end RiemannGaussian
