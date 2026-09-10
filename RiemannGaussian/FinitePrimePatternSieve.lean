/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusLcmBound
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exact prime-divisibility patterns and their weighted overlap cost

The union of products with at least two selected prime divisors is
partitioned by its complete divisibility pattern. Expanding only the
excluded primes gives a finite signed family of mixed-prime factors.
All overlap terms are retained before their factor-sensitive cost is
bounded by one product over the original selected primes.
-/

open Complex
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- A product of distinct selected primes divides an integer exactly
when every selected prime divides it, including the zero integer. -/
theorem prod_primes_dvd_iff (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (n : ℕ) :
    (∏ p ∈ S, p) ∣ n ↔ ∀ p ∈ S, p ∣ n := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem id hp).trans h
  · intro h
    by_cases hn : n = 0
    · simp [hn]
    · apply dvd_trans _ (Nat.prod_primeFactors_dvd n)
      apply Finset.prod_dvd_prod_of_subset
      intro p hp
      exact Nat.mem_primeFactors.mpr ⟨hS p hp, h p hp, hn⟩

/-- Every product containing at least two distinct selected primes is
an eligible mixed-prime arithmetic factor, with all side conditions proved. -/
theorem prod_primes_eligible (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hcard : 2 ≤ S.card) :
    0 < (∏ p ∈ S, p) ∧ (∏ p ∈ S, p) ≠ 1 ∧ ¬IsPrimePow (∏ p ∈ S, p) := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
  have hpd : p ∣ ∏ r ∈ S, r := Finset.dvd_prod_of_mem id hp
  have hqd : q ∣ ∏ r ∈ S, r := Finset.dvd_prod_of_mem id hq
  refine ⟨Finset.prod_pos (fun r hr ↦ (hS r hr).pos), ?_, ?_⟩
  · intro h
    exact (hS p hp).ne_one (Nat.eq_one_of_dvd_one (h ▸ hpd))
  · intro h
    obtain ⟨r, _, hu⟩ := isPrimePow_iff_unique_prime_dvd.mp h
    exact hpq ((hu p ⟨hS p hp, hpd⟩).trans (hu q ⟨hS q hq, hqd⟩).symm)

/-- All distinct-prime pair factors from the selected primes, with
coincident products grouped by the finite image. -/
def primePairFactors (S : Finset ℕ) : Finset ℕ :=
  S.offDiag.image (fun pq ↦ pq.1 * pq.2)

/-- The selected-prime count is exactly the original divisibility
union over all distinct-prime pair factors. -/
theorem primePairSieve_card_iff (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (n : ℕ) :
    2 ≤ (S.filter (fun p ↦ p ∣ n)).card ↔ ∃ P ∈ primePairFactors S, P ∣ n := by
  constructor
  · intro h
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (show 1 < (S.filter (fun p ↦ p ∣ n)).card by omega)
    obtain ⟨hpS, hpn⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqS, hqn⟩ := Finset.mem_filter.mp hq
    refine ⟨p * q, Finset.mem_image.mpr ⟨(p, q), Finset.mem_offDiag.mpr ⟨hpS, hqS, hpq⟩, rfl⟩, ?_⟩
    exact ((Nat.coprime_primes (hS p hpS) (hS q hqS)).mpr hpq).mul_dvd_of_dvd_of_dvd hpn hqn
  · rintro ⟨P, hP, hPn⟩
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨hpS, hqS, hpq⟩ := Finset.mem_offDiag.mp hpq
    have hp : p ∈ S.filter (fun p ↦ p ∣ n) := Finset.mem_filter.mpr
      ⟨hpS, (Nat.dvd_mul_right p q).trans hPn⟩
    have hq : q ∈ S.filter (fun p ↦ p ∣ n) := Finset.mem_filter.mpr
      ⟨hqS, (Nat.dvd_mul_left q p).trans hPn⟩
    have h := Finset.one_lt_card.mpr ⟨p, hp, q, hq, hpq⟩
    omega

/-- The literal pair-factor sieve has every arithmetic eligibility
condition discharged from the selected-prime hypothesis. -/
theorem primePairFactors_eligible (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∀ P ∈ primePairFactors S, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P := by
  intro P hP
  obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.mp hP
  obtain ⟨hpS, hqS, hpq⟩ := Finset.mem_offDiag.mp hpq
  have hp := hS p hpS
  have hq := hS q hqS
  refine ⟨Nat.mul_pos hp.pos hq.pos, ?_, ?_⟩
  · intro h
    exact hp.ne_one (Nat.eq_one_of_dvd_one (h ▸ Nat.dvd_mul_right p q))
  · intro h
    obtain ⟨r, _, hu⟩ := isPrimePow_iff_unique_prime_dvd.mp h
    exact hpq ((hu p ⟨hp, Nat.dvd_mul_right p q⟩).trans (hu q ⟨hq, Nat.dvd_mul_left q p⟩).symm)

private theorem prod_bool (S : Finset ℕ) (b : ℕ → Prop) [DecidablePred b] :
    (∏ p ∈ S, if b p then (1 : ℂ) else 0) = if ∀ p ∈ S, b p then 1 else 0 := by
  by_cases h : ∀ p ∈ S, b p
  · rw [if_pos h]
    exact Finset.prod_eq_one (fun p hp ↦ if_pos (h p hp))
  · rw [if_neg h]
    push Not at h
    obtain ⟨p, hp, hb⟩ := h
    exact Finset.prod_eq_zero hp (if_neg hb)

private theorem prime_pattern_eq (S T : Finset ℕ) (hT : T ⊆ S) (n : ℕ) :
    (∏ p ∈ T, if p ∣ n then (1 : ℂ) else 0) *
      (∏ p ∈ S \ T, (1 - if p ∣ n then (1 : ℂ) else 0)) =
        if T = S.filter (fun p ↦ p ∣ n) then 1 else 0 := by
  have he : (∀ p ∈ T, p ∣ n) ∧ (∀ p ∈ S \ T, ¬p ∣ n) ↔
      T = S.filter (fun p ↦ p ∣ n) := by
    constructor
    · rintro ⟨ht, hu⟩
      ext p
      constructor
      · intro hp
        exact Finset.mem_filter.mpr ⟨hT hp, ht p hp⟩
      · intro hp
        obtain ⟨hpS, hpn⟩ := Finset.mem_filter.mp hp
        by_contra hpT
        exact hu p (Finset.mem_sdiff.mpr ⟨hpS, hpT⟩) hpn
    · intro h
      subst T
      constructor
      · intro p hp
        exact (Finset.mem_filter.mp hp).2
      · intro p hp hpn
        obtain ⟨hpS, hpT⟩ := Finset.mem_sdiff.mp hp
        exact hpT (Finset.mem_filter.mpr ⟨hpS, hpn⟩)
  have hc (p : ℕ) : (1 - if p ∣ n then (1 : ℂ) else 0) =
      if ¬p ∣ n then 1 else 0 := by by_cases h : p ∣ n <;> simp [h]
  simp_rw [hc]
  rw [prod_bool, prod_bool]
  by_cases heq : T = S.filter (fun p ↦ p ∣ n)
  · obtain ⟨ht, hu⟩ := he.mpr heq
    rw [if_pos ht, if_pos hu, if_pos heq, one_mul]
  · rw [if_neg heq]
    by_cases ht : ∀ p ∈ T, p ∣ n
    · have hu : ¬∀ p ∈ S \ T, ¬p ∣ n := fun hu ↦ heq (he.mp ⟨ht, hu⟩)
      rw [if_neg hu, mul_zero]
    · rw [if_neg ht, zero_mul]

/-- The literal at-least-two-prime mask is the full signed pattern
expansion for every complex physical weight. No overlaps are omitted. -/
theorem primePairSieve_eq_signed_patterns (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (F : ℕ → ℂ) (n : ℕ) :
    (if 2 ≤ (S.filter (fun p ↦ p ∣ n)).card then F n else 0) =
      ∑ T ∈ S.powerset.filter (fun T ↦ 2 ≤ T.card), ∑ U ∈ (S \ T).powerset,
        (-1 : ℂ) ^ U.card * (if (∏ p ∈ T ∪ U, p) ∣ n then F n else 0) := by
  let b : ℕ → ℂ := fun p ↦ if p ∣ n then 1 else 0
  have hpartition :
      (∑ T ∈ S.powerset.filter (fun T ↦ 2 ≤ T.card),
        ((∏ p ∈ T, b p) * ∏ p ∈ S \ T, (1 - b p)) * F n) =
      if 2 ≤ (S.filter (fun p ↦ p ∣ n)).card then F n else 0 := by
    have he (T : Finset ℕ) (hT : T ∈ S.powerset.filter (fun T ↦ 2 ≤ T.card)) :
        ((∏ p ∈ T, b p) * ∏ p ∈ S \ T, (1 - b p)) * F n =
          (if T = S.filter (fun p ↦ p ∣ n) then F n else 0) := by
      rw [show (∏ p ∈ T, b p) * ∏ p ∈ S \ T, (1 - b p) =
        if T = S.filter (fun p ↦ p ∣ n) then 1 else 0 from
          prime_pattern_eq S T (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1) n]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl he]
    simp [Finset.sum_ite_eq', Finset.filter_subset]
  rw [← hpartition]
  apply Finset.sum_congr rfl
  intro T hT
  have hTS := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
  rw [Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro U hU
  have hUS := Finset.mem_powerset.mp hU
  have hdis : Disjoint T U := Finset.disjoint_left.mpr (fun p hpT hpU ↦
    (Finset.mem_sdiff.mp (hUS hpU)).2 hpT)
  have hTU : T ∪ U ⊆ S := Finset.union_subset hTS (fun p hp ↦ (Finset.mem_sdiff.mp (hUS hp)).1)
  have hb : (∏ p ∈ T, b p) * ∏ p ∈ U, b p =
      if (∏ p ∈ T ∪ U, p) ∣ n then 1 else 0 := by
    rw [← Finset.prod_union hdis, prod_bool]
    simp only [← prod_primes_dvd_iff (T ∪ U) (fun p hp ↦ hS p (hTU hp))]
  calc
    _ = (-1 : ℂ) ^ U.card * (((∏ p ∈ T, b p) * ∏ p ∈ U, b p) * F n) := by ring
    _ = _ := by rw [hb]; split_ifs <;> simp

/-- The complete factor correction factors over any finite set of
distinct primes; all valuations in the surrounding arithmetic remain free. -/
theorem lcmSqrtFactorMass_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    lcmSqrtFactorMass (∏ p ∈ S, p) = ∏ p ∈ S, lcmSqrtFactorMass p := by
  induction S using Finset.induction_on with
  | empty => simp [lcmSqrtFactorMass]
  | @insert p S hp ih =>
    have hprime := hS p (Finset.mem_insert_self _ _)
    have hrest (q : ℕ) (hq : q ∈ S) := hS q (Finset.mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ S, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes hprime (hrest q hq)).mpr (fun he ↦ hp (he ▸ hq))
    rw [Finset.prod_insert hp, lcmSqrtFactorMass_mul hcop, ih hrest, Finset.prod_insert hp]

/-- The full signed pattern expansion has one product bound for its
factor-sensitive absolute mass, despite all intersection coincidences. -/
theorem sum_prime_pattern_factor_mass_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∑ T ∈ S.powerset.filter (fun T ↦ 2 ≤ T.card), ∑ U ∈ (S \ T).powerset,
      lcmSqrtFactorMass (∏ p ∈ T ∪ U, p)) ≤
        ∏ p ∈ S, (1 + 2 * lcmSqrtFactorMass p) := by
  have he (T : Finset ℕ) (hT : T ∈ S.powerset) :
      (∑ U ∈ (S \ T).powerset, lcmSqrtFactorMass (∏ p ∈ T ∪ U, p)) =
        (∏ p ∈ T, lcmSqrtFactorMass p) * ∏ p ∈ S \ T, (1 + lcmSqrtFactorMass p) := by
    rw [Finset.prod_one_add, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro U hU
    have hTS := Finset.mem_powerset.mp hT
    have hUS := Finset.mem_powerset.mp hU
    have hTU : T ∪ U ⊆ S := Finset.union_subset hTS (fun p hp ↦ (Finset.mem_sdiff.mp (hUS hp)).1)
    have hdis : Disjoint T U := Finset.disjoint_left.mpr (fun p hpT hpU ↦
      (Finset.mem_sdiff.mp (hUS hpU)).2 hpT)
    rw [lcmSqrtFactorMass_prod_primes (T ∪ U) (fun p hp ↦ hS p (hTU hp)), Finset.prod_union hdis]
  calc
    _ ≤ ∑ T ∈ S.powerset, ∑ U ∈ (S \ T).powerset,
        lcmSqrtFactorMass (∏ p ∈ T ∪ U, p) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun T _ _ ↦ Finset.sum_nonneg (fun U _ ↦ lcmSqrtFactorMass_nonneg _))
    _ = ∑ T ∈ S.powerset, (∏ p ∈ T, lcmSqrtFactorMass p) *
        ∏ p ∈ S \ T, (1 + lcmSqrtFactorMass p) := Finset.sum_congr rfl he
    _ = ∏ p ∈ S, (lcmSqrtFactorMass p + (1 + lcmSqrtFactorMass p)) := (Finset.prod_add _ _ _).symm
    _ = _ := Finset.prod_congr rfl (fun _ _ ↦ by ring)

/-- The logarithm of every selected intersection factor is bounded by
the complete selected-prime logarithmic mass. -/
theorem log_prod_primes_le_sum (S T : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hT : T ⊆ S) :
    Real.log (∏ p ∈ T, p : ℕ) ≤ ∑ p ∈ S, Real.log p := by
  rw [Nat.cast_prod, Real.log_prod (fun p hp ↦ by exact_mod_cast (hS p (hT hp)).ne_zero)]
  exact Finset.sum_le_sum_of_subset_of_nonneg hT (fun p _ _ ↦ Real.log_natCast_nonneg p)

/-- An explicit allowance for the complete signed prime-pattern
family, including its logarithmic companion and all intersections. -/
def primePatternSieveCost (S : Finset ℕ) : ℝ :=
  (1 + ∑ p ∈ S, Real.log p) * ∏ p ∈ S, (1 + 2 * lcmSqrtFactorMass p)

/-- The complete pattern allowance is nonnegative. -/
theorem primePatternSieveCost_nonneg (S : Finset ℕ) : 0 ≤ primePatternSieveCost S := by
  unfold primePatternSieveCost
  apply mul_nonneg
  · exact add_nonneg (by norm_num) (Finset.sum_nonneg (fun p _ ↦ Real.log_natCast_nonneg p))
  · exact Finset.prod_nonneg (fun p _ ↦ by linarith [lcmSqrtFactorMass_nonneg p])

/-- Every actual overlap in the pattern expansion is paid by one
product over the selected primes. No unproved overlap budget is assumed. -/
theorem sum_prime_pattern_lcm_cost_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∑ T ∈ S.powerset.filter (fun T ↦ 2 ≤ T.card), ∑ U ∈ (S \ T).powerset,
      zetaMoebiusLcmCost (∏ p ∈ T ∪ U, p)) ≤ primePatternSieveCost S := by
  calc
    _ ≤ ∑ T ∈ S.powerset.filter (fun T ↦ 2 ≤ T.card), ∑ U ∈ (S \ T).powerset,
        (1 + ∑ p ∈ S, Real.log p) * lcmSqrtFactorMass (∏ p ∈ T ∪ U, p) := by
      apply Finset.sum_le_sum
      intro T hT
      apply Finset.sum_le_sum
      intro U hU
      have hTS := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
      have hUS := Finset.mem_powerset.mp hU
      have hTU : T ∪ U ⊆ S := Finset.union_subset hTS (fun p hp ↦ (Finset.mem_sdiff.mp (hUS hp)).1)
      apply (min_le_right _ _).trans
      exact mul_le_mul_of_nonneg_right (by linarith [log_prod_primes_le_sum S (T ∪ U) hS hTU])
        (lcmSqrtFactorMass_nonneg _)
    _ = (1 + ∑ p ∈ S, Real.log p) *
        ∑ T ∈ S.powerset.filter (fun T ↦ 2 ≤ T.card), ∑ U ∈ (S \ T).powerset,
          lcmSqrtFactorMass (∏ p ∈ T ∪ U, p) := by simp_rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_prime_pattern_factor_mass_le S hS)
      (add_nonneg (by norm_num) (Finset.sum_nonneg (fun p _ ↦ Real.log_natCast_nonneg p)))

/-- Every term of the exact pattern expansion is an eligible arithmetic
factor, even when several patterns produce the same intersection integer. -/
theorem prime_pattern_factor_eligible (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {T U : Finset ℕ} (hT : T ∈ S.powerset.filter (fun T ↦ 2 ≤ T.card))
    (hU : U ∈ (S \ T).powerset) :
    0 < (∏ p ∈ T ∪ U, p) ∧ (∏ p ∈ T ∪ U, p) ≠ 1 ∧ ¬IsPrimePow (∏ p ∈ T ∪ U, p) := by
  have hTS := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
  have hUS := Finset.mem_powerset.mp hU
  have hTU : T ∪ U ⊆ S := Finset.union_subset hTS (fun p hp ↦ (Finset.mem_sdiff.mp (hUS hp)).1)
  exact prod_primes_eligible (T ∪ U) (fun p hp ↦ hS p (hTU hp))
    ((Finset.mem_filter.mp hT).2.trans (Finset.card_le_card Finset.subset_union_left))

/-- For every prime the elementary divisor correction is at most
twice its inverse square root. -/
theorem lcmSqrtFactorMass_prime_le {p : ℕ} (hp : p.Prime) :
    lcmSqrtFactorMass p ≤ 2 / Real.sqrt p := by
  rw [lcmSqrtFactorMass_prime hp]
  have hs : (1 : ℝ) ≤ Real.sqrt p := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ p by exact_mod_cast hp.one_lt.le)
  have hi : 1 / Real.sqrt p ≤ 1 := (div_le_one (by positivity)).mpr hs
  calc
    _ ≤ (1 / Real.sqrt p) * 2 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

/-- A uniform complete overlap allowance for every finite family of
primes bounded by `R`. The exponential grows with `sqrt(R)`, and the
logarithmic companion has an explicit polynomial cost. -/
theorem primePatternSieveCost_le_exp_sqrt (S : Finset ℕ) (R : ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ R) :
    primePatternSieveCost S ≤ (1 + (R : ℝ) ^ 2) * Real.exp (8 * Real.sqrt R) := by
  have hsub : S ⊆ Finset.Icc 1 R := fun p hp ↦ Finset.mem_Icc.mpr ⟨(hS p hp).1.pos, (hS p hp).2⟩
  have hcard : S.card ≤ R := by simpa using Finset.card_le_card hsub
  have hlog : (∑ p ∈ S, Real.log p) ≤ (R : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _p ∈ S, (R : ℝ) := Finset.sum_le_sum (fun p hp ↦
        (Real.log_le_self (Nat.cast_nonneg p)).trans (by exact_mod_cast (hS p hp).2))
      _ ≤ (R : ℝ) ^ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        exact (mul_le_mul_of_nonneg_right (show (S.card : ℝ) ≤ R by exact_mod_cast hcard)
          (Nat.cast_nonneg R)).trans_eq (by ring)
  have hmass : (∑ p ∈ S, lcmSqrtFactorMass p) ≤ 4 * Real.sqrt R := by
    calc
      _ ≤ ∑ p ∈ S, 2 / Real.sqrt p := Finset.sum_le_sum (fun p hp ↦ lcmSqrtFactorMass_prime_le (hS p hp).1)
      _ ≤ ∑ p ∈ Finset.Icc 1 R, 2 / Real.sqrt p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ ↦ by positivity)
      _ = 2 * ∑ p ∈ Finset.Icc 1 R, 1 / Real.sqrt p := by rw [Finset.mul_sum]; congr 1; funext p; ring
      _ ≤ _ := by nlinarith [sum_inv_sqrt_Icc_le R]
  have hprod : (∏ p ∈ S, (1 + 2 * lcmSqrtFactorMass p)) ≤ Real.exp (8 * Real.sqrt R) := by
    calc
      _ ≤ ∏ p ∈ S, Real.exp (2 * lcmSqrtFactorMass p) := Finset.prod_le_prod
        (fun p _ ↦ by linarith [lcmSqrtFactorMass_nonneg p])
        (fun p _ ↦ by simpa only [add_comm] using Real.add_one_le_exp (2 * lcmSqrtFactorMass p))
      _ = Real.exp (2 * ∑ p ∈ S, lcmSqrtFactorMass p) := by rw [← Real.exp_sum, Finset.mul_sum]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  exact mul_le_mul (by linarith : (1 : ℝ) + ∑ p ∈ S, Real.log p ≤ 1 + (R : ℝ) ^ 2) hprod
    (Finset.prod_nonneg (fun p _ ↦ by linarith [lcmSqrtFactorMass_nonneg p])) (by positivity)

end
end RiemannGaussian
