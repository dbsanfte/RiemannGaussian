/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeGroupSelection
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt

/-!
# Quantitative targets for useful-group coverage

A power of two of size B supplies an arithmetically admissible Hasse order
whose cofactor is at most B²+1 when B² ≤ p ≤ B³. Realising that order over
the unknown prime and finding a separating public curve remain unproved.
The generic collision obstruction includes both equal and inverse channels.
This side-investigation algebra is checked in the ordinary library; numerical probes remain optional.
-/

namespace RiemannGaussian.SemiprimeGroupCoverage

open SemiprimeOrderSeparation SemiprimeRoughProjection SemiprimeGroupSelection
open scoped BigOperators

/-- The smallest power of two not less than the desired cover width. -/
def dyadicDivisor (B : ℕ) : ℕ := 2 ^ Nat.clog 2 B

theorem dyadicDivisor_bounds {B : ℕ} (hB : 0 < B) :
    B ≤ dyadicDivisor B ∧ dyadicDivisor B < 2*B := by
  refine ⟨Nat.le_pow_clog (by decide) B, ?_⟩
  by_cases hB1 : B = 1
  · subst B
    norm_num [dyadicDivisor]
  · have hBgt : 1 < B := by omega
    have hc := Nat.clog_pos (by decide : 1 < 2) hBgt
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hBgt
    unfold dyadicDivisor
    rw [← Nat.succ_pred hc.ne', pow_succ]
    omega

/-- Cofactor of the first D-multiple strictly above p. -/
def roundedCofactor (p D : ℕ) : ℕ := p/D+1

/-- Candidate curve order, before any unknown-field realisation. -/
def roundedOrder (p D : ℕ) : ℕ := D*roundedCofactor p D

theorem roundedOrder_interval {p D : ℕ} (hD : 0 < D) :
    p+1 ≤ roundedOrder p D ∧ roundedOrder p D ≤ p+D := by
  have hm := Nat.mod_lt p hD
  have he := Nat.mod_add_div p D
  unfold roundedOrder roundedCofactor
  constructor
  · calc
      p+1 = D*(p/D)+(p%D+1) := by omega
      _ ≤ D*(p/D)+D := Nat.add_le_add_left (Nat.succ_le_of_lt hm) _
      _ = D*(p/D+1) := by ring
  · calc
      D*(p/D+1) = p/D*D+D := by ring
      _ ≤ p+D := Nat.add_le_add_right (Nat.div_mul_le_self p D) D

theorem roundedCofactor_pos (p D : ℕ) : 0 < roundedCofactor p D := by
  unfold roundedCofactor
  exact Nat.succ_pos _

theorem roundedCofactor_bound {p B D : ℕ}
    (hB : 0 < B) (hBD : B ≤ D) (hp : p ≤ B^3) :
    roundedCofactor p D ≤ B^2+1 := by
  have hd := Nat.div_mul_le_self p D
  have hm : B*(p/D) ≤ D*(p/D) := Nat.mul_le_mul_right _ hBD
  have he : B^3 = B*B^2 := by ring
  unfold roundedCofactor
  by_contra hn
  have hlarge : B^2+1 ≤ p/D := by omega
  have hs := Nat.mul_le_mul_left B hlarge
  nlinarith

/-- A constructive Hasse-interval arithmetic target. This does not assert
that a public curve realising it can be found without the hidden prime. -/
theorem dyadic_hasse_order_target {p B : ℕ} (hB : 0 < B)
    (hlo : B^2 ≤ p) (hhi : p ≤ B^3) :
    B ≤ dyadicDivisor B ∧ dyadicDivisor B < 2*B ∧
      0 < roundedCofactor p (dyadicDivisor B) ∧
      roundedCofactor p (dyadicDivisor B) ≤ B^2+1 ∧
      p+1 ≤ roundedOrder p (dyadicDivisor B) ∧
      roundedOrder p (dyadicDivisor B) ≤ p+1+2*Nat.sqrt p := by
  obtain ⟨hDlo, hDhi⟩ := dyadicDivisor_bounds hB
  have hD : 0 < dyadicDivisor B := lt_of_lt_of_le hB hDlo
  obtain ⟨hordlo, hordhi⟩ := roundedOrder_interval (p := p) hD
  have hs : B ≤ Nat.sqrt p := Nat.le_sqrt'.mpr hlo
  refine ⟨hDlo, hDhi, roundedCofactor_pos _ _,
    roundedCofactor_bound hB hDlo hhi, hordlo, ?_⟩
  omega

/-- Every prime-size range below B³ has a candidate Hasse order with a
small cofactor. Small p use trace zero; larger p use the dyadic target.
This is an arithmetic existence theorem, not a curve-generation algorithm. -/
theorem exists_hasse_order_small_cofactor {p B : ℕ}
    (hB : 0 < B) (hp : p ≤ B^3) :
    ∃ a c : ℕ, 0 < c ∧ c ≤ (B+1)^2 ∧
      p+1 ≤ 2^a*c ∧ 2^a*c ≤ p+1+2*Nat.sqrt p := by
  by_cases hlo : p ≤ B^2
  · refine ⟨0, p+1, Nat.succ_pos _, ?_, ?_, ?_⟩
    · nlinarith
    · simp
    · simp
  · obtain ⟨_, _, hc, hcB, horderlo, horderhi⟩ :=
      dyadic_hasse_order_target hB (by omega) hp
    refine ⟨Nat.clog 2 B, roundedCofactor p (dyadicDivisor B), hc, ?_,
      horderlo, horderhi⟩
    exact hcB.trans (by nlinarith)

/-- The smaller factor of a semiprime lies below the cubic width scale. -/
theorem smaller_factor_le_cubic_width {p q B : ℕ}
    (hpq : p ≤ q) (hbudget : p*q ≤ B^6) : p ≤ B^3 := by
  have hs : p*p ≤ p*q := Nat.mul_le_mul_left p hpq
  have he : B^6 = B^3*B^3 := by ring
  rw [he] at hbudget
  apply (Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).mp
  simpa only [pow_two] using hs.trans hbudget

/-- Arithmetic useful-order targets cover every smaller semiprime factor.
The input-dependent public curve and the separating point are still missing. -/
theorem semiprime_hasse_order_target {p q B : ℕ}
    (hB : 0 < B) (hpq : p ≤ q) (hbudget : p*q ≤ B^6) :
    ∃ a c : ℕ, 0 < c ∧ c ≤ (B+1)^2 ∧
      p+1 ≤ 2^a*c ∧ 2^a*c ≤ p+1+2*Nat.sqrt p :=
  exists_hasse_order_small_cofactor hB (smaller_factor_le_cubic_width hpq hbudget)

/-- Once a curve order actually divides this target and the chosen exponent
contains D, its residual point order fits the slightly padded cover. -/
theorem projected_candidate_order_bound {G : Type*} [Group G]
    (a : G) {p B D E : ℕ} (hB : 0 < B) (hBD : B ≤ D)
    (hp : p ≤ B^3) (ha : orderOf a ∣ roundedOrder p D) (hDE : D ∣ E) :
    orderOf (a^E) ≤ (B+1)^2 := by
  have hD : 0 < D := lt_of_lt_of_le hB hBD
  have hc := partial_projection_order_dvd a hD ha hDE
  have hb := roundedCofactor_bound hB hBD hp
  have hle := Nat.le_of_dvd (roundedCofactor_pos p D) hc
  have hpad : B^2+1 ≤ (B+1)^2 := by nlinarith
  exact hle.trans (hb.trans hpad)

/-- Actual order realisation and separation are distinct requirements.
Neither is inferred from semiprimality or from Hasse's interval alone. -/
theorem candidate_has_separating_cover {G H : Type*}
    [Group G] [Group H] [Finite G] (a : G) (b : H)
    {p B D E : ℕ} (hB : 0 < B) (hBD : B ≤ D) (hp : p ≤ B^3)
    (ha : orderOf a ∣ roundedOrder p D) (hDE : D ∣ E)
    (hc : (orderOf (a^E)).Coprime (orderOf (b^E)))
    (hb : orderOf (b^E) ≠ 1) :
    ∃ j i : ℕ, 1 ≤ j ∧ j ≤ B+1 ∧ i < B+1 ∧
      (a^E)^((B+1)*j) = (a^E)^i ∧ (b^E)^((B+1)*j) ≠ (b^E)^i := by
  have hbound := projected_candidate_order_bound a hB hBD hp ha hDE
  obtain ⟨d, hd, hdB, had, hbd⟩ :=
    bounded_separating_witness (a^E) (b^E) hc (orderOf_pos _) hbound hb
  exact partial_witness_in_linear_cover (by omega) hd hdB had hbd

/-- A smaller positive period separates two local groups. Coprimality of
the periods is sufficient but unnecessary: a strict inequality suffices. -/
theorem smaller_period_separates {G H : Type*} [Group G] [Group H]
    (a : G) (b : H) (ha : 0 < orderOf a) (hab : orderOf a < orderOf b) :
    a^(orderOf a) = 1 ∧ b^(orderOf a) ≠ 1 := by
  refine ⟨pow_orderOf_eq_one a, ?_⟩
  intro h
  have hd := orderOf_dvd_of_pow_eq_one h
  exact (Nat.not_dvd_of_pos_of_lt ha hab) hd

/-- A useful group only needs unequal local periods and a small minimum.
This removes the unnecessary coprimality premise from a coverage search. -/
theorem unequal_small_periods_have_cover {G H : Type*}
    [Group G] [Group H] [Finite G] [Finite H] (a : G) (b : H)
    {B : ℕ} (hB : 0 < B) (hne : orderOf a ≠ orderOf b)
    (hsmall : min (orderOf a) (orderOf b) ≤ B^2) :
    ∃ j i : ℕ, 1 ≤ j ∧ j ≤ B ∧ i < B ∧
      ((a^(B*j) = a^i ∧ b^(B*j) ≠ b^i) ∨
       (b^(B*j) = b^i ∧ a^(B*j) ≠ a^i)) := by
  rcases lt_or_gt_of_ne hne with hab | hba
  · rw [min_eq_left hab.le] at hsmall
    obtain ⟨hleft, hright⟩ := smaller_period_separates a b (orderOf_pos _) hab
    obtain ⟨j, i, hj, hjB, hi, hpa, hpb⟩ :=
      partial_witness_in_linear_cover hB (orderOf_pos _) hsmall hleft hright
    exact ⟨j, i, hj, hjB, hi, Or.inl ⟨hpa, hpb⟩⟩
  · rw [min_eq_right hba.le] at hsmall
    obtain ⟨hleft, hright⟩ := smaller_period_separates b a (orderOf_pos _) hba
    obtain ⟨j, i, hj, hjB, hi, hpa, hpb⟩ :=
      partial_witness_in_linear_cover hB (orderOf_pos _) hsmall hleft hright
    exact ⟨j, i, hj, hjB, hi, Or.inr ⟨hpa, hpb⟩⟩

/-- The smaller period supplies either a baby identity or a cover leaf
separated in BOTH x-coordinate orientations. For i=0 the second branch is
a giant identity. This avoids losing the factor to an opposite-sign alias. -/
theorem smaller_period_has_two_orientation_cover {G H : Type*}
    [Group G] [Group H] (a : G) (b : H) {B : ℕ}
    (hB : 0 < B) (ha : 0 < orderOf a)
    (hab : orderOf a < orderOf b) (hsmall : orderOf a ≤ B^2) :
    (orderOf a < B ∧ a^(orderOf a) = 1 ∧ b^(orderOf a) ≠ 1) ∨
      ∃ j i : ℕ, 1 ≤ j ∧ j ≤ B ∧ i < B ∧
        a^(B*j)*a^i = 1 ∧ b^(B*j) ≠ b^i ∧ b^(B*j)*b^i ≠ 1 := by
  obtain ⟨haa, hbb⟩ := smaller_period_separates a b ha hab
  by_cases hbelow : orderOf a < B
  · exact Or.inl ⟨hbelow, haa, hbb⟩
  · let j := orderOf a / B
    let i := orderOf a % B
    have hi : i < B := Nat.mod_lt _ hB
    have hj : 1 ≤ j := Nat.div_pos (by omega) hB
    have hprod : B*j ≤ orderOf a := by
      simpa [j, Nat.mul_comm] using Nat.div_mul_le_self (orderOf a) B
    have hjB : j ≤ B := by nlinarith
    have he : B*j+i = orderOf a := by
      simpa [j, i, Nat.add_comm] using Nat.mod_add_div (orderOf a) B
    have hile : i ≤ B*j := by nlinarith
    have hBj : B ≤ B*j := by nlinarith
    have hdiffpos : 0 < B*j-i := by omega
    have hdifflt : B*j-i < orderOf b :=
      lt_of_le_of_lt ((Nat.sub_le _ _).trans hprod) hab
    refine Or.inr ⟨j, i, hj, hjB, hi, ?_, ?_, ?_⟩
    · rw [← pow_add, he]
      exact haa
    · intro halias
      have hpow : b^(B*j-i) = 1 := by
        apply mul_right_cancel (b := b^i)
        rw [← pow_add, Nat.sub_add_cancel hile, halias, one_mul]
      exact Nat.not_dvd_of_pos_of_lt hdiffpos hdifflt
        (orderOf_dvd_of_pow_eq_one hpow)
    · rw [← pow_add, he]
      exact hbb

/-- Equal periods make every integer-exponent alias coherent across the
two groups, including negative exponents and inverse channels. -/
theorem same_period_coherent_aliases {G H : Type*} [Group G] [Group H]
    (a : G) (b : H) (hab : orderOf a = orderOf b) (i j : ℤ) :
    a^i = a^j ↔ b^i = b^j := by
  rw [← orderOf_dvd_sub_iff_zpow_eq_zpow, ← orderOf_dvd_sub_iff_zpow_eq_zpow, hab]

/-- Constant forced torsion cannot alone supply the growing cofactor bound
when the group order is on the cubic scale. This is an arithmetic envelope
obstruction, not an impossibility theorem for ECM or other algorithms. -/
theorem fixed_divisor_cubic_gap {B D : ℕ} (hD : D < B) (hB : 0 < B) :
    D*B^2 < B^3 := by
  have hs : 0 < B^2 := pow_pos hB _
  simpa only [pow_succ, Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right hD hs

/-- A group homomorphism whose kernel is killed by a coprime exponent
preserves the entire element period. Cheap isogeny-like changes cannot
shorten a long prime period unless their kernel reaches that prime. -/
theorem period_preserved_by_coprime_kernel {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a : G) {D : ℕ}
    (hkernel : ∀ x : G, f x = 1 → x^D = 1)
    (hc : (orderOf a).Coprime D) : orderOf (f a) = orderOf a := by
  apply Nat.dvd_antisymm
  · exact orderOf_map_dvd f a
  · have hm : f (a^(orderOf (f a))) = 1 := by
      rw [map_pow, pow_orderOf_eq_one]
    have hp := hkernel _ hm
    rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one] at hp
    exact hc.dvd_of_dvd_mul_right (by simpa [Nat.mul_comm] using hp)

/-- A prime larger than a factorial prefix cannot occur in that prefix. -/
theorem prime_not_dvd_factorial_above {q : ℕ} (hq : q.Prime) :
    ∀ k : ℕ, k < q → ¬q ∣ k.factorial := by
  intro k
  induction k with
  | zero =>
    intro _
    simpa using hq.not_dvd_one
  | succ k ih =>
    intro hk hd
    rw [Nat.factorial_succ] at hd
    rcases hq.dvd_mul.mp hd with hleft | hright
    · exact Nat.not_dvd_of_pos_of_lt (Nat.succ_pos k) hk hleft
    · exact ih (by omega) hright

/-- The additive integer-prefix group has unconditional separating
coverage when the smaller prime lies in the quadratic cover. Polynomial
batching evaluates this prefix without materialising the factorial. -/
theorem factorial_prefix_recovers_smaller_prime {p q B : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hsmall : p ≤ B^2) (hlarge : B^2 < q) :
    (p*q).gcd ((B^2).factorial) = p := by
  apply gcd_semiprime_of_separating_residue hq
  · exact Nat.dvd_factorial hp.pos hsmall
  · exact prime_not_dvd_factorial_above hq _ hlarge

theorem sixth_budget_above_quadratic_prefix {B : ℕ} (hB : 4 ≤ B) :
    B^4 < (B-1)^6 := by
  have hk : 3 ≤ B-1 := by omega
  have he : B = (B-1)+1 := by omega
  have hsq : B^2 ≤ 2*(B-1)^2 := by
    rw [he]
    simp only [Nat.add_sub_cancel]
    nlinarith
  have hfour := Nat.mul_le_mul hsq hsq
  have hfour' : B^4 ≤ 4*(B-1)^4 := by convert hfour using 1 <;> ring
  have hgt : 4 < (B-1)^2 := by nlinarith
  have hp : 0 < (B-1)^4 := pow_pos (by omega) _
  have hlast := Nat.mul_lt_mul_of_pos_right hgt hp
  have hlast' : 4*(B-1)^4 < (B-1)^6 := by convert hlast using 1; ring
  exact hfour'.trans_lt hlast'

/-- For the actual ceiling-sixth-root budget, the larger factor is outside
the quadratic prefix, so the prefix automatically separates the small one. -/
theorem larger_factor_above_prefix {p q B : ℕ} (hB : 4 ≤ B)
    (hpq : p ≤ q) (hbudget : (B-1)^6 < p*q) : B^2 < q := by
  by_contra hn
  have hq : q ≤ B^2 := by omega
  have hp := hpq.trans hq
  have hprod := Nat.mul_le_mul hp hq
  have hprod' : p*q ≤ B^4 := by convert hprod using 1; ring
  have hgap := sixth_budget_above_quadratic_prefix hB
  omega

theorem prefix_recovers_under_sixth_budget {p q B : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hB : 4 ≤ B) (hpq : p ≤ q)
    (hbudget : (B-1)^6 < p*q) (hsmall : p ≤ B^2) :
    (p*q).gcd ((B^2).factorial) = p :=
  factorial_prefix_recovers_smaller_prime hp hq hsmall
    (larger_factor_above_prefix hB hpq hbudget)

/-- Degree-B polynomial evaluation at a positive block endpoint. -/
theorem descending_block_eq_polynomial (n : ℕ) :
    ∀ B : ℕ, n.descFactorial B = ∏ i ∈ Finset.range B, (n-i)
  | 0 => by simp
  | B+1 => by
    rw [Nat.descFactorial, Finset.prod_range_succ_comm, descending_block_eq_polynomial n B]

theorem prefix_rows_eq_factorial (B : ℕ) :
    ∀ J : ℕ, (∏ j ∈ Finset.range J, (B*(j+1)).descFactorial B) = (B*J).factorial
  | 0 => by simp
  | J+1 => by
    rw [Finset.prod_range_succ, prefix_rows_eq_factorial B J]
    have hB : B ≤ B*(J+1) := by nlinarith
    have he : B*(J+1)-B = B*J := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel]
    simpa only [he] using Nat.factorial_mul_descFactorial hB

/-- The joined B-by-B integer cover evaluated by polynomial batching. -/
def prefixProduct (B : ℕ) : ℕ :=
  ∏ j ∈ Finset.range B, (B*(j+1)).descFactorial B

theorem prefixProduct_eq_factorial (B : ℕ) : prefixProduct B = (B^2).factorial := by
  simpa only [prefixProduct, pow_two] using prefix_rows_eq_factorial B B

/-- A guaranteed separating prefix, with every degree-B row retained.
The identity supplies coverage, not a formal bit-cost theorem for the
Python product/remainder-tree implementation. -/
theorem polynomial_prefix_recovers_under_sixth_budget {p q B : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hB : 4 ≤ B) (hpq : p ≤ q)
    (hbudget : (B-1)^6 < p*q) (hsmall : p ≤ B^2) :
    (p*q).gcd (prefixProduct B) = p := by
  rw [prefixProduct_eq_factorial]
  exact prefix_recovers_under_sixth_budget hp hq hB hpq hbudget hsmall

/-- A failed complete prefix rules out all small prime factors. This
certifies exactly which population still needs useful curve coverage. -/
theorem failed_prefix_excludes_small_prime {n p B : ℕ}
    (hp : p.Prime) (hpn : p ∣ n) (hclear : n.gcd ((B^2).factorial) = 1) :
    B^2 < p := by
  by_contra hn
  have hd := Nat.dvd_factorial hp.pos (by omega : p ≤ B^2)
  have hboth := Nat.dvd_gcd hpn hd
  rw [hclear] at hboth
  exact hp.not_dvd_one hboth

theorem counterexample_semiprime_and_budget :
    Nat.Prime 248909 ∧ Nat.Prime 249521 ∧
      248909*249521 = (62108022589 : ℕ) ∧
      62^6 < (62108022589 : ℕ) ∧ (62108022589 : ℕ) ≤ 63^6 := by
  norm_num

/-- A second implementation control lies outside both the quadratic
small-factor prefix and the allotted near-square window. These arithmetic
checks do not verify the whole Python ECM pipeline. -/
theorem separated_control_semiprime_and_windows :
    Nat.Prime 203653 ∧ Nat.Prime 230003 ∧
      203653*230003 = (46840800959 : ℕ) ∧
      60^6 < (46840800959 : ℕ) ∧ (46840800959 : ℕ) ≤ 61^6 ∧
      61^2 < (203653 : ℕ) ∧
      216427^2 < (46840800959 : ℕ) ∧ (46840800959 : ℕ) ≤ 216428^2 ∧
      203653+230003 = 2*(216828 : ℕ) ∧
      (216428+61)^2 < (216828 : ℕ)^2 := by
  norm_num

/-- Observed residual periods; these constants are not asserted to be
elliptic point orders without a separate group-law certificate. -/
def counterexamplePeriods : List ℕ :=
  [5189, 20789, 20773, 20753, 20719, 20873, 5189, 6949]

theorem counterexample_periods_above_cover :
    ∀ d ∈ counterexamplePeriods, 63^2+63 < d := by
  simp only [counterexamplePeriods, List.mem_cons]
  norm_num

/-- Under an actual period certificate, neither orientation of any cover
leaf can vanish. Includes every smaller probe width. -/
theorem counterexample_periods_miss_every_stage {B d i j : ℕ}
    (hB : 0 < B) (hcap : B ≤ 63) (hd : d ∈ counterexamplePeriods)
    (hi : i < B) (hj : 0 < j) (hjB : j ≤ B) :
    ¬d ∣ B*j-i ∧ ¬d ∣ B*j+i := by
  have hs : B^2 ≤ 63^2 := Nat.pow_le_pow_left hcap 2
  have hlarge := counterexample_periods_above_cover d hd
  exact long_order_outside_linear_cover hB hi hj hjB (by omega)

theorem sigma13_recovery_certificate :
    checkedSignal 62108022589 35762846846 = some 249521 := by
  norm_num [checkedSignal]

end RiemannGaussian.SemiprimeGroupCoverage
