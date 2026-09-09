/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimePairDiagonal

/-!
# Product size and logarithmic separation of the surviving prime pairs

On a product of powers of two distinct primes, the entire ordered
von-Mangoldt convolution consists of two terms. Its exact coefficient
retains a logarithmic separation square, rather than only an upper
bound in terms of the product. This is arithmetic of the actual
surviving coefficient; the separation is retained before any complex
kernel is applied.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

private theorem factor_pair_eq {A B u v : ℕ} (hA : 0 < A) (hB : 0 < B)
    (hu : u ∣ A) (hv : v ∣ B) (he : u * v = A * B) : u = A ∧ v = B := by
  have huA := Nat.le_of_dvd hA hu
  have hvB := Nat.le_of_dvd hB hv
  have hu' : u = A := by
    apply Nat.le_antisymm huA
    by_contra hn
    have hlt : u < A := by omega
    have hprod := (Nat.mul_le_mul_left u hvB).trans_lt (Nat.mul_lt_mul_of_pos_right hlt hB)
    omega
  subst u
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hA he⟩

private theorem prime_not_dvd_other_power {p q k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) : ¬ p ∣ q ^ k := by
  intro h
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h))

private theorem nonzero_pair_cases {p q a b u v : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (ha : 0 < a) (hb : 0 < b)
    (he : u * v = p ^ a * q ^ b)
    (hu : IsPrimePow u) (hv : IsPrimePow v) :
    (u = p ^ a ∧ v = q ^ b) ∨ (u = q ^ b ∧ v = p ^ a) := by
  have hcop : (p ^ a).Coprime (q ^ b) := (hp.coprime_iff_not_dvd.mpr
    (fun h ↦ hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h))).pow a b
  have hud := (hcop.isPrimePow_dvd_mul hu).mp (show u ∣ p ^ a * q ^ b from ⟨v, he.symm⟩)
  have hvd := (hcop.isPrimePow_dvd_mul hv).mp
    (show v ∣ p ^ a * q ^ b from ⟨u, by simpa only [mul_comm] using he.symm⟩)
  rcases hud with huA | huB <;> rcases hvd with hvA | hvB
  · have hqprod : q ∣ u * v := by
      rw [he]
      exact dvd_mul_of_dvd_right (dvd_pow_self q hb.ne') _
    rcases hq.dvd_mul.mp hqprod with hqu | hqv
    · exact False.elim (prime_not_dvd_other_power hq hp hpq.symm (hqu.trans huA))
    · exact False.elim (prime_not_dvd_other_power hq hp hpq.symm (hqv.trans hvA))
  · exact Or.inl (factor_pair_eq (pow_pos hp.pos _) (pow_pos hq.pos _) huA hvB he)
  · exact Or.inr (factor_pair_eq (pow_pos hq.pos _) (pow_pos hp.pos _) huB hvA
      (by simpa only [mul_comm] using he))
  · have hpprod : p ∣ u * v := by
      rw [he]
      exact dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') _
    rcases hp.dvd_mul.mp hpprod with hpu | hpv
    · exact False.elim (prime_not_dvd_other_power hp hq hpq (hpu.trans huB))
    · exact False.elim (prime_not_dvd_other_power hp hq hpq (hpv.trans hvB))

private theorem prime_powers_ne {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (ha : 0 < a) : p ^ a ≠ q ^ b := by
  intro he
  exact prime_not_dvd_other_power hp hq hpq (he ▸ dvd_pow_self p ha.ne')

/-- On any product of powers of two distinct primes, the complete
convolution has exactly the two ordered prime-base contributions.
The coefficient is independent of the two positive exponents. -/
theorem zetaPrimePairArithmetic_two_prime_powers {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (ha : 0 < a) (hb : 0 < b) :
    zetaPrimePairArithmetic (p ^ a * q ^ b) = 2 * Real.log p * Real.log q := by
  have hn : p ^ a * q ^ b ≠ 0 := mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero)
  have hne : (p ^ a, q ^ b) ≠ (q ^ b, p ^ a) := by
    intro h
    exact prime_powers_ne hp hq hpq ha (congrArg Prod.fst h)
  have hsub : ({(p ^ a, q ^ b), (q ^ b, p ^ a)} : Finset (ℕ × ℕ)) ⊆
      (p ^ a * q ^ b).divisorsAntidiagonal := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hn⟩
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨mul_comm _ _, hn⟩
  rw [zetaPrimePairArithmetic, ArithmeticFunction.mul_apply]
  calc
    _ = ∑ z ∈ ({(p ^ a, q ^ b), (q ^ b, p ^ a)} : Finset (ℕ × ℕ)),
        ArithmeticFunction.vonMangoldt z.1 * ArithmeticFunction.vonMangoldt z.2 := by
      symm
      apply Finset.sum_subset hsub
      intro z hz hnot
      by_contra hnon
      have hu : IsPrimePow z.1 := by
        by_contra h
        exact (mul_ne_zero_iff.mp hnon).1 (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h)
      have hv : IsPrimePow z.2 := by
        by_contra h
        exact (mul_ne_zero_iff.mp hnon).2 (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h)
      rcases nonzero_pair_cases hp hq hpq ha hb (Nat.mem_divisorsAntidiagonal.mp hz).1 hu hv with h | h
      · have hz' : z = (p ^ a, q ^ b) := Prod.ext h.1 h.2
        exact hnot (by simp [hz'])
      · have hz' : z = (q ^ b, p ^ a) := Prod.ext h.1 h.2
        exact hnot (by simp [hz'])
    _ = _ := by
      have hmem : (p ^ a, q ^ b) ∉ ({(q ^ b, p ^ a)} : Finset (ℕ × ℕ)) := by
        simpa only [Finset.mem_singleton] using hne
      rw [Finset.sum_insert hmem, Finset.sum_singleton]
      simp only [ArithmeticFunction.vonMangoldt_apply_pow ha.ne',
        ArithmeticFunction.vonMangoldt_apply_pow hb.ne',
        ArithmeticFunction.vonMangoldt_apply_prime hp, ArithmeticFunction.vonMangoldt_apply_prime hq]
      ring

private theorem not_primePow_product {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (ha : 0 < a) (hb : 0 < b) : ¬ IsPrimePow (p ^ a * q ^ b) := by
  intro hn
  obtain ⟨r, k, hr, _, he⟩ := (isPrimePow_nat_iff _).mp hn
  have hpd : p ∣ r := hp.dvd_of_dvd_pow (he ▸ dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') (q ^ b))
  have hqd : q ∣ r := hq.dvd_of_dvd_pow (he ▸ dvd_mul_of_dvd_right (dvd_pow_self q hb.ne') (p ^ a))
  exact hpq (((Nat.prime_dvd_prime_iff_eq hp hr).mp hpd).trans
    ((Nat.prime_dvd_prime_iff_eq hq hr).mp hqd).symm)

/-- The surviving distinct-prime coefficient is exactly the same
two-term value; its support restriction does not alter that coefficient. -/
theorem zetaDistinctPrimePairCoefficient_two_prime_powers {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (ha : 0 < a) (hb : 0 < b) :
    zetaDistinctPrimePairCoefficient (p ^ a * q ^ b) = 2 * Real.log p * Real.log q := by
  rw [zetaDistinctPrimePairCoefficient, if_neg (not_primePow_product hp hq hpq ha hb)]
  exact zetaPrimePairArithmetic_two_prime_powers hp hq hpq ha hb

/-- Product size and logarithmic separation retain the full
coefficient exactly. The exponents penalize the coefficient separately
from the separation of the two prime-power factors. -/
theorem zetaDistinctPrimePairCoefficient_separation {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (ha : 0 < a) (hb : 0 < b) :
    2 * (a : ℝ) * b * zetaDistinctPrimePairCoefficient (p ^ a * q ^ b) =
      Real.log (p ^ a * q ^ b : ℕ) ^ 2 -
        (Real.log (p ^ a : ℕ) - Real.log (q ^ b : ℕ)) ^ 2 := by
  rw [zetaDistinctPrimePairCoefficient_two_prime_powers hp hq hpq ha hb]
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  simp only [Nat.cast_mul, Nat.cast_pow, Real.log_mul
    (pow_ne_zero a hp0) (pow_ne_zero b hq0),
    Real.log_pow]
  ring

/-- The product-size upper bound is downstream of the exact
separation identity, leaving its nonnegative defect available. -/
theorem zetaDistinctPrimePairCoefficient_product_bound {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (ha : 0 < a) (hb : 0 < b) :
    zetaDistinctPrimePairCoefficient (p ^ a * q ^ b) ≤
      Real.log (p ^ a * q ^ b : ℕ) ^ 2 / (2 * (a : ℝ) * b) := by
  have hab : (0 : ℝ) < 2 * (a : ℝ) * b := by positivity
  apply (le_div_iff₀ hab).mpr
  have h := zetaDistinctPrimePairCoefficient_separation hp hq hpq ha hb
  nlinarith [sq_nonneg (Real.log (p ^ a : ℕ) - Real.log (q ^ b : ℕ))]

end

end RiemannGaussian
