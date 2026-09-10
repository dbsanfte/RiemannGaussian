/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusDivisorBoundary

/-!
# The signed profile of a two-prime cutoff fibre

The four divisor terms are kept together. In the middle cutoff range
their entire dependence on the ambient product cancels, leaving one
negative prime logarithm. The other boundary ranges are retained exactly.
In particular, rough semiprimes have a nonzero negative tail coefficient;
complete-fibre cancellation does not annihilate the boundary.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The full four-term profile before any sign or endpoint is discarded. -/
theorem zetaMoebiusLogDivisorFibre_two_primes (D n : ℕ) {p q d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p.Coprime q) (hd : 0 < d) :
    zetaMoebiusLogDivisorFibre D (p * q) n d =
      (if D < d then (Real.log (((p * q : ℕ) : ℝ) * n) : ℂ) - (Real.log d : ℂ) else 0) -
      (if D < p * d then (Real.log (((p * q : ℕ) : ℝ) * n) : ℂ) -
        (Real.log p : ℂ) - (Real.log d : ℂ) else 0) -
      (if D < q * d then (Real.log (((p * q : ℕ) : ℝ) * n) : ℂ) -
        (Real.log q : ℂ) - (Real.log d : ℂ) else 0) +
      (if D < (p * q) * d then (Real.log (((p * q : ℕ) : ℝ) * n) : ℂ) -
        (Real.log p : ℂ) - (Real.log q : ℂ) - (Real.log d : ℂ) else 0) := by
  rw [zetaMoebiusLogDivisorFibre, sum_divisors_coprime_product hpq, hq.sum_divisors]
  simp_rw [hp.sum_divisors]
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hpq]
  simp only [ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.moebius_apply_prime hq,
    mul_one, one_mul, ArithmeticFunction.moebius_apply_one, Nat.cast_mul]
  rw [Real.log_mul (x := (p : ℝ) * q) (y := (d : ℝ))
      (by exact_mod_cast (Nat.mul_pos hp.pos hq.pos).ne') (by exact_mod_cast hd.ne'),
    Real.log_mul (x := (p : ℝ)) (y := (q : ℝ))
      (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero),
    Real.log_mul (x := (p : ℝ)) (y := (d : ℝ))
      (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hd.ne'),
    Real.log_mul (x := (q : ℝ)) (y := (d : ℝ))
      (by exact_mod_cast hq.ne_zero) (by exact_mod_cast hd.ne')]
  simp only [Complex.ofReal_add, Int.cast_mul, Int.cast_neg, Int.cast_one]
  split_ifs <;> ring_nf

/-- In the middle range the ambient logarithm cancels completely.
The signed fibre is exactly `-log p`, independent of the product size. -/
theorem zetaMoebiusLogDivisorFibre_middle (D n : ℕ) {p q d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p.Coprime q)
    (hleft : D < q * d) (hright : p * d ≤ D) :
    zetaMoebiusLogDivisorFibre D (p * q) n d = -(Real.log p : ℂ) := by
  have hd : 0 < d := by nlinarith
  have hbase : d ≤ D := (Nat.le_mul_of_pos_left d hp.pos).trans hright
  have htop : D < (p * q) * d := by nlinarith [hp.one_lt]
  rw [zetaMoebiusLogDivisorFibre_two_primes D n hp hq hpq hd,
    if_neg (not_lt.mpr hbase), if_neg (not_lt.mpr hright), if_pos hleft, if_pos htop]
  ring

/-- The middle-fibre norm has no logarithm of the ambient integer. -/
theorem norm_zetaMoebiusLogDivisorFibre_middle (D n : ℕ) {p q d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p.Coprime q)
    (hleft : D < q * d) (hright : p * d ≤ D) :
    ‖zetaMoebiusLogDivisorFibre D (p * q) n d‖ = Real.log p := by
  rw [zetaMoebiusLogDivisorFibre_middle D n hp hq hpq hleft hright,
    norm_neg, Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg p)]

/-- At the outer boundary all but the divisor-one term survive.
Their signed sum is the negative full logarithmic offset. -/
theorem zetaMoebiusLogDivisorFibre_outer (D n : ℕ) {p q d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p.Coprime q) (hd : 0 < d)
    (hbase : d ≤ D) (hpD : D < p * d) (hqD : D < q * d) :
    zetaMoebiusLogDivisorFibre D (p * q) n d =
      -((Real.log (((p * q : ℕ) : ℝ) * n) : ℂ) - (Real.log d : ℂ)) := by
  have htop : D < (p * q) * d := by nlinarith [hp.one_lt]
  rw [zetaMoebiusLogDivisorFibre_two_primes D n hp hq hpq hd,
    if_neg (not_lt.mpr hbase), if_pos hpD, if_pos hqD, if_pos htop]
  ring

/-- The first boundary range retains exactly the complementary logarithm.
Its sign is opposite to that of the outer and middle logarithmic profiles. -/
theorem zetaMoebiusLogDivisorFibre_inner (D : ℕ) {p q n d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p.Coprime q) (hn : 0 < n) (hd : 0 < d)
    (hpD : p * d ≤ D) (hqD : q * d ≤ D) (htop : D < (p * q) * d) :
    zetaMoebiusLogDivisorFibre D (p * q) n d =
      (Real.log n : ℂ) - (Real.log d : ℂ) := by
  have hbase : d ≤ D := (Nat.le_mul_of_pos_left d hp.pos).trans hpD
  rw [zetaMoebiusLogDivisorFibre_two_primes D n hp hq hpq hd,
    if_neg (not_lt.mpr hbase), if_neg (not_lt.mpr hpD), if_neg (not_lt.mpr hqD), if_pos htop]
  rw [Real.log_mul (by exact_mod_cast (Nat.mul_pos hp.pos hq.pos).ne')
    (by exact_mod_cast hn.ne'), Nat.cast_mul,
    Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
  push_cast
  ring

/-- The surviving boundary is real arithmetic: every product of two
distinct primes above the cutoff has coefficient exactly `-log(p*q)`. -/
theorem zetaMoebiusLogTailCoefficient_rough_semiprime {D p q : ℕ}
    (hD : 1 ≤ D) (hp : p.Prime) (hq : q.Prime) (hpq : p.Coprime q)
    (hDp : D < p) (hDq : D < q) :
    zetaMoebiusLogTailCoefficient D (p * q) = -(Real.log (p * q : ℕ) : ℂ) := by
  have hf := zetaMoebiusLogTailCoefficient_eq_fibres D (Nat.coprime_one_right (p * q))
  simp only [mul_one, Nat.divisors_one, Finset.sum_singleton,
    ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul] at hf
  rw [hf, zetaMoebiusLogDivisorFibre_outer D 1 hp hq hpq (by omega) hD
    (by simpa using hDp) (by simpa using hDq)]
  simp

end
end RiemannGaussian
