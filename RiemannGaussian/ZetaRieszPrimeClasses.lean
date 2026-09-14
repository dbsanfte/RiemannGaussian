/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeFourier
import RiemannGaussian.ZetaRieszFixedCofactor
import Mathlib.NumberTheory.Primorial

/-!
# Prime-count classes in the original Riesz carrier

The original squarefree composite band has no all-small-prime labels
from order 60 onward. Its exact partition retains the one-large-prime and
at-least-two-large-prime classes, with every original coefficient and phase.
-/

namespace RiemannGaussian.ZetaRieszPrimeClasses
noncomputable section
open scoped BigOperators

/-- The number of distinct prime factors in the controlled large-prime
range; every smaller prime stays in the explicit finite head. -/
def largePrimeCount (n : ℕ) : ℕ := (n.primeFactors.filter (fun p => 16 ≤ p)).card

/-- Zero large-prime count means every actual prime factor is below 16. -/
theorem largePrimeCount_eq_zero_iff (n : ℕ) :
    largePrimeCount n = 0 ↔ ∀ p ∈ n.primeFactors, p < 16 := by
  simp only [largePrimeCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff, not_le]

/-- The fixed small-prime universe has exactly this finite product. -/
theorem primorial_fifteen : primorial 15 = 30030 := by decide

/-- A squarefree integer with no large prime factor lies below the exact
product of the six small primes. -/
theorem small_only_le {n : ℕ} (hn : Squarefree n) (hcount : largePrimeCount n = 0) :
    n ≤ 30030 := by
  have hp := (largePrimeCount_eq_zero_iff n).mp hcount
  have hsub : n.primeFactors ⊆ Nat.primesLE 15 := by
    intro p hpn
    have hp' := hp p hpn
    exact Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_of_mem_primeFactors hpn⟩
  have hd := Finset.prod_dvd_prod_of_subset n.primeFactors (Nat.primesLE 15) id hsub
  simp only [Function.id_def] at hd
  rw [Nat.prod_primeFactors_of_squarefree hn, ← primorial_eq_prod_primesLE,
    primorial_fifteen] at hd
  exact Nat.le_of_dvd (by norm_num) hd

/-- From order 60 onward, the original band contains no squarefree
integer built only from primes below 16. This is an exact support deletion. -/
theorem small_only_not_mem_band {N n : ℕ} (hN : 60 ≤ N) (hn : Squarefree n)
    (hcount : largePrimeCount n = 0) : n ∉ zetaPrimeLogBand N := by
  intro hb
  have hsmall := small_only_le hn hcount
  have hlower := (Finset.mem_filter.mp hb).2
  have hpos := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
  have hn32 : (n : ℝ) ≤ (2 : ℝ) ^ 15 := by norm_num; exact_mod_cast (hsmall.trans (by norm_num))
  have hlog := Real.log_le_log (by exact_mod_cast hpos : (0 : ℝ) < n) hn32
  rw [Real.log_pow] at hlog
  have hN' : (60 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hN' hlog2.le
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

/-- Every surviving squarefree original-band label has a large prime
factor once the fixed small-prime range has been exhausted. -/
theorem largePrimeCount_pos_of_mem_band {N n : ℕ} (hN : 60 ≤ N)
    (hn : Squarefree n) (hb : n ∈ zetaPrimeLogBand N) : 0 < largePrimeCount n := by
  apply Nat.pos_of_ne_zero
  intro hz
  exact small_only_not_mem_band hN hn hz hb

/-- The actual carrier splits into the one-large-prime and at-least-two
large-prime classes. No size or sign estimate for either surviving sum
is asserted by this exact support partition. -/
theorem actual_band_eq_two_prime_classes (P : Polynomial ℂ) (N : ℕ)
    (hN : 60 ≤ N) (y L : ℝ) :
    zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y =
      (∑ n ∈ (zetaPrimeLogBand N).filter (fun n =>
        (Squarefree n ∧ n ≠ 1 ∧ ¬ n.Prime) ∧ largePrimeCount n = 1),
        SquarefreeVaughanLogSource.coefficient L n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) +
      ∑ n ∈ (zetaPrimeLogBand N).filter (fun n =>
        (Squarefree n ∧ n ≠ 1 ∧ ¬ n.Prime) ∧ 2 ≤ largePrimeCount n),
        SquarefreeVaughanLogSource.coefficient L n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
  simp only [zetaArithmeticBand, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hg : Squarefree n ∧ n ≠ 1 ∧ ¬ n.Prime
  · have hc := largePrimeCount_pos_of_mem_band hN hg.1 hn
    by_cases h1 : largePrimeCount n = 1
    · rw [if_pos ⟨hg, h1⟩, if_neg (by rintro ⟨_hg, h2⟩; omega), add_zero]
    · have h2 : 2 ≤ largePrimeCount n := by omega
      rw [if_neg (by rintro ⟨_hg, h1'⟩; exact h1 h1'), if_pos ⟨hg, h2⟩, zero_add]
  · have hz : SquarefreeVaughanLogSource.coefficient L n = 0 := by
      rw [ZetaRieszPrimeFourier.coefficient_eq_primePair_integral, if_neg hg]
    simp only [hz, zero_mul, ite_self, zero_add]

/-- Every all-small squarefree cofactor divides the fixed six-prime product. -/
theorem small_only_dvd {a : ℕ} (ha : Squarefree a) (hc : largePrimeCount a = 0) :
    a ∣ 30030 := by
  have hsmall := (largePrimeCount_eq_zero_iff a).mp hc
  have hsub : a.primeFactors ⊆ Nat.primesLE 15 := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨by have := hsmall p hp; omega,
      Nat.prime_of_mem_primeFactors hp⟩
  have hd := Finset.prod_dvd_prod_of_subset a.primeFactors (Nat.primesLE 15) id hsub
  simpa only [Function.id_def, Nat.prod_primeFactors_of_squarefree ha,
    ← primorial_eq_prod_primesLE, primorial_fifteen] using hd

/-- The actual one-large-prime class consists of one large prime and a
nonunit divisor of 30030. Squarefreeness excludes repeated prime insertion. -/
theorem one_large_prime_factorization {n : ℕ} (hn : Squarefree n) (hnp : ¬ n.Prime)
    (hc : largePrimeCount n = 1) :
    ∃ a p : ℕ, a ∣ 30030 ∧ 1 < a ∧ Squarefree a ∧ p.Prime ∧ 16 ≤ p ∧
      ¬ p ∣ a ∧ n = p * a := by
  obtain ⟨p, hp, huniq⟩ := Finset.card_eq_one_iff_existsUnique.mp hc
  have hpn := (Finset.mem_filter.mp hp).1
  have hp16 := (Finset.mem_filter.mp hp).2
  have hprime := Nat.prime_of_mem_primeFactors hpn
  obtain ⟨a, he⟩ := Nat.dvd_of_mem_primeFactors hpn
  have hsf : Squarefree (p * a) := by rwa [← he]
  have hasf := (Nat.squarefree_mul_iff.mp hsf).2.2
  have hpa : ¬ p ∣ a := hprime.coprime_iff_not_dvd.mp
    (Nat.coprime_of_squarefree_mul hsf)
  have ha1 : 1 < a := by
    have ha0 := Nat.pos_of_ne_zero hasf.ne_zero
    have ha_ne : a ≠ 1 := by
      intro he1
      apply hnp
      simpa only [he, he1, mul_one] using hprime
    omega
  have hac : largePrimeCount a = 0 := by
    apply (largePrimeCount_eq_zero_iff a).mpr
    intro q hqa
    by_contra hqsmall
    have hqn : q ∈ n.primeFactors := Nat.primeFactors_mono
      (by rw [he]; exact dvd_mul_left a p) hn.ne_zero hqa
    have hqp : q = p := huniq q (Finset.mem_filter.mpr ⟨hqn, by omega⟩)
    exact hpa (hqp ▸ Nat.dvd_of_mem_primeFactors hqa)
  exact ⟨a, p, small_only_dvd hasf hac, ha1, hasf, hprime, hp16, hpa, he⟩

/-- The six prime fixed cofactors that can leave a semiprime tail. -/
theorem prime_divisor_small_product {a : ℕ} (ha : a.Prime) (had : a ∣ 30030) :
    a ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ) := by
  have hp : a ∈ (primorial 15).primeFactors :=
    ha.mem_primeFactors (primorial_fifteen ▸ had) (primorial_ne_zero 15)
  rw [primeFactors_primorial] at hp
  have he : Nat.primesLE 15 = ({2, 3, 5, 7, 11, 13} : Finset ℕ) := by decide
  rwa [he] at hp

/-- Every fixed composite cofactor in the original one-large-prime
partition has its entire prime-insertion band independently tending to zero. -/
theorem tendsto_small_composite_cofactor_band {a : ℕ} (had : a ∣ 30030)
    (ha1 : a ≠ 1) (hap : ¬ a.Prime) (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Filter.Tendsto (fun N => (u : ℂ) ^ (N + 1) *
      ∑ n ∈ ZetaRieszFixedCofactor.primeCofactorBand a N,
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) Filter.atTop (nhds 0) := by
  have ha : Squarefree a := (squarefree_primorial 15).squarefree_of_dvd
    (primorial_fifteen ▸ had)
  exact ZetaRieszFixedCofactor.tendsto_actual_composite_cofactor_band ha ha1 hap P y hu hu1

end
end RiemannGaussian.ZetaRieszPrimeClasses
