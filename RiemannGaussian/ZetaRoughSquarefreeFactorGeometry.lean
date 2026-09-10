/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRoughSquarefreePrimeBalance
import RiemannGaussian.ZetaMoebiusDivisorBoundary

/-!
# Factor geometry of the original rough squarefree carrier

Complete divisor fibres cancel the large-prime logarithm whenever the
cofactor lies below the actual divisor cutoff. Composite squarefree
cofactors vanish pointwise; prime cofactors leave only their own logarithm.
The source-preserving unit-divisor approximation remains available, but
these local estimates use the original signed coefficient.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian
noncomputable section

/-- A prime larger than the divisor cutoff is automatically coprime to
every positive cofactor below that cutoff. -/
theorem prime_coprime_of_cutoff_separation {D p m : ℕ} (hp : p.Prime)
    (hDp : D < p) (hm : 0 < m) (hmD : m ≤ D) : p.Coprime m := by
  apply hp.coprime_iff_not_dvd.mpr
  intro h
  exact (not_le_of_gt (hmD.trans_lt hDp)) (Nat.le_of_dvd hm h)

/-- In the unbalanced sector, all dependence on the large prime's
logarithm cancels. This follows from the existing complete divisor fibres,
before replacing the full prefix by its unit row. -/
theorem zetaMoebiusLogTailCoefficient_large_prime_small_cofactor {D p m : ℕ} (hp : p.Prime)
    (hDp : D < p) (hm : 1 < m) (hmD : m ≤ D) :
    zetaMoebiusLogTailCoefficient D (p * m) =
      -(ArithmeticFunction.vonMangoldt m : ℂ) := by
  have hcop := (prime_coprime_of_cutoff_separation hp hDp (by omega) hmD).symm
  rw [Nat.mul_comm p m, zetaMoebiusLogTailCoefficient_eq_fibres D hcop, hp.sum_divisors,
    zetaMoebiusLogDivisorFibre_empty D m p 1 (by simpa using hmD),
    zetaMoebiusLogDivisorFibre_complete D m p hDp]
  simp [ne_of_gt hm, ArithmeticFunction.moebius_apply_prime hp]

/-- For a squarefree cofactor the only surviving unbalanced terms are
semiprimes, and their coefficient is the negative SMALL prime logarithm. -/
theorem zetaMoebiusLogTailCoefficient_large_prime_squarefree_cofactor {D p m : ℕ} (hp : p.Prime)
    (hDp : D < p) (hm : 1 < m) (hmD : m ≤ D) (hsf : Squarefree m) :
    zetaMoebiusLogTailCoefficient D (p * m) =
      if m.Prime then -(Real.log m : ℂ) else 0 := by
  rw [zetaMoebiusLogTailCoefficient_large_prime_small_cofactor hp hDp hm hmD]
  by_cases hprime : m.Prime
  · simp [hprime, ArithmeticFunction.vonMangoldt_apply_prime hprime]
  · have hpp : ¬IsPrimePow m := fun h ↦ hprime
      (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hsf, h⟩)
    simp [hprime, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]

/-- The rough squarefree carrier agrees with the original tail on its
actual composite support. No unit-divisor approximation is used here. -/
theorem zetaRoughSquarefreeCoefficient_eq_tail_on_support (D : ℕ) (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) {n : ℕ} (hsf : Squarefree n) (hcomp : ¬n.Prime)
    (hrough : ¬∃ a ∈ S, a ∣ n) :
    zetaRoughSquarefreeCoefficient D S n = zetaMoebiusLogTailCoefficient D n := by
  have hpp : ¬IsPrimePow n := fun h ↦ hcomp
    (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hsf, h⟩)
  rw [zetaRoughSquarefreeCoefficient_eq_prefix_add_prime D hD S hS,
    zetaMoebiusLogTailCoefficient_eq_vonMangoldt_add_prefix,
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
  simp [zetaRoughSquarefreePrefixCoefficient, zetaSquarefreeDivisibilityPrefixCoefficient,
    zetaRoughPrimeCoefficient, hrough, hsf, hcomp]

/-- The exact small-cofactor cancellation holds on the literal rough
squarefree survivor, with every selected-prime exclusion retained. -/
theorem zetaRoughSquarefreeCoefficient_large_prime_squarefree_cofactor (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) {D p m : ℕ} (hp : p.Prime)
    (hDp : D < p) (hm : 1 < m) (hmD : m ≤ D) (hsf : Squarefree m)
    (hrough : ¬∃ a ∈ S, a ∣ p * m) :
    zetaRoughSquarefreeCoefficient D S (p * m) =
      if m.Prime then -(Real.log m : ℂ) else 0 := by
  have hcop := prime_coprime_of_cutoff_separation hp hDp (by omega) hmD
  have hsfprod := (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, hsf⟩
  have hcomp : ¬(p * m).Prime := by simp [Nat.prime_mul_iff, hp.ne_one, ne_of_gt hm]
  rw [zetaRoughSquarefreeCoefficient_eq_tail_on_support D (by omega) S hS hsfprod hcomp hrough,
    zetaMoebiusLogTailCoefficient_large_prime_squarefree_cofactor hp hDp hm hmD hsf]

/-- Every small composite cofactor in this unbalanced sector vanishes
pointwise, independently of the kernel, source asymptotic, and window. -/
theorem zetaRoughSquarefreeCoefficient_large_prime_composite_zero (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) {D p m : ℕ} (hp : p.Prime)
    (hDp : D < p) (hm : 1 < m) (hmD : m ≤ D) (hsf : Squarefree m)
    (hcomp : ¬m.Prime) :
    zetaRoughSquarefreeCoefficient D S (p * m) = 0 := by
  by_cases hrough : ∃ a ∈ S, a ∣ p * m
  · simp [zetaRoughSquarefreeCoefficient, hrough]
  rw [zetaRoughSquarefreeCoefficient_large_prime_squarefree_cofactor S hS hp hDp hm hmD hsf hrough, if_neg hcomp]

/-- The surviving small-cofactor weights have a bound involving only
the original divisor cutoff, independent of the arbitrarily large prime. -/
theorem norm_zetaRoughSquarefreeCoefficient_large_prime_small_cofactor_le (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) {D p m : ℕ} (hp : p.Prime)
    (hDp : D < p) (hm : 1 < m) (hmD : m ≤ D) (hsf : Squarefree m) :
    ‖zetaRoughSquarefreeCoefficient D S (p * m)‖ ≤ Real.log D := by
  by_cases hrough : ∃ a ∈ S, a ∣ p * m
  · simpa [zetaRoughSquarefreeCoefficient, hrough] using Real.log_natCast_nonneg D
  rw [zetaRoughSquarefreeCoefficient_large_prime_squarefree_cofactor S hS hp hDp hm hmD hsf hrough]
  split_ifs
  · rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg m)]
    exact Real.log_le_log (by exact_mod_cast (show 0 < m by omega)) (by exact_mod_cast hmD)
  · exact (by simpa only [norm_zero] using Real.log_natCast_nonneg D)

/-- The precise sector removed by complete cofactor cancellation. -/
def zetaSmallCompositeCofactorSector (D n : ℕ) : Prop :=
  ∃ p m : ℕ, p.Prime ∧ D < p ∧ 1 < m ∧ m ≤ D ∧ Squarefree m ∧ ¬m.Prime ∧ n = p * m

/-- The original rough coefficient vanishes on the entire sector,
including all selected-prime overlaps. -/
theorem zetaRoughSquarefreeCoefficient_zero_on_smallCompositeSector (D : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) {n : ℕ} (hn : zetaSmallCompositeCofactorSector D n) :
    zetaRoughSquarefreeCoefficient D S n = 0 := by
  obtain ⟨p, m, hp, hDp, hm, hmD, hsf, hcomp, rfl⟩ := hn
  exact zetaRoughSquarefreeCoefficient_large_prime_composite_zero S hS hp hDp hm hmD hsf hcomp

/-- This arithmetic sector may be deleted from any finite
test window at exactly zero cost, retaining the complete complex kernel. -/
theorem sum_zetaRoughSquarefreeCoefficient_remove_small_composite (D : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (F : ℕ → ℂ) (T : Finset ℕ) :
    (∑ n ∈ T, zetaRoughSquarefreeCoefficient D S n * F n) =
      ∑ n ∈ T.filter (fun n ↦ ¬zetaSmallCompositeCofactorSector D n),
        zetaRoughSquarefreeCoefficient D S n * F n := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : zetaSmallCompositeCofactorSector D n
  · simp [hn, zetaRoughSquarefreeCoefficient_zero_on_smallCompositeSector D S hS hn]
  · simp [hn]


/-- A genuine factorization with both factors strictly past the divisor
cutoff. The product equality is retained, rather than independent ranges. -/
def zetaBalancedFactorization (D n : ℕ) : Prop :=
  ∃ a b : ℕ, D < a ∧ D < b ∧ n = a * b

/-- Above the cubic cutoff, failure of a balanced factorization forces
one prime factor with cofactor at most the original cutoff. This is a
finite integer theorem, with no distribution assumption about primes. -/
theorem exists_large_prime_small_cofactor_of_not_balanced {D n : ℕ}
    (hD : 1 ≤ D) (hn : D ^ 3 < n) (hbal : ¬zetaBalancedFactorization D n) :
    ∃ p m : ℕ, p.Prime ∧ D < p ∧ m ≤ D ∧ n = p * m := by
  have hDcube : D ≤ D ^ 3 := by
    calc
      D ≤ D * D := Nat.le_mul_self D
      _ ≤ (D * D) * D := Nat.le_mul_of_pos_right _ hD
      _ = D ^ 3 := by ring
  have hex : ∃ d : ℕ, d ∣ n ∧ D < d := ⟨n, dvd_rfl, hDcube.trans_lt hn⟩
  let d := Nat.find hex
  have hdvd : d ∣ n := (Nat.find_spec hex).1
  have hdD : D < d := (Nat.find_spec hex).2
  have hd0 : 0 < d := by omega
  have hprod : d * (n / d) = n := Nat.mul_div_cancel' hdvd
  have hcof : n / d ≤ D := by
    by_contra! h
    exact hbal ⟨d, n / d, hdD, h, hprod.symm⟩
  have hsmall (a : ℕ) (ha : a ∣ n) (had : a < d) : a ≤ D := by
    by_contra! h
    exact Nat.find_min hex had ⟨ha, h⟩
  have hprime : d.Prime := by
    by_contra hnp
    obtain ⟨a, had, ha2, halt⟩ := Nat.exists_dvd_of_not_prime2 (by omega : 2 ≤ d) hnp
    have haD : a ≤ D := hsmall a (had.trans hdvd) halt
    have hbD : d / a ≤ D := hsmall (d / a)
      ((Nat.div_dvd_of_dvd had).trans hdvd) (Nat.div_lt_self hd0 ha2)
    have hdprod : a * (d / a) = d := Nat.mul_div_cancel' had
    have hd2 : d ≤ D ^ 2 := by
      calc
        d = a * (d / a) := hdprod.symm
        _ ≤ D * D := Nat.mul_le_mul haD hbD
        _ = D ^ 2 := by ring
    have hnle : n ≤ D ^ 3 := by
      calc
        n = d * (n / d) := hprod.symm
        _ ≤ D ^ 2 * D := Nat.mul_le_mul hd2 hcof
        _ = D ^ 3 := by ring
    omega
  exact ⟨d, n / d, hprime, hdD, hcof, hprod.symm⟩

/-- A nonzero original rough squarefree coefficient above the cubic
cutoff either has a balanced factorization or is an unbalanced semiprime.
The latter retains exactly the smaller prime logarithm. -/
theorem zetaRoughSquarefreeCoefficient_balanced_or_semiprime (D : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {n : ℕ}
    (hn : D ^ 3 < n) (hsf : Squarefree n) (hcomp : ¬n.Prime)
    (hc : zetaRoughSquarefreeCoefficient D S n ≠ 0) :
    zetaBalancedFactorization D n ∨
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ q ≤ D ∧ D < p ∧ n = p * q ∧
        zetaRoughSquarefreeCoefficient D S n = -(Real.log q : ℂ) := by
  by_cases hbal : zetaBalancedFactorization D n
  · exact Or.inl hbal
  obtain ⟨p, q, hp, hDp, hqD, rfl⟩ :=
    exists_large_prime_small_cofactor_of_not_balanced hD hn hbal
  have hqsf : Squarefree q := hsf.of_mul_right
  have hq0 : q ≠ 0 := hqsf.ne_zero
  have hq1 : q ≠ 1 := by
    intro h
    subst q
    exact hcomp (by simpa using hp)
  have hq : 1 < q := by omega
  have hqprime : q.Prime := by
    by_contra h
    exact hc (zetaRoughSquarefreeCoefficient_large_prime_composite_zero S hS hp hDp hq hqD hqsf h)
  have hrough : ¬∃ a ∈ S, a ∣ p * q := by
    intro h
    exact hc (by simp [zetaRoughSquarefreeCoefficient, h])
  refine Or.inr ⟨p, q, hp, hqprime, hqD, hDp, rfl, ?_⟩
  rw [zetaRoughSquarefreeCoefficient_large_prime_squarefree_cofactor S hS hp hDp hq hqD hqsf hrough,
    if_pos hqprime]

/-- Squarefreeness gives coprime squarefree factors in the balanced arm,
so no overlap is discarded when moving to a two-factor representation. -/
theorem zetaBalancedFactorization_squarefree {D n : ℕ} (hn : Squarefree n)
    (hbal : zetaBalancedFactorization D n) :
    ∃ a b : ℕ, D < a ∧ D < b ∧ n = a * b ∧ Squarefree a ∧ Squarefree b ∧ a.Coprime b := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hbal
  exact ⟨a, b, ha, hb, rfl, hn.of_mul_left, hn.of_mul_right, Nat.coprime_of_squarefree_mul hn⟩

end
end RiemannGaussian
