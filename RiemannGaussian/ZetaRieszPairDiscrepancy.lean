/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszTypeIILocalization
import RiemannGaussian.ZetaRieszFixedCofactor

/-!
# The actual prime-versus-truncated-sieve discrepancy

The two-prime identity simplifies to Lambda minus a single hinge only when
the other three cutoffs are saturated. The full correction is retained here.
Ordered distinct prime pairs are averaged, so a label is counted exactly once.
These identities supply the literal sum in the quantitative Type-II test;
they are not estimates for that sum.
-/

namespace RiemannGaussian.ZetaRieszTypeII
noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
open ZetaSquarefreeRieszWindows ZetaRieszJointAllocation

/-- The unsaturated three-cutoff correction to the proposed prime discrepancy. -/
def saturationCorrection (L : ℝ) (p q a : ℕ) : ℝ :=
  VaughanLogAverage.riesz (L - Real.log p) a +
    VaughanLogAverage.riesz (L - Real.log q) a -
      VaughanLogAverage.riesz L a - ArithmeticFunction.vonMangoldt a

/-- The full signed discrepancy. The correction is part of the Type-II input,
not an implicitly paid error term. -/
def pairDiscrepancy (L : ℝ) (p q a : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt a -
    VaughanLogAverage.riesz (L - Real.log p - Real.log q) a +
      saturationCorrection L p q a

/-- Two prime insertions identify the exact discrepancy on every admissible cofactor. -/
theorem pairDiscrepancy_eq_neg_riesz (L : ℝ) {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpa : ¬p ∣ a) (hqa : ¬q ∣ a) :
    pairDiscrepancy L p q a = -VaughanLogAverage.riesz L (p * (q * a)) := by
  have hpqa : ¬p ∣ q * a := by
    intro h
    rcases hp.dvd_mul.mp h with h | h
    · exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
    · exact hpa h
  rw [riesz_prime_mul L hp hpqa, riesz_prime_mul L hq hqa,
    riesz_prime_mul (L - Real.log p) hq hqa]
  simp only [pairDiscrepancy, saturationCorrection]
  ring

/-- Complete saturation gives Lambda, with the nonunit condition explicit. -/
theorem riesz_eq_vonMangoldt_of_saturated {a : ℕ} (ha : a ≠ 0) (ha1 : a ≠ 1)
    {L : ℝ} (hL : Real.log a ≤ L) :
    VaughanLogAverage.riesz L a = ArithmeticFunction.vonMangoldt a := by
  have hm : (∑ d ∈ a.divisors, (μ d : ℝ)) = 0 := by
    exact_mod_cast ZetaRieszPrimeFourier.sum_moebius_eq_zero ha1
  calc
    _ = ∑ d ∈ a.divisors, (μ d : ℝ) * (L - Real.log d) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [max_eq_right]
      exact sub_nonneg.mpr ((Real.log_le_log (by
        exact_mod_cast Nat.pos_of_mem_divisors hd : (0 : ℝ) < d)
        (by exact_mod_cast (Nat.le_of_dvd (Nat.pos_of_ne_zero ha)
          (Nat.dvd_of_mem_divisors hd)))).trans hL)
    _ = _ := by
      have hl := ArithmeticFunction.sum_moebius_mul_log_eq (n := a)
      simp only [ArithmeticFunction.log_apply] at hl
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hm, zero_mul,
        hl, zero_sub, neg_neg]

/-- The advertised prime-versus-sieve formula is valid on the saturated pair class. -/
theorem pairDiscrepancy_of_saturated {a : ℕ} (ha : a ≠ 0) (ha1 : a ≠ 1)
    (L : ℝ) (p q : ℕ)
    (hp : Real.log a ≤ L - Real.log p) (hq : Real.log a ≤ L - Real.log q) :
    pairDiscrepancy L p q a = ArithmeticFunction.vonMangoldt a -
      VaughanLogAverage.riesz (L - Real.log p - Real.log q) a := by
  have hL : Real.log a ≤ L := by linarith [Real.log_natCast_nonneg p]
  simp only [pairDiscrepancy, saturationCorrection,
    riesz_eq_vonMangoldt_of_saturated ha ha1 hp,
    riesz_eq_vonMangoldt_of_saturated ha ha1 hq,
    riesz_eq_vonMangoldt_of_saturated ha ha1 hL]
  ring

/-- The exact existing coefficient, including its sign and cutoff normalization. -/
theorem coefficient_eq_pairDiscrepancy {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpa : ¬p ∣ a) (hqa : ¬q ∣ a) (hn : Squarefree (p * (q * a))) (L : ℝ) :
    SquarefreeVaughanLogSource.coefficient L (p * (q * a)) =
      ((Real.log (p * (q * a) : ℕ) / L * pairDiscrepancy L p q a : ℝ) : ℂ) := by
  have ha : 0 < a := by
    have h := hn.ne_zero
    by_contra hh
    have : a = 0 := by omega
    simp [this] at h
  have hnp : ¬(p * (q * a)).Prime :=
    Nat.not_prime_mul hp.ne_one (by nlinarith [hq.two_le])
  rw [SquarefreeVaughanLogSource.coefficient, if_pos ⟨hn, hnp⟩,
    pairDiscrepancy_eq_neg_riesz L hp hq hpq hpa hqa]
  congr 1
  ring

/-- The proposed short formula, with precisely the saturation hypotheses
needed to remove its correction and the literal log(p*q) cutoff. -/
theorem coefficient_prime_minus_hinge {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpa : ¬p ∣ a) (hqa : ¬q ∣ a) (hn : Squarefree (p * (q * a)))
    (ha : a ≠ 0) (ha1 : a ≠ 1) (L : ℝ)
    (hLp : Real.log a ≤ L - Real.log p) (hLq : Real.log a ≤ L - Real.log q) :
    SquarefreeVaughanLogSource.coefficient L (p * (q * a)) =
      ((Real.log (p * (q * a) : ℕ) / L *
        (ArithmeticFunction.vonMangoldt a -
          VaughanLogAverage.riesz (L - Real.log (p * q : ℕ)) a) : ℝ) : ℂ) := by
  have hl : Real.log (p * q : ℕ) = Real.log p + Real.log q := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
  rw [coefficient_eq_pairDiscrepancy hp hq hpq hpa hqa hn,
    pairDiscrepancy_of_saturated ha ha1 L p q hLp hLq,
    hl, sub_add_eq_sub_sub]

/-- All ordered distinct prime incidences of an integer. -/
def primePairs (n : ℕ) : Finset (ℕ × ℕ) := n.primeFactors.offDiag

/-- Pair multiplicity is omega(n)(omega(n)-1); it must not be omitted. -/
theorem primePairs_card (n : ℕ) :
    (primePairs n).card = n.primeFactors.card * (n.primeFactors.card - 1) := by
  rw [primePairs, Finset.offDiag_card, Nat.mul_sub_left_distrib, mul_one]

/-- Every retained label has at least three distinct prime factors. -/
theorem narrowBand_prime_count {u : ℝ} {N K n : ℕ} (hn : n ∈ narrowBand u N K) :
    3 ≤ n.primeFactors.card := by
  have h := (Finset.mem_filter.mp hn).1
  have h := (Finset.mem_sdiff.mp h).1
  have h := (Finset.mem_sdiff.mp h).1
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.1

/-- Every actual prime pair has a unique squarefree coprime complementary factor. -/
theorem primePair_data {n : ℕ} (hn : Squarefree n) {pq : ℕ × ℕ}
    (hpq : pq ∈ primePairs n) :
    pq.1.Prime ∧ pq.2.Prime ∧ pq.1 ≠ pq.2 ∧
      pq.1 * (pq.2 * (n / (pq.1 * pq.2))) = n ∧
      ¬pq.1 ∣ n / (pq.1 * pq.2) ∧ ¬pq.2 ∣ n / (pq.1 * pq.2) := by
  obtain ⟨hp, hq, hne⟩ := Finset.mem_offDiag.mp hpq
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hcop : pq.1.Coprime pq.2 := hpp.coprime_iff_not_dvd.mpr
    (fun h => hne ((Nat.prime_dvd_prime_iff_eq hpp hqp).mp h))
  have hd : pq.1 * pq.2 ∣ n := hcop.mul_dvd_of_dvd_of_dvd
    (Nat.dvd_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hq)
  have he : pq.1 * (pq.2 * (n / (pq.1 * pq.2))) = n := by
    rw [← mul_assoc, Nat.mul_div_cancel' hd]
  have hs : Squarefree (pq.1 * (pq.2 * (n / (pq.1 * pq.2)))) := by rw [he]; exact hn
  have hs1 := Nat.squarefree_mul_iff.mp hs
  have hs2 := Nat.squarefree_mul_iff.mp hs1.2.2
  exact ⟨hpp, hqp, hne, he,
    fun h => (hpp.coprime_iff_not_dvd.mp hs1.1) (dvd_mul_of_dvd_right h _),
    hqp.coprime_iff_not_dvd.mp hs2.1⟩

/-- Cofactors in the actual incidence form are squarefree nonunits and
coprime to both marked primes; no unit or repeated-prime boundary is hidden. -/
theorem primePair_cofactor {n : ℕ} (hn : Squarefree n) (hc : 3 ≤ n.primeFactors.card)
    {pq : ℕ × ℕ} (hpq : pq ∈ primePairs n) :
    Squarefree (n / (pq.1 * pq.2)) ∧ 1 < n / (pq.1 * pq.2) ∧
      pq.1.Coprime (n / (pq.1 * pq.2)) ∧ pq.2.Coprime (n / (pq.1 * pq.2)) := by
  obtain ⟨hp, hq, _, he, hpa, hqa⟩ := primePair_data hn hpq
  have hsf : Squarefree (pq.1 * (pq.2 * (n / (pq.1 * pq.2)))) := by rw [he]; exact hn
  have ha := (Nat.squarefree_mul_iff.mp (Nat.squarefree_mul_iff.mp hsf).2.2).2.2
  refine ⟨ha, ?_, hp.coprime_iff_not_dvd.mpr hpa, hq.coprime_iff_not_dvd.mpr hqa⟩
  have ha1 : n / (pq.1 * pq.2) ≠ 1 := by
    intro h
    rw [h, mul_one] at he
    have htwo := ZetaRieszMaskSupport.pair_prime_count_le_two hp hq
    rw [he] at htwo
    omega
  exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ha.ne_zero, ha1⟩

/-- The literal finite trilinear incidence form. Its variables satisfy
n=p*q*a, distinct primality and coprimality by `primePair_data`. The outer
set carries every original mask. The weight includes the full allocation;
`kernel` will be the exact bounded normalization of the factorial phase. -/
def pairForm (u : ℝ) (N : ℕ) (S : Finset ℕ) (kernel : ℕ → ℂ) : ℂ :=
  ∑ n ∈ S.filter Squarefree, ∑ pq ∈ primePairs n,
    ((1 - boundedShare (ZetaRieszAnnulusJoint.intermediatePrimes u N) N n : ℝ) : ℂ) *
      ((Real.log n / SquarefreeVaughanLogSource.length u N *
        pairDiscrepancy (SquarefreeVaughanLogSource.length u N) pq.1 pq.2
          (n / (pq.1 * pq.2)) : ℝ) : ℂ) * kernel n / ((primePairs n).card : ℂ)

/-- Incidence averaging reconstructs exactly the surviving signed sum, with
no off-mask, cutoff or repeated-prime error. -/
theorem pairForm_eq_sum (u : ℝ) (N : ℕ) (S : Finset ℕ) (kernel : ℕ → ℂ)
    (hS : ∀ n ∈ S, 3 ≤ n.primeFactors.card) :
    pairForm u N S kernel = ∑ n ∈ S,
      residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) N n * kernel n := by
  rw [pairForm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hnS
  by_cases hn : Squarefree n
  · rw [if_pos hn]
    have hcard : (primePairs n).card ≠ 0 := by
      rw [primePairs_card]
      have hc := hS n hnS
      exact Nat.mul_ne_zero (by omega) (by omega)
    have hcC : ((primePairs n).card : ℂ) ≠ 0 := by exact_mod_cast hcard
    calc
      _ = ∑ _pq ∈ primePairs n,
          (residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
            (SquarefreeVaughanLogSource.length u N) N n * kernel n) /
              ((primePairs n).card : ℂ) := by
        apply Finset.sum_congr rfl
        intro pq hpq
        obtain ⟨hp, hq, hne, he, hpa, hqa⟩ := primePair_data hn hpq
        have hsf : Squarefree (pq.1 * (pq.2 * (n / (pq.1 * pq.2)))) := by
          rw [he]; exact hn
        have hcoeff := coefficient_eq_pairDiscrepancy hp hq hne hpa hqa hsf
          (SquarefreeVaughanLogSource.length u N)
        rw [he] at hcoeff
        rw [← hcoeff, residualCoefficient]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; field_simp
  · simp [hn, residualCoefficient, SquarefreeVaughanLogSource.coefficient]

/-- If every available prime is below the reflected cutoff, no selected
pair can satisfy the saturation conditions used by the shorter formula. -/
theorem no_saturated_pair_of_small_primes {t L lp lq la : ℝ}
    (ht : t = lp + lq + la) (hp : lp < t - L) :
    ¬la ≤ L - lq := by
  linarith

end
end RiemannGaussian.ZetaRieszTypeII
