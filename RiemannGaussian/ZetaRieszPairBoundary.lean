/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszTypeIIReduction

/-!
# The literal ordered-pair discrepancy at its cutoff boundary

The saturation conditions are retained explicitly. On the side where
log(pq)>L, the discrepancy is exactly the prime-cofactor von Mangoldt
term. If all cofactor primes are below the reflected threshold, the other
side cannot have a prime cofactor. In its innermost boundary layer the
complete truncated response is exactly its unit-divisor term, regardless
of prime count. These statements do not estimate the weighted carrier.
-/

namespace RiemannGaussian.ZetaRieszTypeII
noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius

/-- The signed boundary coordinate of the marked outer pair, at the
original full integer and logarithmic Riesz cutoff. -/
def pairBoundary (L : ℝ) (p q a : ℕ) : ℝ :=
  (Real.log (p * q : ℕ) - L) / Real.log (p * (q * a) : ℕ)

/-- The requested exactly-two-large sector uses the reflected threshold
log n-L. It does not substitute the separate quadratic prime cutoff. -/
def ReflectedOuterPair (L : ℝ) (n : ℕ) (pq : ℕ × ℕ) : Prop :=
  pq ∈ primePairs n ∧
    n.primeFactors.filter (fun r : ℕ => Real.log n - L ≤ Real.log r) = ({pq.1, pq.2} : Finset ℕ)

/-- The full product logarithm retains both marked primes and the cofactor. -/
theorem pair_log (p q a : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) (ha : a ≠ 0) :
    Real.log (p * (q * a) : ℕ) = Real.log p + Real.log q + Real.log a := by
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hp : (p : ℝ) ≠ 0)
    (by exact_mod_cast mul_ne_zero hq ha : ((q * a : ℕ) : ℝ) ≠ 0),
    Nat.cast_mul, Real.log_mul (by exact_mod_cast hq : (q : ℝ) ≠ 0) (by exact_mod_cast ha : (a : ℝ) ≠ 0)]
  ring

/-- The literal exactly-two-large support supplies both saturation
inequalities and the strict reflected cutoff on every cofactor prime. -/
theorem reflectedOuterPair_data {L : ℝ} {n : ℕ} (hn : Squarefree n)
    (hc : 3 ≤ n.primeFactors.card) {pq : ℕ × ℕ} (hpair : ReflectedOuterPair L n pq) :
    let a := n / (pq.1 * pq.2)
    Real.log a ≤ L - Real.log pq.1 ∧ Real.log a ≤ L - Real.log pq.2 ∧
      ∀ r ∈ a.primeFactors, Real.log r < Real.log n - L := by
  obtain ⟨hp, hq, _, he, hpa, hqa⟩ := primePair_data hn hpair.1
  obtain ⟨ha, ha1, _, _⟩ := primePair_cofactor hn hc hpair.1
  have hl : Real.log n = Real.log pq.1 + Real.log pq.2 + Real.log (n / (pq.1 * pq.2) : ℕ) := by
    conv_lhs => rw [← he]
    exact pair_log _ _ _ hp.ne_zero hq.ne_zero ha.ne_zero
  have hpL : Real.log n - L ≤ Real.log pq.1 := by
    apply (Finset.mem_filter.mp (show pq.1 ∈ n.primeFactors.filter
      (fun r : ℕ => Real.log n - L ≤ Real.log r) by rw [hpair.2]; simp)).2
  have hqL : Real.log n - L ≤ Real.log pq.2 := by
    apply (Finset.mem_filter.mp (show pq.2 ∈ n.primeFactors.filter
      (fun r : ℕ => Real.log n - L ≤ Real.log r) by rw [hpair.2]; simp)).2
  refine ⟨by linarith, by linarith, ?_⟩
  intro r hr
  have hd : n / (pq.1 * pq.2) ∣ n := by
    conv_rhs => rw [← he]
    exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
  have hrn := Nat.primeFactors_mono hd hn.ne_zero hr
  by_contra hh
  have hmem : r ∈ ({pq.1, pq.2} : Finset ℕ) := by
    rw [← hpair.2]
    exact Finset.mem_filter.mpr ⟨hrn, le_of_not_gt hh⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · have hdvd := Nat.dvd_of_mem_primeFactors hr
    rw [h] at hdvd
    exact hpa hdvd
  · have hdvd := Nat.dvd_of_mem_primeFactors hr
    rw [h] at hdvd
    exact hqa hdvd

/-- The boundary coordinate gives precisely the original fourth cutoff;
there is no logarithmic approximation or shifted order. -/
theorem boundary_cutoff {p q a : ℕ} (hp : p.Prime) (hq : q.Prime) (ha : 1 < a) (L : ℝ) :
    -pairBoundary L p q a * Real.log (p * (q * a) : ℕ) = L - Real.log p - Real.log q := by
  have hn : (1 : ℝ) < (p * (q * a) : ℕ) := by
    have h := Nat.mul_le_mul hp.two_le (Nat.mul_le_mul hq.two_le (show 2 ≤ a by omega))
    exact_mod_cast (show 1 < p * (q * a) by omega)
  have hlog : Real.log (p * (q * a) : ℕ) ≠ 0 := (Real.log_pos hn).ne'
  unfold pairBoundary
  rw [neg_mul, div_mul_cancel₀ _ hlog, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
  ring

/-- Complete saturation removes the correction exactly, without a bound
for an unsaturated error being implicitly assumed. -/
theorem saturationCorrection_eq_zero {a : ℕ} (ha : a ≠ 0) (ha1 : a ≠ 1)
    (L : ℝ) (p q : ℕ) (hp : Real.log a ≤ L - Real.log p)
    (hq : Real.log a ≤ L - Real.log q) : saturationCorrection L p q a = 0 := by
  have hL : Real.log a ≤ L := by linarith [Real.log_natCast_nonneg p]
  rw [saturationCorrection, riesz_eq_vonMangoldt_of_saturated ha ha1 hp,
    riesz_eq_vonMangoldt_of_saturated ha ha1 hq, riesz_eq_vonMangoldt_of_saturated ha ha1 hL]
  ring

/-- The boundary formula for every pair retains the complete saturation
correction, before a saturated sector is selected. -/
theorem pairDiscrepancy_boundary {p q a : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ha : 1 < a) (L : ℝ) :
    pairDiscrepancy L p q a = ArithmeticFunction.vonMangoldt a -
      VaughanLogAverage.riesz (-pairBoundary L p q a * Real.log (p * (q * a) : ℕ)) a +
        saturationCorrection L p q a := by
  rw [boundary_cutoff hp hq ha]
  rfl

/-- On the positive side only the von Mangoldt prime-cofactor term
survives, provided the other three cutoffs are genuinely saturated. -/
theorem pairDiscrepancy_positive_boundary {p q a : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ha : 1 < a) (L : ℝ) (hLp : Real.log a ≤ L - Real.log p)
    (hLq : Real.log a ≤ L - Real.log q) (hv : 0 ≤ pairBoundary L p q a) :
    pairDiscrepancy L p q a = ArithmeticFunction.vonMangoldt a := by
  rw [pairDiscrepancy_boundary hp hq ha, saturationCorrection_eq_zero
    (by omega : a ≠ 0) (by omega : a ≠ 1) L p q hLp hLq,
    ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hv) (Real.log_natCast_nonneg _)),
    sub_zero, add_zero]

/-- If every cofactor prime is below the reflected saturation threshold,
a prime cofactor forces the outer pair onto the strictly positive side. -/
theorem prime_cofactor_boundary_pos {p q a : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ha : a.Prime) (L : ℝ)
    (hsmall : ∀ r ∈ a.primeFactors,
      Real.log r < Real.log (p * (q * a) : ℕ) - L) :
    0 < pairBoundary L p q a := by
  have hs := hsmall a (by rw [ha.primeFactors]; simp)
  rw [pair_log p q a hp.ne_zero hq.ne_zero ha.ne_zero] at hs
  have hn : (1 : ℝ) < (p * (q * a) : ℕ) := by
    have h := Nat.mul_le_mul hp.two_le (Nat.mul_le_mul hq.two_le ha.two_le)
    exact_mod_cast (show 1 < p * (q * a) by omega)
  apply div_pos _ (Real.log_pos hn)
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
  linarith

/-- On the nonpositive side of an exactly-two-reflected-large pair,
the squarefree cofactor is composite and the discrepancy is the negative
truncated response. The full correction is separately and exactly paid. -/
theorem pairDiscrepancy_negative_boundary {p q a : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ha : Squarefree a) (ha1 : 1 < a) (L : ℝ)
    (hLp : Real.log a ≤ L - Real.log p) (hLq : Real.log a ≤ L - Real.log q)
    (hsmall : ∀ r ∈ a.primeFactors,
      Real.log r < Real.log (p * (q * a) : ℕ) - L)
    (hv : pairBoundary L p q a ≤ 0) :
    pairDiscrepancy L p q a =
      -VaughanLogAverage.riesz (-pairBoundary L p q a * Real.log (p * (q * a) : ℕ)) a := by
  have hnp : ¬a.Prime := fun h => (prime_cofactor_boundary_pos hp hq h L hsmall).not_ge hv
  have hLambda : ArithmeticFunction.vonMangoldt a = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (fun h =>
      hnp (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨ha, h⟩))
  rw [pairDiscrepancy_boundary hp hq ha1, hLambda,
    saturationCorrection_eq_zero ha.ne_zero (by omega) L p q hLp hLq, zero_sub, add_zero]

/-- The complete boundary split on the literal exactly-two-large support.
Saturation and the prime-cofactor restriction follow from that support,
rather than being additional analytic assumptions. -/
theorem reflectedOuterPair_discrepancy {L : ℝ} {n : ℕ} (hn : Squarefree n)
    (hc : 3 ≤ n.primeFactors.card) {pq : ℕ × ℕ} (hpair : ReflectedOuterPair L n pq) :
    let a := n / (pq.1 * pq.2)
    let v := pairBoundary L pq.1 pq.2 a
    pairDiscrepancy L pq.1 pq.2 a =
      if 0 ≤ v then ArithmeticFunction.vonMangoldt a
      else -VaughanLogAverage.riesz (-v * Real.log n) a := by
  obtain ⟨hp, hq, _, he, _, _⟩ := primePair_data hn hpair.1
  obtain ⟨ha, ha1, _, _⟩ := primePair_cofactor hn hc hpair.1
  obtain ⟨hLp, hLq, hsmall⟩ := reflectedOuterPair_data hn hc hpair
  dsimp only
  split_ifs with hv
  · exact pairDiscrepancy_positive_boundary hp hq ha1 L hLp hLq hv
  · have hs : ∀ r ∈ (n / (pq.1 * pq.2)).primeFactors,
        Real.log r < Real.log (pq.1 * (pq.2 * (n / (pq.1 * pq.2))) : ℕ) - L := by
      simpa only [he] using hsmall
    simpa only [he] using
      pairDiscrepancy_negative_boundary hp hq ha ha1 L hLp hLq hs (le_of_not_ge hv)

/-- Before the first nonunit divisor enters, the entire finite Riesz
response is exactly the unit-divisor hinge, for every prime count. -/
theorem riesz_eq_cutoff_below_minFac {a : ℕ} (ha : a ≠ 0) {z : ℝ}
    (hz : 0 ≤ z) (hzp : z ≤ Real.log a.minFac) :
    VaughanLogAverage.riesz z a = z := by
  have h1 : 1 ∈ a.divisors := Nat.mem_divisors.mpr ⟨one_dvd _, ha⟩
  have hs : (∑ d ∈ a.divisors, (μ d : ℝ) * max 0 (z - Real.log d)) =
      (μ (1 : ℕ) : ℝ) * max 0 (z - Real.log ((1 : ℕ) : ℝ)) := by
    apply Finset.sum_eq_single_of_mem 1 h1
    intro d hd hd1
    have hd2 : 2 ≤ d := by have := Nat.pos_of_mem_divisors hd; omega
    have hm := Nat.minFac_le_of_dvd hd2 (Nat.dvd_of_mem_divisors hd)
    have hl := Real.log_le_log (by exact_mod_cast Nat.minFac_pos a : (0 : ℝ) < a.minFac)
      (show (a.minFac : ℝ) ≤ d by exact_mod_cast hm)
    rw [max_eq_left (by linarith), mul_zero]
  simpa only [VaughanLogAverage.riesz, ArithmeticFunction.moebius_apply_one,
    Int.cast_one, Nat.cast_one, Real.log_one, sub_zero, max_eq_right hz, one_mul] using hs

/-- The innermost negative boundary layer has an evaluated discrepancy:
all composite prime-count classes have exactly the same linear response. -/
theorem pairDiscrepancy_inner_boundary {p q a : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ha : Squarefree a) (ha1 : 1 < a) (L : ℝ)
    (hLp : Real.log a ≤ L - Real.log p) (hLq : Real.log a ≤ L - Real.log q)
    (hsmall : ∀ r ∈ a.primeFactors,
      Real.log r < Real.log (p * (q * a) : ℕ) - L)
    (hv : pairBoundary L p q a ≤ 0)
    (hz : -pairBoundary L p q a * Real.log (p * (q * a) : ℕ) ≤ Real.log a.minFac) :
    pairDiscrepancy L p q a = pairBoundary L p q a * Real.log (p * (q * a) : ℕ) := by
  rw [pairDiscrepancy_negative_boundary hp hq ha ha1 L hLp hLq hsmall hv,
    riesz_eq_cutoff_below_minFac ha.ne_zero
      (mul_nonneg (neg_nonneg.mpr hv) (Real.log_natCast_nonneg _)) hz]
  ring

end
end RiemannGaussian.ZetaRieszTypeII
