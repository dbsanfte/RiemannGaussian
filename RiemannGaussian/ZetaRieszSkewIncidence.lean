/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSkewAllocation
import RiemannGaussian.ZetaRieszWideOwnerObstruction

/-!
# The literal second-largest-prime skew incidence

All integer, reflected-large, allocation and order masks are retained.
The two large prime legs are separated by an exact factorial identity;
the composite cofactor is never completed. There is at most one selected
second-largest-prime incidence at each integer, with no pair averaging.
-/

namespace RiemannGaussian.ZetaRieszSkewAllocation
noncomputable section
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszWideOwnerAudit ZetaRieszPrimeEndpoint
open ZetaRieszTypeII ZetaRieszAnnulusJoint ZetaRieszPrimePairConvolution

/-- The remaining prime in the actual marked largest/second-largest pair. -/
def smallPrime (n q : ℕ) : ℕ := n / (largestPrime n * q)

/-- The literal rank-two incidences: exactly two reflected-large primes,
the smaller one distinguished, and the third prime strictly smaller still. -/
def secondIncidences (u : ℝ) (N n : ℕ) : Finset ℕ :=
  (n.primeFactors.erase (largestPrime n)).filter (fun q =>
    q ∈ intermediatePrimes u N ∧ (smallPrime n q).Prime ∧ smallPrime n q < q ∧
      ReflectedOuterPair (SquarefreeVaughanLogSource.length u N) n (largestPrime n, q))

/-- Exact quotient factorizations on the selected incidence. -/
theorem second_factorization {u : ℝ} {N n q : ℕ} (hn : Squarefree n)
    (hq : q ∈ secondIncidences u N n) :
    n / largestPrime n = q * smallPrime n q ∧ n / q = largestPrime n * smallPrime n q := by
  have hpq := (Finset.mem_filter.mp hq).2.2.2.2
  obtain ⟨hp, hqp, _, he, _, _⟩ := primePair_data hn hpq.1
  dsimp only [Prod.fst, Prod.snd] at hp hqp he
  change largestPrime n * (q * smallPrime n q) = n at he
  constructor
  · calc
      n / largestPrime n = (largestPrime n * (q * smallPrime n q)) / largestPrime n :=
        congrArg (fun a => a / largestPrime n) he.symm
      _ = _ := Nat.mul_div_cancel_left _ hp.pos
  · calc
      n / q = (largestPrime n * (q * smallPrime n q)) / q :=
        congrArg (fun a => a / q) he.symm
      _ = (q * (largestPrime n * smallPrime n q)) / q := by congr 1; ring
      _ = _ := Nat.mul_div_cancel_left _ hqp.pos

/-- Strict ordering makes the second incidence unique, rather than an
average of the three equal pair discrepancies. -/
theorem secondIncidences_card_le_one {u : ℝ} {N n : ℕ} (hn : Squarefree n) :
    (secondIncidences u N n).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro q hq t ht
  have hq' := (Finset.mem_filter.mp hq).2
  have ht' := (Finset.mem_filter.mp ht).2
  have hqp := Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp (Finset.mem_filter.mp hq).1).2
  have htp := Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp (Finset.mem_filter.mp ht).1).2
  have he := (second_factorization hn hq).1.symm.trans (second_factorization hn ht).1
  rcases (prime_mul_eq_iff hqp htp ht'.2.1).mp he with h | h
  · exact h.1
  · have hqs := hq'.2.2.1
    have hts := ht'.2.2.1
    omega

/-- The reflected coefficient on this exact support is log r. -/
theorem second_neg_riesz {u : ℝ} {N n q : ℕ} (hn : Squarefree n)
    (hc : n.primeFactors.card = 3) (hq : q ∈ secondIncidences u N n) :
    -VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N) n =
      Real.log (smallPrime n q) := by
  have hs := (Finset.mem_filter.mp hq).2
  have hpair := hs.2.2.2
  obtain ⟨hp, hqp, hpq, he, hpr, hqr⟩ := primePair_data hn hpair.1
  obtain ⟨hLp, hLq, hsmall⟩ := reflectedOuterPair_data hn (by omega) hpair
  have hr := hs.2.1
  dsimp only [Prod.fst, Prod.snd] at hp hqp hpq he hpr hqr hLp hLq hsmall
  change largestPrime n * (q * smallPrime n q) = n at he
  have hsmall' : ∀ r ∈ (smallPrime n q).primeFactors,
      Real.log r < Real.log (largestPrime n * (q * smallPrime n q) : ℕ) -
        SquarefreeVaughanLogSource.length u N := by
    rw [he]
    exact hsmall
  have hv := prime_cofactor_boundary_pos hp hqp hr _ hsmall'
  have hd := pairDiscrepancy_eq_neg_riesz (a := smallPrime n q)
    (SquarefreeVaughanLogSource.length u N) hp hqp hpq hpr hqr
  rw [he] at hd
  exact hd.symm.trans ((pairDiscrepancy_positive_boundary hp hqp hr.one_lt _ hLp hLq hv.le).trans
    (ArithmeticFunction.vonMangoldt_apply_prime hr))

/-- The requested concrete quarter-gap factorial box, with h+1 on r.
The cofactor order remains the original j+h in ownerOrders. -/
def skewOrders (N j : ℕ) : Finset ℕ :=
  (Finset.range (N + 1 - j + 1)).filter (fun h =>
    j + h ∈ ownerOrders N ∧ 25 * (h + 1) ≤ N ∧
      N + 4 * (N + 1 - j - h) ≤ 4 * j)

/-- The small-prime cap and order gap force j>=121N/200, exactly. -/
theorem skew_order_high {N j h : ℕ} (hj : j < N + 2) (hh : h ∈ skewOrders N j) :
    j ∈ highOrders N := by
  obtain ⟨hr, _, hc, hg⟩ := Finset.mem_filter.mp hh
  have hr' := Finset.mem_range.mp hr
  simp only [highOrders, Finset.mem_filter, Finset.mem_range]
  omega

/-- The exact multinomial fraction of the requested order box. The first
argument is the largest prime's complementary share; the second is the
small prime's share inside that complement. -/
def skewMass (N : ℕ) (x c : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 2), mass (N + 1) j (1 - x) *
    ∑ h ∈ skewOrders N j, mass (N + 1 - j) h c

/-- Marginalization retains the large-prime selection; no phase is
changed and no independence of the actual primes is assumed. -/
theorem skewMass_bounds (N : ℕ) {x c : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ skewMass N x c ∧ skewMass N x c ≤ highMass N x := by
  have hm := fun j => mass_nonneg (N + 1) j (by linarith : 0 ≤ 1 - x)
    (by linarith : 1 - x ≤ 1)
  have hi (j : ℕ) : 0 ≤ ∑ h ∈ skewOrders N j, mass (N + 1 - j) h c :=
    Finset.sum_nonneg (fun h _ => mass_nonneg _ _ hc hc1)
  have hb (j : ℕ) : (∑ h ∈ skewOrders N j, mass (N + 1 - j) h c) ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun h _ _ => mass_nonneg _ _ hc hc1)).trans_eq (mass_total _ _)
  refine ⟨Finset.sum_nonneg (fun j _ => mul_nonneg (hm j) (hi j)), ?_⟩
  unfold skewMass highMass highOrders
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hjh : 121 * N ≤ 200 * j
  · rw [if_pos hjh]
    exact mul_le_of_le_one_right (hm j) (hb j)
  · rw [if_neg hjh]
    have he : skewOrders N j = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro h hh
      exact hjh (Finset.mem_filter.mp (skew_order_high (Finset.mem_range.mp hj) hh)).2
    simp [he]

/-- Both logarithmic arguments are literal ratios from the actual
factorization, with their unit-interval domains discharged. -/
theorem second_log_data {u : ℝ} {N n q : ℕ} (hn : Squarefree n)
    (hc : n.primeFactors.card = 3) (hq : q ∈ secondIncidences u N n) :
    0 < Real.log n ∧ 0 < Real.log (n / largestPrime n : ℕ) ∧
      Real.log (n / largestPrime n : ℕ) + Real.log (largestPrime n) = Real.log n ∧
      (0 ≤ Real.log (n / largestPrime n : ℕ) / Real.log n ∧
        Real.log (n / largestPrime n : ℕ) / Real.log n ≤ 1) ∧
      (0 ≤ Real.log (smallPrime n q) / Real.log (n / largestPrime n : ℕ) ∧
        Real.log (smallPrime n q) / Real.log (n / largestPrime n : ℕ) ≤ 1) := by
  have hs := (Finset.mem_filter.mp hq).2
  obtain ⟨hp, hqp, _, he, _, _⟩ := primePair_data hn hs.2.2.2.1
  have hr := hs.2.1
  have hn1 : 1 < n := hp.one_lt.trans_le
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn.ne_zero)
      (Nat.dvd_of_mem_primeFactors (largestPrime_mem_of_three hc)))
  have hlog := Real.log_pos (show (1 : ℝ) < n by exact_mod_cast hn1)
  have hab := (second_factorization hn hq).1
  have hcof : 1 < n / largestPrime n := by rw [hab]; nlinarith [hqp.two_le, hr.two_le]
  have hcoflog := Real.log_pos (show (1 : ℝ) < (n / largestPrime n : ℕ) by exact_mod_cast hcof)
  have hlogs : Real.log (n / largestPrime n : ℕ) + Real.log (largestPrime n) = Real.log n := by
    rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors (largestPrime_mem_of_three hc))
      (by exact_mod_cast hp.ne_zero), Real.log_div (by exact_mod_cast hn.ne_zero)
        (by exact_mod_cast hp.ne_zero)]
    ring
  have hrle : smallPrime n q ≤ n / largestPrime n := by rw [hab]; nlinarith [hqp.two_le]
  refine ⟨hlog, hcoflog, hlogs, ⟨div_nonneg hcoflog.le hlog.le, ?_⟩,
    ⟨div_nonneg (Real.log_natCast_nonneg _) hcoflog.le, ?_⟩⟩
  · apply (div_le_one hlog).mpr
    linarith [Real.log_natCast_nonneg (largestPrime n)]
  · apply (div_le_one hcoflog).mpr
    exact Real.log_le_log (by exact_mod_cast hr.pos)
      (by exact_mod_cast hrle)

/-- The actual skew atom keeps the full old allocation and complex phase. -/
def skewAtom (u y : ℝ) (N n q : ℕ) : ℂ :=
  (skewMass N (Real.log (n / largestPrime n : ℕ) / Real.log n)
    (Real.log (smallPrime n q) / Real.log (n / largestPrime n : ℕ)) : ℂ) *
      (residualCoefficient (intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) N n *
          zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n)

/-- The literal quarter-gap rank-two subfamily of the original correction.
It uses the original narrow/nondominant/count masks and no incidence average. -/
def skewResponse (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ tripleBand u N K, ∑ q ∈ secondIncidences u N n, skewAtom u y N n q

/-- Exact factorial convolution on the cofactor, with the extra logarithm
kept on r. In particular there is no completed composite series here. -/
theorem log_kernel_convolution (k p r : ℕ) (hp : 0 < p) (hr : 0 < r) (s : ℂ) :
    (Real.log r : ℂ) * zetaPrimeLogKernel k s (p * r) =
      ∑ j ∈ Finset.range (k + 1), ((k - j + 1 : ℕ) : ℂ) *
        zetaPrimeLogKernel j s p * zetaPrimeLogKernel (k - j + 1) s r := by
  rw [ZetaPrimeCofactorCompletion.logKernel_product k s hp hr]
  simp only [Finset.mul_sum, zetaPrimeLogKernel]
  apply Finset.sum_congr rfl
  intro j _
  have h := ZetaRieszHeadOrders.log_mul_kernel (k - j) r s
  dsimp only [zetaPrimeLogKernel] at h
  linear_combination (Real.log p : ℂ) ^ j / (j.factorial : ℂ) * zetaPrimeFeature s p * h

end
end RiemannGaussian.ZetaRieszSkewAllocation
