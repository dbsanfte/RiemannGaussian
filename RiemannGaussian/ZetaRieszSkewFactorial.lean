/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSkewIncidence

/-!
# Exact three-leg factorial expansion of the rank-two incidence

These are identities of the actual complex kernels. The cofactor p*r is
split into its two literal prime legs, never completed or replaced by a
prime moment. The old unassigned factor remains in every selected atom.
-/

namespace RiemannGaussian.ZetaRieszSkewAllocation
noncomputable section
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszWideOwnerAudit ZetaRieszPrimeEndpoint
open ZetaRieszTypeII ZetaRieszAnnulusJoint ZetaRieszPrimePairConvolution

/-- One binomial mass gives precisely the corresponding factorial
product kernel, including the full complex product phase. -/
theorem split_mass_kernel (M j a b : ℕ) (hj : j ≤ M) (ha : 0 < a) (hb : 0 < b)
    (hab : 1 < a * b) (s : ℂ) :
    (mass M j (Real.log a / Real.log (a * b : ℕ)) : ℂ) *
      zetaPrimeLogKernel M s (a * b) =
        zetaPrimeLogKernel j s a * zetaPrimeLogKernel (M - j) s b := by
  have hl : Real.log a + Real.log b = Real.log (a * b : ℕ) := by
    rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  have hlog : Real.log (a * b : ℕ) ≠ 0 := (Real.log_pos (by exact_mod_cast hab)).ne'
  have hm := mass_as_factorials M j hj (Real.log a) (Real.log b) (by rw [hl]; exact hlog)
  rw [hl] at hm
  rw [hm]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast,
    zetaPrimeLogKernel, CoprimeEulerPhase.feature_mul s ha hb]
  have hlogC : (Real.log (a * b : ℕ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog
  have hf : (M.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp [hlogC, hf]

/-- The literal coefficient on this incidence, before any order selection. -/
theorem second_original_kernel {u : ℝ} {N n q : ℕ} (hn : Squarefree n)
    (hc : n.primeFactors.card = 3) (hq : q ∈ secondIncidences u N n) (y : ℝ) :
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
      zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n =
        (((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
          (Real.log (smallPrime n q) : ℂ) *
            zetaPrimeLogKernel (N + 1) (3 / 2 + Complex.I * y) n := by
  have hnp : ¬n.Prime := by intro h; rw [h.primeFactors, Finset.card_singleton] at hc; omega
  have hr : VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N) n =
      -Real.log (smallPrime n q) := by linarith [second_neg_riesz hn hc hq]
  calc
    _ = ((Real.log (smallPrime n q) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
        ((Real.log n : ℂ) * zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n) := by
      rw [SquarefreeVaughanLogSource.coefficient, if_pos ⟨hn, hnp⟩, hr]
      push_cast
      ring
    _ = _ := by rw [ZetaRieszHeadOrders.log_mul_kernel]; ring

/-- The three literal prime legs. The orders sum to N+2, including
the extra logarithm on the small prime. -/
def factorialAtom (y : ℝ) (N n q j h : ℕ) : ℂ :=
  ((h + 1 : ℕ) : ℂ) * zetaPrimeLogKernel j (3 / 2 + Complex.I * y) (largestPrime n) *
    zetaPrimeLogKernel (N + 1 - j - h) (3 / 2 + Complex.I * y) q *
      zetaPrimeLogKernel (h + 1) (3 / 2 + Complex.I * y) (smallPrime n q)

/-- Every selected order has the requested exact total, including the
successor derivative on the third prime. -/
theorem factorial_orders_sum {N j h : ℕ} (hj : j < N + 2) (hh : h ∈ skewOrders N j) :
    j + (N + 1 - j - h) + h + 1 = N + 2 := by
  have he := Finset.mem_range.mp (Finset.mem_filter.mp hh).1
  omega

/-- Exact multinomial-to-factorial identity on the actual marked triple. -/
theorem second_mass_kernel {u : ℝ} {N n q j h : ℕ} (hn : Squarefree n)
    (hc : n.primeFactors.card = 3) (hq : q ∈ secondIncidences u N n)
    (hj : j ≤ N + 1) (hh : h ≤ N + 1 - j) (y : ℝ) :
    ((mass (N + 1) j (1 - Real.log (n / largestPrime n : ℕ) / Real.log n) *
      mass (N + 1 - j) h (Real.log (smallPrime n q) / Real.log (n / largestPrime n : ℕ)) : ℝ) : ℂ) *
      (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n) =
          (((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
            factorialAtom y N n q j h := by
  have hqs := (Finset.mem_filter.mp hq).2
  obtain ⟨hp, hqp, _, he, _, _⟩ := primePair_data hn hqs.2.2.2.1
  dsimp only [Prod.fst, Prod.snd] at hp hqp he
  change largestPrime n * (q * smallPrime n q) = n at he
  have hr := hqs.2.1
  obtain ⟨hln, hla, hlogs, _, _⟩ := second_log_data hn hc hq
  have hab := (second_factorization hn hq).1
  have hn1 : 1 < n := hp.one_lt.trans_le
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn.ne_zero)
      (Nat.dvd_of_mem_primeFactors (largestPrime_mem_of_three hc)))
  have hcof : 1 < q * smallPrime n q := by nlinarith [hqp.two_le, hr.two_le]
  have hpK := split_mass_kernel (N + 1) j (largestPrime n) (q * smallPrime n q) hj hp.pos
    (Nat.mul_pos hqp.pos hr.pos) (by rw [he]; exact hn1) (3 / 2 + Complex.I * y)
  rw [he, ← hab] at hpK
  have hrK := split_mass_kernel (N + 1 - j) h (smallPrime n q) q hh hr.pos hqp.pos
    (by simpa only [mul_comm] using hcof) (3 / 2 + Complex.I * y)
  rw [mul_comm (smallPrime n q) q, ← hab] at hrK
  have hx : 1 - Real.log (n / largestPrime n : ℕ) / Real.log n =
      Real.log (largestPrime n) / Real.log n := by
    apply (eq_div_iff hln.ne').mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hln.ne']
    linarith
  rw [← hx] at hpK
  rw [second_original_kernel hn hc hq y, Complex.ofReal_mul]
  dsimp only [factorialAtom]
  have hs := ZetaRieszHeadOrders.log_mul_kernel h (smallPrime n q) (3 / 2 + Complex.I * y)
  linear_combination
    (((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ) *
      (Real.log (smallPrime n q) : ℂ) *
      (mass (N + 1 - j) h (Real.log (smallPrime n q) / Real.log (n / largestPrime n : ℕ)) : ℂ)) * hpK +
    (((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ) *
      (Real.log (smallPrime n q) : ℂ) *
      zetaPrimeLogKernel j (3 / 2 + Complex.I * y) (largestPrime n)) * hrK +
    (((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ) *
      zetaPrimeLogKernel j (3 / 2 + Complex.I * y) (largestPrime n) *
      zetaPrimeLogKernel (N + 1 - j - h) (3 / 2 + Complex.I * y) q) * hs

/-- The defined skew atom is exactly the requested three-leg convolution,
with the original unassigned multiplier and the full order box intact. -/
theorem skewAtom_eq_factorials {u : ℝ} {N n q : ℕ} (hn : Squarefree n)
    (hc : n.primeFactors.card = 3) (hq : q ∈ secondIncidences u N n) (y : ℝ) :
    skewAtom u y N n q =
      ((1 - boundedShare (intermediatePrimes u N) N n : ℝ) : ℂ) *
        (((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
          ∑ j ∈ Finset.range (N + 2), ∑ h ∈ skewOrders N j, factorialAtom y N n q j h := by
  simp only [skewAtom, skewMass, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum,
    Finset.sum_mul, residualCoefficient]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro h hh
  have hm := second_mass_kernel (j := j) (h := h) hn hc hq
    (by have := Finset.mem_range.mp hj; omega)
    (by have := Finset.mem_range.mp (Finset.mem_filter.mp hh).1; omega) y
  simp only [Complex.ofReal_mul] at hm
  linear_combination ((1 - boundedShare (intermediatePrimes u N) N n : ℝ) : ℂ) * hm

/-- A nonowner incidence cannot also appear in the subtracted unique-owner
fibre of ownerCompletionCorrection. -/
theorem second_not_owner {u : ℝ} {N K n q : ℕ} (hq : q ∈ secondIncidences u N n) :
    n ∉ (tripleBand u N K).filter (fun m => largestPrime m = q) := by
  have hne := (Finset.mem_erase.mp (Finset.mem_filter.mp hq).1).1
  intro h
  exact hne (Finset.mem_filter.mp h).2.symm

/-- The exact cofactor row that occurs in ownerCompletionCorrection.
Each of its selected three-leg terms has a literal original incidence. -/
theorem second_composite_convolution {u : ℝ} {N n q : ℕ} (hn : Squarefree n)
    (hc : n.primeFactors.card = 3) (hq : q ∈ secondIncidences u N n) (y : ℝ) (k ℓ : ℕ) :
    ZetaRieszJointCofactor.compositeAtom (SquarefreeVaughanLogSource.length u N) y k ℓ q (n / q) =
      ∑ j ∈ Finset.range (k + 1), ((k - j + 1 : ℕ) : ℂ) *
        zetaPrimeLogKernel j (3 / 2 + Complex.I * y) (largestPrime n) *
        zetaPrimeLogKernel ℓ (3 / 2 + Complex.I * y) q *
        zetaPrimeLogKernel (k - j + 1) (3 / 2 + Complex.I * y) (smallPrime n q) := by
  have hqm := (Finset.mem_erase.mp (Finset.mem_filter.mp hq).1).2
  have hel := ZetaRieszDominantAllocation.eligible_of_three_prime_factors hn (by omega) hqm
  have hp := Nat.prime_of_mem_primeFactors (largestPrime_mem_of_three hc)
  have hr := (Finset.mem_filter.mp hq).2.2.1
  have he : q * (n / q) = n := Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hqm)
  have hcoef : -(VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N) n : ℂ) =
      (Real.log (smallPrime n q) : ℂ) := by exact_mod_cast second_neg_riesz hn hc hq
  change Squarefree (n / q) ∧ n / q ≠ 1 ∧ ¬Nat.Prime (n / q) ∧ ¬q ∣ n / q at hel
  rw [ZetaRieszJointCofactor.compositeAtom, if_pos hel, he, hcoef,
    (second_factorization hn hq).2, log_kernel_convolution _ _ _ hp.pos hr.pos,
    Finset.sum_mul]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- Exact finite-incidence partition of the existing completion correction.
The second term is ownership removal with the original unassigned weight.
The first term retains all completion, allocation and off-mask differences;
no estimate for that term is asserted. -/
theorem correction_eq_nonowner_rows (u y : ℝ) (N K : ℕ) :
    ownerCompletionCorrection u y N K =
      (((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
        ∑ k ∈ ownerOrders N, ∑ q ∈ intermediatePrimes u N,
          ((∑' a, ZetaRieszJointCofactor.compositeAtom
            (SquarefreeVaughanLogSource.length u N) y k (N + 1 - k) q a) -
          ∑ n ∈ (tripleBand u N K).filter (fun n => q ∈ n.primeFactors),
            ((1 - boundedShare (intermediatePrimes u N) N n : ℝ) : ℂ) *
              ZetaRieszJointCofactor.compositeAtom
                (SquarefreeVaughanLogSource.length u N) y k (N + 1 - k) q (n / q)) +
      (((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
        ∑ k ∈ ownerOrders N, ∑ q ∈ intermediatePrimes u N,
          ∑ n ∈ ((tripleBand u N K).filter (fun n => q ∈ n.primeFactors)).filter
              (fun n => largestPrime n ≠ q),
            ((1 - boundedShare (intermediatePrimes u N) N n : ℝ) : ℂ) *
              ZetaRieszJointCofactor.compositeAtom
                (SquarefreeVaughanLogSource.length u N) y k (N + 1 - k) q (n / q) := by
  unfold ownerCompletionCorrection
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  have he : ((tripleBand u N K).filter (fun n => q ∈ n.primeFactors)).filter
        (fun n => largestPrime n = q) =
      (tripleBand u N K).filter (fun n => largestPrime n = q) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · intro h
      refine ⟨⟨h.1, ?_⟩, h.2⟩
      rw [← h.2]
      exact largestPrime_mem_of_three (Finset.mem_filter.mp h.1).2.2
  have hs := Finset.sum_filter_add_sum_filter_not
    ((tripleBand u N K).filter (fun n => q ∈ n.primeFactors))
    (fun n => largestPrime n = q)
    (fun n => ((1 - boundedShare (intermediatePrimes u N) N n : ℝ) : ℂ) *
      ZetaRieszJointCofactor.compositeAtom
        (SquarefreeVaughanLogSource.length u N) y k (N + 1 - k) q (n / q))
  rw [he] at hs
  linear_combination -hs

/-- The marked second-prime incidence is actually in the nonowner row
of the exact correction partition, with no incidence averaging. -/
theorem second_mem_nonowner_row {u : ℝ} {N K n q : ℕ}
    (hn : n ∈ tripleBand u N K) (hq : q ∈ secondIncidences u N n) :
    n ∈ ((tripleBand u N K).filter (fun n => q ∈ n.primeFactors)).filter
      (fun n => largestPrime n ≠ q) := by
  obtain ⟨hne, hprime⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp hq).1
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hn, hprime⟩, Ne.symm hne⟩

end
end RiemannGaussian.ZetaRieszSkewAllocation
