/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszWholeWindow

/-!
# The absent unit-divisor window on actual higher-prime support

The exact arithmetic signs, complex amplitudes and physical cutoffs remain
available alongside their finite energy bounds. No source-scale decay of
the complete signed energy or new zero-free region is asserted.
-/

namespace RiemannGaussian.ZetaRieszWindowUnitDeletion
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate Classical
open ZetaRieszWholeWindow
/-- With four or more distinct prime factors, the two smallest
prime logs occupy at most half the total logarithm. -/
theorem two_smallest_logs_le_half {n p q m : ℕ} (h : smallestPairFactorization n p q m)
    (hk : 4 ≤ n.primeFactors.card) :
    2 * (Real.log p + Real.log q) ≤ Real.log n := by
  obtain ⟨hp, hq, _, he, hm, _, _, hpmin, hqmin, hcard⟩ := h
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm.ne_zero
  have hn0 : n ≠ 0 := by rw [he]; exact mul_ne_zero hp.ne_zero (mul_ne_zero hq.ne_zero hm.ne_zero)
  have hqn : q ∣ n := by rw [he]; exact dvd_mul_of_dvd_right (dvd_mul_right q m) p
  have hpq : p ≤ q := hpmin q (hq.mem_primeFactors hqn hn0)
  have hlogpq : Real.log p ≤ Real.log q :=
    Real.log_le_log hp0 (by exact_mod_cast hpq)
  have hlogq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hmcount : (2 : ℝ) ≤ m.primeFactors.card := by
    exact_mod_cast (show 2 ≤ m.primeFactors.card by omega)
  have hsum : (∑ _r ∈ m.primeFactors, Real.log q) ≤ ∑ r ∈ m.primeFactors, Real.log r := by
    apply Finset.sum_le_sum
    intro r hr
    exact Real.log_le_log hq0 (by exact_mod_cast hqmin r hr)
  rw [Finset.sum_const, nsmul_eq_mul, ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hm] at hsum
  have hlogm : 2 * Real.log q ≤ Real.log m :=
    (mul_le_mul_of_nonneg_right hmcount hlogq).trans hsum
  have hlog : Real.log n = Real.log p + Real.log q + Real.log m := by
    rw [he]
    simp only [Nat.cast_mul]
    rw [Real.log_mul hp0.ne' (mul_pos hq0 hm0).ne', Real.log_mul hq0.ne' hm0.ne']
    ring
  linarith

/-- When the two selected primes lie below the physical cutoff,
the unit divisor's entire scaled window is absent from the actual integral. -/
theorem unit_primeWindowAtom_eq_zero (L : ℝ) (p q : ℕ → ℕ) (n : ℕ)
    (hp : (p n).Prime) (hL : Real.log (p n) + Real.log (q n) ≤ L)
    {v : ℝ} (hv : v ∈ Ioo 0 1) :
    intervalAtom (primeWindowLower L p q ⟨n, 1⟩) (primeWindowUpper L p ⟨n, 1⟩) v = 0 := by
  have ha : 0 < Real.log (p n) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlo : 1 ≤ (L - Real.log (q n)) / Real.log (p n) :=
    (le_div_iff₀ ha).mpr (by linarith)
  have hnot : ¬ ((L - Real.log (q n)) / Real.log (p n) < v ∧ v < L / Real.log (p n)) := by
    intro h
    linarith [hv.2, h.1]
  simp only [primeWindowLower, primeWindowUpper, Nat.cast_one, Real.log_one, sub_zero,
    intervalAtom, indicator_apply, mem_Ioo, if_neg hnot]

/-- The unit divisor is independently absent for every actual central
atom with at least four prime factors. Prime selection, ordering and the
physical cutoff condition are all discharged from the original support. -/
theorem exists_central_higher_unit_window_zero {u : ℝ} {N n : ℕ}
    (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hn : n ∈ ZetaRieszCentralPrimeLayers.centralUnpairedBand u N)
    (hc : SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n ≠ 0)
    (hk : 4 ≤ n.primeFactors.card) :
    ∃ p q m : ℕ, smallestPairFactorization n p q m ∧
      Real.log p + Real.log q < SquarefreeVaughanLogSource.length u N ∧
      ∀ v ∈ Ioo 0 1,
        intervalAtom ((SquarefreeVaughanLogSource.length u N - Real.log q) / Real.log p)
          (SquarefreeVaughanLogSource.length u N / Real.log p) v = 0 := by
  obtain ⟨hs, hs2⟩ := ZetaRieszSperner.coefficient_ne_zero_support hc
  obtain ⟨p, q, m, h⟩ := ZetaRieszSperner.exists_two_smallest_factorization hs hs2
  have hp : p.Prime := h.1
  have hh := two_smallest_logs_le_half h hk
  have hnlog := ZetaRieszCentralPrimeLayers.log_lt_twice_length_of_mem_annulus huh
    (ZetaRieszCentralPrimeLayers.centralUnpairedBand_subset_annulus u N hn)
  have hL : Real.log p + Real.log q < SquarefreeVaughanLogSource.length u N := by linarith
  refine ⟨p, q, m, h, hL, ?_⟩
  intro v hv
  simpa only [primeWindowLower, primeWindowUpper, Nat.cast_one, Real.log_one, sub_zero] using
    unit_primeWindowAtom_eq_zero (SquarefreeVaughanLogSource.length u N)
      (fun _ => p) (fun _ => q) n hp hL.le hv

/-- The same complete prime-pair lift with just the unit-divisor
columns removed. Original integer labels and cross-family phases remain. -/
def primeWindowLiftWithoutUnit (S : Finset ℕ) (p q m : ℕ → ℕ) (L : ℝ)
    (P : Polynomial ℂ) (N : ℕ) (t v : ℝ) : ℂ :=
  intervalLift (S.sigma (fun n => (m n).divisors.erase 1))
    (primeWindowCoefficient L P N t p) (primeWindowLower L p q) (primeWindowUpper L p) v

/-- The actual entire lift is unchanged on the integration domain
when the geometrically absent unit columns are deleted together. -/
theorem primeWindowLift_eq_withoutUnit (S : Finset ℕ) (p q m : ℕ → ℕ) (L : ℝ)
    (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (hS : ∀ n ∈ S, (p n).Prime ∧ Real.log (p n) + Real.log (q n) ≤ L)
    {v : ℝ} (hv : v ∈ Ioo 0 1) :
    primeWindowLift S p q m L P N t v = primeWindowLiftWithoutUnit S p q m L P N t v := by
  simp only [primeWindowLift, primeWindowLiftWithoutUnit, intervalLift, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro n hn
  symm
  apply Finset.sum_subset (Finset.erase_subset _ _)
  intro d hd hnot
  have hd1 : d = 1 := by
    by_contra h
    exact hnot (Finset.mem_erase.mpr ⟨h, hd⟩)
  subst d
  rw [unit_primeWindowAtom_eq_zero L p q n (hS n hn).1 (hS n hn).2 hv, mul_zero]

end
end RiemannGaussian.ZetaRieszWindowUnitDeletion
