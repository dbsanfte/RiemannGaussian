/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszNarrowCarrier

/-!
# Physical-cutoff prime counts in the actual narrowed carrier

Every selected squarefree prime factor spends its logarithm from the same
integer's total log budget. The actual damped floor gives an eventual
linear physical length, so the narrowed support has bounded extreme-prime
degree at every fixed source scale. On u<exp(-1/2), the explicit support
bound is five. These are primes at or above X_N, not all primes above N^2;
intermediate primes may still be numerous and their phases remain coupled.
-/

namespace RiemannGaussian.ZetaRieszExtremePrimeCount
noncomputable section
open Filter Topology
open scoped BigOperators Classical

/-- The exact logarithmic budget for any selected squarefree prime factors.
This counts distinct primes without forgetting their original labels. -/
theorem prime_subset_log_budget {n : ℕ} (hn : Squarefree n) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (L : ℝ) (hL : ∀ p ∈ S, L ≤ Real.log p) :
    (S.card : ℝ) * L ≤ Real.log n := by
  calc
    _ = ∑ p ∈ S, L := by simp
    _ ≤ ∑ p ∈ S, Real.log p := Finset.sum_le_sum hL
    _ ≤ ∑ p ∈ n.primeFactors, Real.log p :=
      Finset.sum_le_sum_of_subset_of_nonneg hS (fun p _ _ => Real.log_natCast_nonneg p)
    _ = _ := (CoprimeEulerPhase.squarefree_log_eq_prime_sum hn).symm

/-- Every admissible exponential base supplies an explicit eventual
linear lower bound for the actual floor-dependent physical length. -/
theorem eventually_length_ge_tilt {u r : ℝ} (hu : 0 < u) (hr : 1 ≤ r) (hur : u * r < 1) :
    ∀ᶠ N : ℕ in atTop, 2 * Real.log r * N ≤ SquarefreeVaughanLogSource.length u N := by
  filter_upwards [ZetaVaughanCutoffBudget.eventually_geometricCutoff_lt_linearDampedCutoff hu hr hur]
    with N hN
  have hfloor : r ^ N < (zetaMoebiusGeometricCutoff r N : ℝ) + 1 := Nat.lt_floor_add_one (r ^ N)
  have hcast : (zetaMoebiusGeometricCutoff r N : ℝ) <
      ZetaVaughanCutoffBudget.linearDampedCutoff u N := by exact_mod_cast hN
  have hle : r ^ N ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N : ℝ) + 2 := by linarith
  have hlog := Real.log_le_log (pow_pos (by linarith : 0 < r) N) hle
  rw [Real.log_pow] at hlog
  rw [SquarefreeVaughanLogSource.length, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith

/-- The actual prime factors at or beyond the common physical cutoff. -/
def extremePrimes (u : ℝ) (N n : ℕ) : Finset ℕ :=
  n.primeFactors.filter (fun p => (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p)

/-- Each extreme prime spends the entire physical logarithmic length
from the same integer's total logarithmic budget. -/
theorem extreme_prime_log_budget (u : ℝ) (N : ℕ) {n : ℕ} (hn : Squarefree n) :
    ((extremePrimes u N n).card : ℝ) * SquarefreeVaughanLogSource.length u N ≤ Real.log n := by
  apply prime_subset_log_budget hn _ (Finset.filter_subset _ _)
  intro p hp
  have hXp := (Finset.mem_filter.mp hp).2
  apply Real.log_le_log (by positivity)
  exact_mod_cast hXp

/-- A linear physical-length lower bound and the narrowed window bound
the number of extreme factors by a fixed real quantity. -/
theorem extreme_prime_count_le {u c : ℝ} {N n : ℕ} (hc : 0 < c) (hN : 0 < N)
    (hL : c * N ≤ SquarefreeVaughanLogSource.length u N)
    (hn : n ∈ ZetaRieszNarrowCarrier.residualBand u N) (hs : Squarefree n) :
    ((extremePrimes u N n).card : ℝ) ≤ (8 * Real.log 2) / c := by
  apply (le_div_iff₀ hc).mpr
  have hm := mul_le_mul_of_nonneg_left hL
    (show (0 : ℝ) ≤ ((extremePrimes u N n).card : ℝ) by positivity)
  have hh := (extreme_prime_log_budget u N hs).trans (ZetaRieszNarrowCarrier.mem_residualBand.mp hn).2.2
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hmul : ((extremePrimes u N n).card : ℝ) * c * N ≤ (8 * Real.log 2) * N := by nlinarith
  exact (mul_le_mul_iff_left₀ hNreal).mp (by simpa only [mul_comm] using hmul)

/-- At every fixed source scale the narrowed actual support has uniformly
bounded extreme-prime count. The bound and starting order can depend on u. -/
theorem exists_eventually_bounded_extreme_count {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∃ K : ℕ, ∀ᶠ N : ℕ in atTop, ∀ n ∈ ZetaRieszNarrowCarrier.residualBand u N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n ≠ 0 →
        (extremePrimes u N n).card ≤ K := by
  obtain ⟨c, hc, hL⟩ := ZetaRieszCompletedCofactor.eventually_linear_length_lower hu hu1
  refine ⟨⌈(8 * Real.log 2) / c⌉₊, ?_⟩
  filter_upwards [hL, eventually_ge_atTop 1] with N hLN hN
  intro n hn hcoeff
  have hs : Squarefree n := by
    by_contra hs
    exact hcoeff (by simp [SquarefreeVaughanLogSource.coefficient, hs])
  have hbound := extreme_prime_count_le hc (by omega) hLN hn hs
  exact_mod_cast hbound.trans (Nat.le_ceil _)

/-- On the complete-composite source interval, the actual physical
length eventually exceeds the moment order itself. -/
theorem eventually_length_ge_order {u : ℝ} (hu : 0 < u)
    (hcontact : u < Real.exp (-(1 / 2 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ≤ SquarefreeVaughanLogSource.length u N := by
  have hr : 1 ≤ Real.exp (1 / 2 : ℝ) := Real.one_le_exp (by norm_num)
  have hur : u * Real.exp (1 / 2 : ℝ) < 1 := by
    calc
      _ < Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 2 : ℝ) :=
        mul_lt_mul_of_pos_right hcontact (Real.exp_pos _)
      _ = 1 := by rw [← Real.exp_add]; norm_num
  have h := eventually_length_ge_tilt hu hr hur
  simpa only [Real.log_exp, mul_one_div_cancel (by norm_num : (2 : ℝ) ≠ 0), one_mul] using h

/-- At most five physical-cutoff primes occur in any nonzero narrowed
survivor on the complete-composite interval. This is a support bound, not
an estimate of the coupled signed sum of those surviving products. -/
theorem eventually_extreme_count_le_five {u : ℝ} (hu : 0 < u)
    (hcontact : u < Real.exp (-(1 / 2 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ n ∈ ZetaRieszNarrowCarrier.residualBand u N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n ≠ 0 →
        (extremePrimes u N n).card ≤ 5 := by
  filter_upwards [eventually_length_ge_order hu hcontact, eventually_ge_atTop 1] with N hLN hN
  intro n hn hcoeff
  have hs : Squarefree n := by
    by_contra hs
    exact hcoeff (by simp [SquarefreeVaughanLogSource.coefficient, hs])
  have hb := extreme_prime_count_le (c := 1) (by norm_num) (by omega)
    (by simpa using hLN) hn hs
  have hb6 : ((extremePrimes u N n).card : ℝ) < 6 := by
    norm_num only [div_one] at hb
    linarith [Real.log_two_lt_d9]
  have hh : (extremePrimes u N n).card < 6 := by exact_mod_cast hb6
  omega

end
end RiemannGaussian.ZetaRieszExtremePrimeCount
