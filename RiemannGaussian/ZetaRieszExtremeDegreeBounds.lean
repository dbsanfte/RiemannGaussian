/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszExtremePrimeCount

/-!
# Independent arithmetic decay at high extreme-prime degree

Every actual finite class with at least six physical-cutoff prime factors
has an unnormalized geometric bound on 0<u<exp(-1/2). At every fixed
0<u<1 a possibly different finite degree threshold gives the same type
of bound. The finite selections may vary freely, the ordinate is arbitrary,
and every fixed filter retains its explicit cost. No zero is assumed.
Lower extreme degrees and their intermediate-prime couplings remain unpaid.
-/

namespace RiemannGaussian.ZetaRieszExtremeDegreeBounds
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszExtremePrimeCount

/-- Every actual finite class containing at least six physical-cutoff
primes has an independent geometric arithmetic bound on the complete-
composite interval. The finite support may change arbitrarily with N. -/
theorem eventually_norm_many_extreme_sum_le (S : ℕ → Finset ℕ) (P : Polynomial ℂ)
    (y : ℝ) {u : ℝ} (hu : 0 < u) (hcontact : u < Real.exp (-(1 / 2 : ℝ)))
    (hS : ∀ N n, n ∈ S N → 6 ≤ (extremePrimes u N n).card) :
    ∀ᶠ N : ℕ in atTop,
      ‖∑ n ∈ S N, SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
          ZetaArithmeticLogWindow.upperRate ^ N *
            ZetaArithmeticLogWindow.tiltConstant P (1 / 5) (121 / 120) := by
  filter_upwards [eventually_length_ge_order hu hcontact] with N hLN
  have he : (∑ n ∈ S N, SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
      ∑ n ∈ (S N).filter Squarefree,
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hs : Squarefree n
    · simp only [hs, if_true]
    · simp [SquarefreeVaughanLogSource.coefficient, hs]
  rw [he]
  apply ZetaArithmeticLogWindow.norm_upper_sum_le
    _ _ (fun n _ => SquarefreeVaughanLogSource.norm_coefficient_le
      (SquarefreeVaughanLogSource.length_pos u N) n) P N y
  intro n hn
  have hs := (Finset.mem_filter.mp hn).2
  have hc : (6 : ℝ) ≤ (extremePrimes u N n).card := by
    exact_mod_cast hS N n (Finset.mem_filter.mp hn).1
  have hmass := extreme_prime_log_budget u N hs
  have hh := mul_le_mul_of_nonneg_right hc (SquarefreeVaughanLogSource.length_pos u N).le
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith [mul_le_mul_of_nonneg_right (Real.log_two_lt_d9.le) hN]

/-- The entire actual six-or-more-extreme-prime class vanishes even
before source normalization, on the stated source interval. This does
not bound the remaining zero-through-five-extreme-prime classes. -/
theorem tendsto_many_extreme_sum (S : ℕ → Finset ℕ) (P : Polynomial ℂ)
    (y : ℝ) {u : ℝ} (hu : 0 < u) (hcontact : u < Real.exp (-(1 / 2 : ℝ)))
    (hS : ∀ N n, n ∈ S N → 6 ≤ (extremePrimes u N n).card) :
    Tendsto (fun N : ℕ =>
      ∑ n ∈ S N, SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (eventually_norm_many_extreme_sum_le S P y hu hcontact hS)
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one ZetaArithmeticLogWindow.upperRate_pos.le
      ZetaArithmeticLogWindow.upperRate_lt_one).mul_const
        (ZetaArithmeticLogWindow.tiltConstant P (1 / 5) (121 / 120))

/-- At every source scale, sufficiently many physical-cutoff prime factors
force an actual arithmetic geometric bound. The integer threshold depends
only on u; the eventual bound is uniform in finite support, filter and height,
with the filter's explicit finite cost retained. -/
theorem exists_eventually_extreme_class_bound {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∃ K : ℕ, ∀ᶠ N : ℕ in atTop, ∀ S : Finset ℕ,
      (∀ n ∈ S, K ≤ (extremePrimes u N n).card) → ∀ (P : Polynomial ℂ) (y : ℝ),
      ‖∑ n ∈ S, SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
          ZetaArithmeticLogWindow.upperRate ^ N *
            ZetaArithmeticLogWindow.tiltConstant P (1 / 5) (121 / 120) := by
  obtain ⟨c, hc, hL⟩ := ZetaRieszCompletedCofactor.eventually_linear_length_lower hu hu1
  let K : ℕ := ⌈(8 * Real.log 2) / c⌉₊
  have hK : 8 * Real.log 2 ≤ (K : ℝ) * c :=
    (div_le_iff₀ hc).mp (Nat.le_ceil _)
  refine ⟨K, ?_⟩
  filter_upwards [hL] with N hLN
  intro S hS P y
  have he : (∑ n ∈ S, SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
      ∑ n ∈ S.filter Squarefree,
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hs : Squarefree n
    · simp only [hs, if_true]
    · simp [SquarefreeVaughanLogSource.coefficient, hs]
  rw [he]
  apply ZetaArithmeticLogWindow.norm_upper_sum_le
    _ _ (fun n _ => SquarefreeVaughanLogSource.norm_coefficient_le
      (SquarefreeVaughanLogSource.length_pos u N) n) P N y
  intro n hn
  have hs := (Finset.mem_filter.mp hn).2
  have hcard : (K : ℝ) ≤ (extremePrimes u N n).card := by
    exact_mod_cast hS n (Finset.mem_filter.mp hn).1
  calc
    _ = (8 * Real.log 2) * N := by ring
    _ ≤ ((K : ℝ) * c) * N := mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg N)
    _ = (K : ℝ) * (c * N) := by ring
    _ ≤ (K : ℝ) * SquarefreeVaughanLogSource.length u N :=
      mul_le_mul_of_nonneg_left hLN (Nat.cast_nonneg K)
    _ ≤ ((extremePrimes u N n).card : ℝ) * SquarefreeVaughanLogSource.length u N :=
      mul_le_mul_of_nonneg_right hcard (SquarefreeVaughanLogSource.length_pos u N).le
    _ ≤ _ := extreme_prime_log_budget u N hs

/-- Every fixed source scale has a finite extreme-prime degree above
which all actual finite arithmetic selections decay, before normalization.
This leaves the finitely many lower degrees and their intermediate-prime
couplings as the remaining contribution, not a proved whole-sum floor. -/
theorem exists_global_extreme_class_decay {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∃ K : ℕ, ∀ S : ℕ → Finset ℕ,
      (∀ N n, n ∈ S N → K ≤ (extremePrimes u N n).card) →
      ∀ (P : Polynomial ℂ) (y : ℝ), Tendsto (fun N : ℕ =>
        ∑ n ∈ S N, SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := exists_eventually_extreme_class_bound hu hu1
  refine ⟨K, ?_⟩
  intro S hS P y
  apply squeeze_zero_norm' (hK.mono (fun N hN => hN (S N) (hS N) P y))
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one ZetaArithmeticLogWindow.upperRate_pos.le
      ZetaArithmeticLogWindow.upperRate_lt_one).mul_const
        (ZetaArithmeticLogWindow.tiltConstant P (1 / 5) (121 / 120))

end
end RiemannGaussian.ZetaRieszExtremeDegreeBounds
