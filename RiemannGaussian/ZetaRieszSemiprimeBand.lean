/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSemiprimeCompletion

/-!
# Decay of the actual uniquely counted semiprime band

The entire original semiprime class with a prime factor at most N^2 has
vanishing source-normalized response at exposed right-half zeros, for
every fixed complex polynomial filter and varying selected small primes.
Double-small-prime products eventually lie below the original band;
the large prime is uniquely recoverable, so actual integers count once.
This is a component bound, not a bound for the full signed Riesz carrier.
-/

namespace RiemannGaussian.ZetaRieszSemiprimeBand
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaExposedZero
open ZetaExposedPrimeMoments
open ZetaPrimeCofactorCompletion
open ZetaRieszCompletedCofactor
open ZetaRieszSemiprimePrefix
open ZetaRieszSemiprimePrefixDecay
open ZetaRieszSemiprimeCompletion

/-- The entire actual semiprime PAIR band with small prime cofactors
has vanishing normalized response at an exposed zero. The physical prefix
and both original band tails are independently paid. Integer uniqueness
will be imposed on the one-large-prime class below. -/
theorem tendsto_actual_semiprime_pair_band (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (P : Polynomial ℂ) (A : ℕ → Finset ℕ)
    (hA : ∀ N a, a ∈ A N → a.Prime ∧ a ≤ N ^ 2) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      ∑ a ∈ A N, ∑ p ∈ Nat.primesLE (2 ^ (32 * N)), if a * p ∈ zetaPrimeLogBand N then
        SquarefreeVaughanLogSource.coefficient
          (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) (a * p) *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * (rho.1.im : ℂ)) (a * p : ℕ) else 0)
      atTop (𝓝 0) := by
  let u : ℝ := 3 / 2 - rho.1.re
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  let Q (N : ℕ) := (Nat.primesLE (2 ^ (32 * N))).filter
    (fun p => p ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
  have he := tendsto_semiprime_completion_prefix_error A Q P rho.1.im hu hu1 hA
    (fun _N _p hp => ⟨(Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2,
      (Finset.mem_filter.mp hp).2⟩) (fun N a p => a * p ∈ zetaPrimeLogBand N)
  have h := (tendsto_completed_integer_band rho hrho hexposed P A hA).add he
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_two_head_logs_le_length hu hu1] with N hN
  have hs : ∀ a ∈ A N, a.Prime ∧ Real.log a ≤ SquarefreeVaughanLogSource.length u N := by
    intro a ha
    refine ⟨(hA N a ha).1, ?_⟩
    have hlog := Real.log_le_log (by exact_mod_cast (hA N a ha).1.pos : (0 : ℝ) < a)
      (by exact_mod_cast (hA N a ha).2 : (a : ℝ) ≤ (N ^ 2 : ℕ))
    linarith [Real.log_natCast_nonneg (N ^ 2)]
  have hid := actual_pair_band_sub_completed_eq_prefix (A N) P N rho.1.im u hs
  change _ + (u : ℂ) ^ (N + 1) * _ = _
  dsimp only [Q]
  have hscaled := congrArg (fun z : ℂ => (u : ℂ) ^ (N + 1) * z) hid
  dsimp only [u] at hscaled ⊢
  linear_combination (norm := ring_nf) -hscaled

/-- Every integer through N to the fourth eventually lies below the
original band's strict lower edge. This removes the double-small-prime
part exactly, rather than by a multiplicity convention. -/
theorem eventually_fourth_power_not_mem_band :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, n ≤ N ^ 4 → n ∉ zetaPrimeLogBand N := by
  have hl : Tendsto (fun N : ℕ => 4 * Real.log N / (N : ℝ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, pow_one, one_mul, add_zero, mul_div_assoc, mul_zero] using h.const_mul 4
  filter_upwards [hl.eventually_lt_const (show 0 < Real.log 2 / 4 by positivity),
    eventually_ge_atTop 1] with N hlog hN
  intro n hn hband
  have hb := Finset.mem_filter.mp hband
  have hn0 := (Finset.mem_Icc.mp hb.1).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have ht := (div_lt_iff₀ hN0).mp hlog
  have hm := Real.log_le_log (by exact_mod_cast hn0 : (0 : ℝ) < n)
    (by exact_mod_cast hn : (n : ℝ) ≤ (N ^ 4 : ℕ))
  rw [Nat.cast_pow, Real.log_pow] at hm
  norm_num only [Nat.cast_ofNat] at hm
  nlinarith [hb.2]

/-- The actual one-large-prime semiprime class uses the existing
injective product-band definition. Its integer labels are counted once. -/
def semiprimeBand (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  ZetaRieszSmoothPrimePrefix.productBand (fun _ => True) A
    ((Nat.primesLE (2 ^ (32 * N))).filter (fun p => N ^ 2 < p)) N

/-- Prime factorization uniqueness converts the literal semiprime
integer sum to its pair sum, with the full factorial filter unchanged. -/
theorem semiprimeBand_sum_eq_pairs (A : Finset ℕ) (P : Polynomial ℂ)
    (N : ℕ) (y L : ℝ) (hA : ∀ a ∈ A, a.Prime ∧ a ≤ N ^ 2) :
    (∑ n ∈ semiprimeBand A N, SquarefreeVaughanLogSource.coefficient L n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
    ∑ a ∈ A, ∑ p ∈ (Nat.primesLE (2 ^ (32 * N))).filter (fun p => N ^ 2 < p),
      if a * p ∈ zetaPrimeLogBand N then SquarefreeVaughanLogSource.coefficient L (a * p) *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (a * p : ℕ) else 0 := by
  have h := ZetaRieszSmoothPrimePrefix.productBand_sum_eq_pairResponse (fun _ => True)
    A ((Nat.primesLE (2 ^ (32 * N))).filter (fun p => N ^ 2 < p)) P N (N ^ 2) y L
    (fun a ha => (hA a ha).1.squarefree) (fun a ha p hp => by
      have he : p = a := by simpa only [(hA a ha).1.primeFactors, Finset.mem_singleton] using hp
      simpa only [he] using (hA a ha).2)
    (fun p hp => ⟨(Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2,
      (Finset.mem_filter.mp hp).2⟩)
  simpa only [semiprimeBand, ZetaRieszSmoothPrimeProduct.pairResponse,
    and_true, Nat.mul_comm] using h

/-- Above the eventual lower-band threshold there are no omitted
small-prime pairs. Hence the full actual pair band is the uniquely counted
one-large-prime semiprime integer band. -/
theorem eventually_semiprimeBand_sum_eq_full_pairs (A : ℕ → Finset ℕ)
    (hA : ∀ N a, a ∈ A N → a.Prime ∧ a ≤ N ^ 2) (P : Polynomial ℂ) (y : ℝ) (L : ℕ → ℝ) :
    ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ semiprimeBand (A N) N, SquarefreeVaughanLogSource.coefficient (L N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
      ∑ a ∈ A N, ∑ p ∈ Nat.primesLE (2 ^ (32 * N)), if a * p ∈ zetaPrimeLogBand N then
        SquarefreeVaughanLogSource.coefficient (L N) (a * p) *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (a * p : ℕ) else 0 := by
  filter_upwards [eventually_fourth_power_not_mem_band] with N hN
  rw [semiprimeBand_sum_eq_pairs (A N) P N y (L N) (hA N)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hp : N ^ 2 < p
  · simp only [if_pos hp]
  · have hsmall : a * p ≤ N ^ 4 := by
      have h := Nat.mul_le_mul (hA N a ha).2 (le_of_not_gt hp)
      simpa only [← pow_add, show (2 : ℕ) + 2 = 4 by rfl] using h
    simp only [if_neg hp, if_neg (hN (a * p) hsmall)]

/-- The ACTUAL, uniquely counted, original-band semiprime class
with a prime factor at most N squared vanishes at every exposed right-half
zero. The coefficient, band, physical floor and arbitrary fixed filter are
unchanged. This bounds a full arithmetic class, not merely its completion. -/
theorem tendsto_actual_semiprime_integer_band (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (P : Polynomial ℂ) (A : ℕ → Finset ℕ)
    (hA : ∀ N a, a ∈ A N → a.Prime ∧ a ≤ N ^ 2) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      ∑ n ∈ semiprimeBand (A N) N, SquarefreeVaughanLogSource.coefficient
        (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * (rho.1.im : ℂ)) n) atTop (𝓝 0) := by
  apply (tendsto_actual_semiprime_pair_band rho hrho hexposed P A hA).congr'
  filter_upwards [eventually_semiprimeBand_sum_eq_full_pairs A hA P rho.1.im
    (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re))] with N hN
  rw [hN]

end
end RiemannGaussian.ZetaRieszSemiprimeBand
