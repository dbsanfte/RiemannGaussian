/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCentralPair
import RiemannGaussian.ZetaRieszTriplePrime

/-!
# The actual central carrier separated by prime degree

Every three-prime coefficient in the remaining central support has
a known sign and two independent amplitude bounds. The exact carrier
retains the full prime head, pair correction, three-prime response and
the four-or-more-prime response together. Their joint cofinal floor
remains open; no new zero-free region is claimed.
-/

namespace RiemannGaussian.ZetaRieszCentralPrimeLayers
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAnnulusJoint ZetaRieszCentralWindow ZetaRieszRemainingPrefix
open ZetaRieszCentralPair ZetaRieszTriplePrime

/-- The inherited central unpaired support, retaining every previous
arithmetic cut, the physical annulus and every prime below its cutoff. -/
def centralUnpairedBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  centralBand (((ZetaRieszPhysicalAnnulus.annulusBand u N).filter (fun n =>
    ∀ p ∈ n.primeFactors, p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)) \
      pairedLabels (intermediatePrimes u N)) N

/-- The new support still consists of actual original annular integers. -/
theorem centralUnpairedBand_subset_annulus (u : ℝ) (N : ℕ) :
    centralUnpairedBand u N ⊆ ZetaRieszPhysicalAnnulus.annulusBand u N := by
  intro n hn
  exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hn).1).1).1

/-- The literal integer annulus, with the damped floor kept, lies on
the upper-cutoff side of each integer's reflection midpoint. -/
theorem log_lt_twice_length_of_mem_annulus {u : ℝ} {N n : ℕ}
    (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hn : n ∈ ZetaRieszPhysicalAnnulus.annulusBand u N) :
    Real.log n < 2 * SquarefreeVaughanLogSource.length u N := by
  have hp := (ZetaRieszPhysicalAnnulus.mem_annulusBand huh).mp hn
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (lt_trans (by positivity :
      0 < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) hp.2.1)
  have h := Real.log_lt_log hn0 (show (n : ℝ) <
      (((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2 : ℕ) by
        exact_mod_cast hp.2.2)
  simpa only [SquarefreeVaughanLogSource.length, Nat.cast_pow, Nat.cast_add,
    Nat.cast_ofNat, Real.log_pow] using h

/-- Every surviving three-prime coefficient has a nonnegative arithmetic
sign and both the half-logarithm and reflection-gap bounds. All these
hypotheses follow from the actual support, without a zero assumption. -/
theorem central_three_coefficient_bounds {u : ℝ} {N n : ℕ}
    (huh : u < Real.exp (-(2 / 3 : ℝ))) (hn : n ∈ centralUnpairedBand u N)
    (hcard : n.primeFactors.card = 3) :
    0 ≤ (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n).re ∧
      ‖SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n‖ ≤
        Real.log n / 2 ∧
      ‖SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n‖ ≤
        Real.log n / SquarefreeVaughanLogSource.length u N *
          (2 * SquarefreeVaughanLogSource.length u N - Real.log n) := by
  have hmid := (log_lt_twice_length_of_mem_annulus huh
    (centralUnpairedBand_subset_annulus u N hn)).le
  exact ⟨(actual_three_prime_coefficient_bounds hcard
    (SquarefreeVaughanLogSource.length_pos u N) hmid).1,
    (actual_three_prime_coefficient_bounds hcard
      (SquarefreeVaughanLogSource.length_pos u N) hmid).2,
    norm_actual_three_prime_le_midpoint_gap hcard
      (SquarefreeVaughanLogSource.length_pos u N) hmid⟩

/-- The entire actual three-prime part, with its known arithmetic sign
but unchanged factorial filter and product phase. -/
def centralThreePrimeResponse (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ (centralUnpairedBand u N).filter (fun n => n.primeFactors.card = 3),
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- The remaining actual coefficient class with four or more distinct
prime factors. No sign or cancellation is assumed for this class. -/
def centralHigherPrimeResponse (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ (centralUnpairedBand u N).filter (fun n => 4 ≤ n.primeFactors.card),
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- The previous three-factor support theorem gives an exact signed
partition. Integers occur once, and zero coefficients remove all lower
degrees without silently changing any old arithmetic support. -/
theorem eventually_unpaired_eq_three_add_higher (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, centralUnpairedResponse P u y N =
      centralThreePrimeResponse P u y N + centralHigherPrimeResponse P u y N := by
  filter_upwards [eventually_centralUnpaired_three_primes hu huh] with N hdegree
  change (∑ n ∈ centralUnpairedBand u N,
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) = _
  simp only [centralThreePrimeResponse, centralHigherPrimeResponse, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h3 : n.primeFactors.card = 3
  · have h4 : ¬ 4 ≤ n.primeFactors.card := by omega
    simp only [if_pos h3, if_neg h4, add_zero]
  · by_cases h4 : 4 ≤ n.primeFactors.card
    · simp only [if_neg h3, if_pos h4, zero_add]
    · have hc : SquarefreeVaughanLogSource.coefficient
          (SquarefreeVaughanLogSource.length u N) n = 0 := by
        by_contra hc
        have := hdegree n hn hc
        omega
      simp only [if_neg h3, if_neg h4, hc, zero_mul, zero_add]

/-- The complete head and explicit pair correction remain coupled with
both actual higher-degree classes. The new partition is a literal identity,
not an assertion that any of its four terms separately tends to zero. -/
theorem eventually_centralJoint_eq_prime_layers (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, centralJoint P u y N =
      ZetaPrimeCofactorCompletion.completedCofactorHead (intermediatePrimes u N) P N
        (3 / 2 + Complex.I * y) (SquarefreeVaughanLogSource.length u N) +
      centralPairResponse P u y N + centralThreePrimeResponse P u y N +
      centralHigherPrimeResponse P u y N := by
  filter_upwards [eventually_unpaired_eq_three_add_higher P y hu huh] with N he
  rw [centralJoint, he]
  ring

/-- A literal source-normalized lower bound for the entire surviving
three-prime response. Its cost retains only negative real observations,
with coefficient one half-logarithm. It is uniform in height and fixed
filter; estimating this phase cost remains an open arithmetic task. -/
theorem re_normalized_three_ge_negative_phase (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) (N : ℕ) :
    u ^ (N + 1) * (∑ n ∈ (centralUnpairedBand u N).filter
      (fun n => n.primeFactors.card = 3),
        -(Real.log n / 2) * max 0 (-(zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n).re)) ≤
      ((u : ℂ) ^ (N + 1) * centralThreePrimeResponse P u y N).re := by
  have h := re_three_prime_sum_ge_negative_phase
    ((centralUnpairedBand u N).filter (fun n => n.primeFactors.card = 3))
    (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
    (SquarefreeVaughanLogSource.length_pos u N)
    (fun _ hn => (Finset.mem_filter.mp hn).2)
    (fun _ hn => (log_lt_twice_length_of_mem_annulus huh
      (centralUnpairedBand_subset_annulus u N (Finset.mem_filter.mp hn).1)).le)
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_left h (pow_nonneg hu _)

end

end RiemannGaussian.ZetaRieszCentralPrimeLayers
