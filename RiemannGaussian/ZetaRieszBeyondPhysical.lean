/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszProductCeiling
import RiemannGaussian.ZetaRieszSmoothPrimePrefix

/-!
# Composite smooth cofactors beyond the physical prime cutoff

The actual large-cofactor class decays when 2*u^2<1. Below the physical
cofactor cutoff, composite smooth cofactors vanish exactly when the prime
is beyond that cutoff. Combined with the proved prime-prefix bound, every
one-large-prime composite-smooth pair family decays for 1/2<u<exp(-1/2).
Semiprimes and multiple-large-prime classes remain outside this assertion.
-/

namespace RiemannGaussian.ZetaRieszBeyondPhysical
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszSmoothPrimeProduct
open ZetaRieszProductCeiling

/-- The actual integer class with one large prime and a smooth
cofactor at or beyond the physical cutoff, retaining an arbitrary mask. -/
def largeCofactorBand (keep : ℕ → Prop) (u : ℝ) (N : ℕ) : Finset ℕ :=
  ZetaRieszSmoothPrimePrefix.productBand keep
    ((ZetaRieszSmoothPrimePrefix.cofactorHead (N ^ 2)).filter
      (fun a => (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ a))
    ((Nat.primesLE (2 ^ (32 * N))).filter (fun p => N ^ 2 < p)) N

/-- The complete actual large-cofactor class decays independently
when 2*u^2<1. Prime support, product ceiling and all original filter offsets remain. -/
theorem tendsto_actual_largeCofactorBand (keep : ℕ → ℕ → Prop) (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (hu2 : 2 * u ^ 2 < 1) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      ∑ n ∈ largeCofactorBand (keep N) u N,
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (nhds 0) := by
  let A := fun N => (ZetaRieszSmoothPrimePrefix.cofactorHead (N ^ 2)).filter
    (fun a => (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ a)
  let Q := fun N => (Nat.primesLE (2 ^ (32 * N))).filter (fun p => N ^ 2 < p)
  have hA N a (ha : a ∈ A N) : Squarefree a :=
    ZetaRieszSmoothPrimePrefix.cofactorHead_squarefree _ _ (Finset.mem_filter.mp ha).1
  have hS N a (ha : a ∈ A N) : a.primeFactors ⊆ Nat.primesLE (N ^ 2) :=
    ZetaRieszSmoothPrimePrefix.cofactorHead_primeFactors _ _ (Finset.mem_filter.mp ha).1
  have hQ N p (hp : p ∈ Q N) : p.Prime :=
    (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
  have he N : (∑ n ∈ largeCofactorBand (keep N) u N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
      pairResponse (keep N) (A N) (Q N) P N y (SquarefreeVaughanLogSource.length u N) := by
    apply ZetaRieszSmoothPrimePrefix.productBand_sum_eq_pairResponse _ _ _ P N (N ^ 2) y _ (hA N)
    · intro a ha p hp
      exact (Nat.mem_primesLE.mp (hS N a ha hp)).1
    · intro p hp
      exact ⟨hQ N p hp, (Finset.mem_filter.mp hp).2⟩
  simp_rw [he]
  exact tendsto_large_cofactor_pairResponse keep A Q (fun N => Nat.primesLE (N ^ 2)) P y hA hS
    (fun N p hp => ⟨(Nat.mem_primesLE.mp hp).2, (Nat.mem_primesLE.mp hp).1⟩)
    hQ hu hu2 (fun N a ha => (Finset.mem_filter.mp ha).2)

/-- The prime prefix and its complement split the original signed
pair response exactly, before any norm or coefficient bound is applied. -/
theorem pairResponse_eq_prime_split (keep : ℕ → Prop) (A Q : Finset ℕ)
    (P : Polynomial ℂ) (N X : ℕ) (y L : ℝ) :
    pairResponse keep A Q P N y L =
      pairResponse keep A (Q.filter (fun p => p ≤ X)) P N y L +
      pairResponse keep A (Q.filter (fun p => X < p)) P N y L := by
  simp only [pairResponse, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases h : p ≤ X
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

/-- Beyond the physical prime cutoff, all smaller composite smooth
cofactors disappear exactly from the signed response, at every original order. -/
theorem pairResponse_eq_large_of_beyond (keep : ℕ → Prop) (A Q : Finset ℕ)
    (P : Polynomial ℂ) (N : ℕ) (y u : ℝ)
    (hA : ∀ a ∈ A, Squarefree a ∧ a ≠ 1 ∧ ¬ a.Prime)
    (hsmall : ∀ a ∈ A, ∀ r ∈ a.primeFactors, r ≤ N ^ 2)
    (hQ : ∀ p ∈ Q, p.Prime ∧ N ^ 2 < p ∧
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p) :
    pairResponse keep A Q P N y (SquarefreeVaughanLogSource.length u N) =
      pairResponse keep
        (A.filter (fun a => (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ a))
        Q P N y (SquarefreeVaughanLogSource.length u N) := by
  simp only [pairResponse, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hx : (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ a
  · simp only [hx, ite_true]
  · rw [if_neg hx]
    apply Finset.sum_eq_zero
    intro p hp
    split_ifs
    · rw [coefficient_eq_zero_of_beyond_physical (hA a ha).1 (hA a ha).2.1
        (hA a ha).2.2 (hsmall a ha) (hQ p hp).1 (hQ p hp).2.1 (hQ p hp).2.2
        (by omega), zero_mul]
    · rfl

/-- All composite smooth-cofactor contributions beyond the physical
prime cutoff decay independently when 2*u^2<1, without a cofactor size cap. -/
theorem tendsto_beyond_composite_pairResponse (keep : ℕ → ℕ → Prop)
    (A Q S : ℕ → Finset ℕ) (P : Polynomial ℂ) (y : ℝ)
    (hA : ∀ N a, a ∈ A N → Squarefree a ∧ a ≠ 1 ∧ ¬ a.Prime)
    (hS : ∀ N a, a ∈ A N → a.primeFactors ⊆ S N)
    (hprime : ∀ N p, p ∈ S N → p.Prime ∧ p ≤ N ^ 2)
    {u : ℝ} (hu : 0 < u) (hu2 : 2 * u ^ 2 < 1)
    (hQ : ∀ N p, p ∈ Q N → p.Prime ∧ N ^ 2 < p ∧
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      pairResponse (keep N) (A N) (Q N) P N y (SquarefreeVaughanLogSource.length u N))
      atTop (nhds 0) := by
  have he N := pairResponse_eq_large_of_beyond (keep N) (A N) (Q N) P N y u (hA N)
    (fun a ha p hp => (hprime N p (hS N a ha hp)).2) (hQ N)
  simp_rw [he]
  apply tendsto_large_cofactor_pairResponse keep _ Q S P y
    (fun N a ha => (hA N a (Finset.mem_filter.mp ha).1).1)
    (fun N a ha => hS N a (Finset.mem_filter.mp ha).1) hprime
    (fun N p hp => (hQ N p hp).1) hu hu2
  intro N a ha
  exact (Finset.mem_filter.mp ha).2

/-- The prefix interval lies strictly inside the new large-cofactor
saving interval; no numerical comparison of exponential constants is assumed. -/
theorem twice_square_lt_one_of_small_source {u : ℝ} (hu : 0 < u)
    (hcontact : u < Real.exp (-(1 / 2 : ℝ))) : 2 * u ^ 2 < 1 := by
  have he : (2 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    linarith
  have hs : Real.exp (-(1 / 2 : ℝ)) ^ 2 = (Real.exp 1)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    norm_num
  have huq : u ^ 2 < Real.exp (-(1 / 2 : ℝ)) ^ 2 := by nlinarith [Real.exp_pos (-(1 / 2 : ℝ))]
  rw [hs] at huq
  have hi : (Real.exp 1)⁻¹ < (1 / 2 : ℝ) := by
    simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2) he
  linarith

/-- On the proved prefix interval, the complete one-large-prime
response with composite quadratic-head cofactors decays independently,
including all primes beyond the physical cutoff and every cofactor size. -/
theorem tendsto_all_composite_pairResponse (keep : ℕ → ℕ → Prop)
    (A Q S : ℕ → Finset ℕ) (P : Polynomial ℂ) (y : ℝ)
    (hA : ∀ N a, a ∈ A N → Squarefree a ∧ a ≠ 1 ∧ ¬ a.Prime)
    (hS : ∀ N a, a ∈ A N → a.primeFactors ⊆ S N)
    (hprime : ∀ N p, p ∈ S N → p.Prime ∧ p ≤ N ^ 2)
    (hQ : ∀ N p, p ∈ Q N → p.Prime ∧ N ^ 2 < p)
    {u : ℝ} (hu : 1 / 2 < u) (hcontact : u < Real.exp (-(1 / 2 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      pairResponse (keep N) (A N) (Q N) P N y (SquarefreeVaughanLogSource.length u N))
      atTop (nhds 0) := by
  have hu0 : 0 < u := by linarith
  obtain ⟨q, hq, hq1, hrate⟩ := ZetaRieszSmoothPrimePrefix.exists_quadratic_head_tilt hu hcontact
  let Qlo := fun N => (Q N).filter
    (fun p => p ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
  let Qhi := fun N => (Q N).filter
    (fun p => (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < p)
  have hlo := tendsto_quadratic_pairResponse keep A Qlo S P y
    (fun N a ha => (hA N a ha).1) hS hprime hu0
    ((hcontact.trans (Real.exp_lt_one_iff.mpr (by norm_num))).le) hq hq1
    (fun N p hp => ⟨(hQ N p (Finset.mem_filter.mp hp).1).1, (Finset.mem_filter.mp hp).2⟩) hrate
  have hhi := tendsto_beyond_composite_pairResponse keep A Qhi S P y hA hS hprime hu0
    (twice_square_lt_one_of_small_source hu0 hcontact)
    (fun N p hp => ⟨(hQ N p (Finset.mem_filter.mp hp).1).1,
      (hQ N p (Finset.mem_filter.mp hp).1).2, (Finset.mem_filter.mp hp).2.le⟩)
  have h := hlo.add hhi
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with N
  rw [pairResponse_eq_prime_split (keep N) (A N) (Q N) P N
    ((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)]
  ring

end
end RiemannGaussian.ZetaRieszBeyondPhysical
