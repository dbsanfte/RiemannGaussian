/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszNondominantCarrier
import RiemannGaussian.ZetaRieszSperner
import RiemannGaussian.ZetaRieszCosineCarrier

/-!
# Exact arithmetic signs when the reflected cutoff sees only single primes

If every prime logarithm lies between half the reflected cutoff and that
cutoff, all composite divisors cancel out of the reflected Riesz sum.
The original coefficient becomes an explicit linear expression, retaining
its Möbius parity. No zero or cancellation hypothesis is used.
-/

namespace RiemannGaussian.ZetaRieszReflectedLinear
noncomputable section
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszDominantAllocation

private theorem card_ge_two {n : ℕ} (hn : Squarefree n) (h1 : n ≠ 1)
    (hp : ¬ n.Prime) : 2 ≤ n.primeFactors.card := by
  by_contra h
  have hk : n.primeFactors.card = 0 ∨ n.primeFactors.card = 1 := by omega
  rcases hk with hk | hk
  · apply h1
    rw [← Nat.prod_primeFactors_of_squarefree hn, Finset.card_eq_zero.mp hk,
      Finset.prod_empty]
  · obtain ⟨p, he⟩ := Finset.card_eq_one.mp hk
    have heq : n = p := by
      rw [← Nat.prod_primeFactors_of_squarefree hn, he, Finset.prod_singleton]
    exact hp (heq ▸ Nat.prime_of_mem_primeFactors (by rw [he]; simp))

/-- Two or more actual prime factors cannot fit strictly below this reflected cutoff. -/
theorem composite_divisor_log_ge {n d : ℕ} (hn : Squarefree n)
    (hd : d ∈ n.divisors) (hd1 : d ≠ 1) (hdp : ¬d.Prime)
    {D : ℝ} (hD : 0 ≤ D) (hmin : ∀ p ∈ n.primeFactors, D / 2 ≤ Real.log p) :
    D ≤ Real.log d := by
  have hds := hn.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
  have hk := card_ge_two hds hd1 hdp
  have hs : (∑ _p ∈ d.primeFactors, D / 2) ≤ ∑ p ∈ d.primeFactors, Real.log p := by
    exact Finset.sum_le_sum (fun p hp => hmin p
      (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hn.ne_zero hp))
  rw [Finset.sum_const, nsmul_eq_mul,
    ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hds] at hs
  have hkR : (2 : ℝ) ≤ d.primeFactors.card := by exact_mod_cast hk
  nlinarith [mul_nonneg (sub_nonneg.mpr hkR) hD]

/-- The complete reflected divisor sum is evaluated, not replaced by its absolute mass. -/
theorem riesz_eq_linear {n : ℕ} (hn : Squarefree n) {D : ℝ} (hD : 0 ≤ D)
    (hp : ∀ p ∈ n.primeFactors, D / 2 ≤ Real.log p ∧ Real.log p ≤ D) :
    VaughanLogAverage.riesz D n =
      Real.log n - ((n.primeFactors.card : ℝ) - 1) * D := by
  let f := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    max 0 (D - Real.log d)
  have h1 : 1 ∉ n.primeFactors := fun h => Nat.not_prime_one (Nat.prime_of_mem_primeFactors h)
  have hsub : insert 1 n.primeFactors ⊆ n.divisors := by
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact Nat.mem_divisors.mpr ⟨one_dvd _, hn.ne_zero⟩
    · exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mem_primeFactors hd, hn.ne_zero⟩
  have he : (∑ d ∈ insert 1 n.primeFactors, f d) = ∑ d ∈ n.divisors, f d := by
    apply Finset.sum_subset hsub
    intro d hd hout
    have hd1 : d ≠ 1 := fun h => hout (by simp [h])
    have hdp : ¬d.Prime := fun h => hout (Finset.mem_insert_of_mem
      (h.mem_primeFactors (Nat.dvd_of_mem_divisors hd) hn.ne_zero))
    have hlog := composite_divisor_log_ge hn hd hd1 hdp hD (fun p h => (hp p h).1)
    simp only [f, max_eq_left (sub_nonpos.mpr hlog), mul_zero]
  change (∑ d ∈ n.divisors, f d) = _
  rw [← he, Finset.sum_insert h1]
  have hf : f 1 = D := by simp [f, max_eq_right hD]
  rw [hf]
  have hs : (∑ p ∈ n.primeFactors, f p) =
      ∑ p ∈ n.primeFactors, (Real.log p - D) := by
    apply Finset.sum_congr rfl
    intro p h
    simp only [f, ArithmeticFunction.moebius_apply_prime (Nat.prime_of_mem_primeFactors h),
      Int.cast_neg, Int.cast_one, max_eq_right (sub_nonneg.mpr (hp p h).2)]
    ring
  rw [hs, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hn]
  ring

/-- A decidable arithmetic class defined using the actual prime logarithms and cutoff. -/
def LinearClass (L : ℝ) (n : ℕ) : Prop :=
  Squarefree n ∧ 3 ≤ n.primeFactors.card ∧ 0 ≤ Real.log n - L ∧
    ∀ p ∈ n.primeFactors,
      (Real.log n - L) / 2 ≤ Real.log p ∧ Real.log p ≤ Real.log n - L

/-- Squarefree prime-count parity is the literal Möbius sign. -/
theorem moebius_eq_primeCount {n : ℕ} (hn : Squarefree n) :
    ArithmeticFunction.moebius n = (-1 : ℤ) ^ n.primeFactors.card := by
  have he : n.primeFactors.card = n.primeFactorsList.length :=
    List.toFinset_card_of_nodup hn.nodup_primeFactorsList
  rw [ArithmeticFunction.moebius_apply_of_squarefree hn,
    ArithmeticFunction.cardFactors_apply, he]

/-- The explicit coefficient retains prime-count parity and its exact radial sign change. -/
def linearCoefficient (L : ℝ) (n : ℕ) : ℝ :=
  -(Real.log n / L) * ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
    (((n.primeFactors.card : ℝ) - 1) * L -
      ((n.primeFactors.card : ℝ) - 2) * Real.log n)

/-- Every atom in the arithmetic class has this exact coefficient, with no Riesz sum left. -/
theorem coefficient_eq_linear {L : ℝ} {n : ℕ} (hn : LinearClass L n) :
    SquarefreeVaughanLogSource.coefficient L n = (linearCoefficient L n : ℂ) := by
  obtain ⟨hs, hk, hD, hp⟩ := hn
  have h1 : n ≠ 1 := by intro h; subst n; norm_num at hk
  have hnp : ¬n.Prime := by
    intro h
    rw [h.primeFactors, Finset.card_singleton] at hk
    omega
  have hr := VaughanLogAverage.riesz_reflection (Real.log n - L) hs h1 hnp
  rw [sub_sub_cancel] at hr
  rw [riesz_eq_linear hs hD hp] at hr
  rw [SquarefreeVaughanLogSource.coefficient, if_pos ⟨hs, hnp⟩, hr]
  congr 1
  unfold linearCoefficient
  ring

/-- For four prime factors the sign changes exactly at log n = 3L/2. -/
theorem linearCoefficient_four {L : ℝ} {n : ℕ} (hn : LinearClass L n)
    (hk : n.primeFactors.card = 4) :
    linearCoefficient L n = (Real.log n / L) * (2 * Real.log n - 3 * L) := by
  rw [linearCoefficient, moebius_eq_primeCount hn.1, hk]
  norm_num
  ring

/-- On the actual remaining support the evaluated class has between three and nine primes. -/
theorem linearClass_count_le_nine {u : ℝ} (hu : 1 / 2 ≤ u) {N K n : ℕ}
    (hN : 2 ≤ N) (hnB : n ∈ nondominantBand u N K)
    (hn : LinearClass (SquarefreeVaughanLogSource.length u N) n) :
    n.primeFactors.card ≤ 9 := by
  have hnret := (Finset.mem_sdiff.mp hnB).1
  have hnS := (Finset.mem_sdiff.mp hnret).1
  have hwin := (Finset.mem_filter.mp hnS).2
  have hlo : (7 / 4 : ℝ) * N < Real.log n := hwin.1
  have hL : SquarefreeVaughanLogSource.length u N ≤ (139 / 100 : ℝ) * N := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu hN
    have hlog : 2 * Real.log 2 ≤ (139 / 100 : ℝ) := by linarith [Real.log_two_lt_d9]
    exact h.trans (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg _))
  have hs : (∑ _p ∈ n.primeFactors,
      (Real.log n - SquarefreeVaughanLogSource.length u N) / 2) ≤
      ∑ p ∈ n.primeFactors, Real.log p :=
    Finset.sum_le_sum (fun p hp => (hn.2.2.2 p hp).1)
  rw [Finset.sum_const, nsmul_eq_mul,
    ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hn.1] at hs
  by_contra hk
  have hkR : (10 : ℝ) ≤ n.primeFactors.card := by exact_mod_cast (show 10 ≤ n.primeFactors.card by omega)
  have hD := hn.2.2.1
  nlinarith [mul_nonneg (sub_nonneg.mpr hkR) hD, Nat.cast_nonneg (α := ℝ) N]

end
end RiemannGaussian.ZetaRieszReflectedLinear
