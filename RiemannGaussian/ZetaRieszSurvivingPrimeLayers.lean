/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCompositeBoundaryWindow

/-!
# Complete surviving prime layers and their necessary window

Every nonzero actual survivor has its full smooth, intermediate and
extreme prime factors. A composite smooth core forces an actual divisor
in the strict physical boundary window with nonzero shifted profile.
Saturated extreme cores have coefficient norm at most the total logarithm,
independently of their extreme-prime count. The joint signed floor remains
open, and the earlier independent deletion retains its proved interval.
-/

namespace RiemannGaussian.ZetaRieszSurvivingPrimeLayers
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszExtremePrimeProfile
open ZetaRieszCompositeBoundaryWindow

/-- Complete squarefree factorization at any integer prime threshold.
This retains both full factors and proves their support separation. -/
theorem exists_threshold_factorization {n : ℕ} (hn : Squarefree n) (K : ℕ) :
    ∃ a b : ℕ, Squarefree a ∧ (∀ p ∈ a.primeFactors, p ≤ K) ∧
      Squarefree b ∧ (∀ p ∈ b.primeFactors, K < p) ∧ n = b * a := by
  let a := Nat.gcd n (primorial K)
  have had : a ∣ n := Nat.gcd_dvd_left _ _
  have hah : a ∣ primorial K := Nat.gcd_dvd_right _ _
  obtain ⟨b, he⟩ := had
  have hmul : Squarefree (a * b) := by rwa [← he]
  have ha : Squarefree a := hmul.of_mul_left
  have hb : Squarefree b := hmul.of_mul_right
  have hsmall (p : ℕ) (hp : p ∈ a.primeFactors) : p ≤ K := by
    have hm := Nat.primeFactors_mono hah (primorial_ne_zero _) hp
    rw [primeFactors_primorial] at hm
    exact (Nat.mem_primesLE.mp hm).1
  have hrough (p : ℕ) (hp : p ∈ b.primeFactors) : K < p := by
    apply lt_of_not_ge
    intro hle
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hphead : p ∣ primorial K := by
      apply Nat.dvd_of_mem_primeFactors
      rw [primeFactors_primorial]
      exact Nat.mem_primesLE.mpr ⟨hle, hprime⟩
    have hpb : p ∣ b := Nat.dvd_of_mem_primeFactors hp
    have hpn : p ∣ n := by rw [he]; exact dvd_mul_of_dvd_right hpb a
    have hpa : p ∣ a := Nat.dvd_gcd hpn hphead
    have hg : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
    rw [(Nat.coprime_of_squarefree_mul hmul).gcd_eq_one] at hg
    exact hprime.ne_one (Nat.dvd_one.mp hg)
  exact ⟨a, b, ha, hsmall, hb, hrough, he.trans (Nat.mul_comm a b)⟩

/-- Every nonzero survivor has all three complete prime layers:
the small smooth core, the intermediate primes, and the extreme primes.
The actual integer and physical cutoff are retained at every order. -/
theorem surviving_complete_prime_layers {u : ℝ} {N n : ℕ}
    (hn : n ∈ ZetaRieszLargeSmoothDeletion.largeSmoothResidualBand u N)
    (hc : SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n ≠ 0) :
    ∃ a q b : ℕ,
      Squarefree a ∧ (∀ p ∈ a.primeFactors, p ≤ N ^ 2) ∧
      Squarefree q ∧ (∀ p ∈ q.primeFactors,
        N ^ 2 < p ∧ p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ∧
      Squarefree b ∧ (∀ p ∈ b.primeFactors,
        N ^ 2 < p ∧ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p) ∧
      n = b * (q * a) ∧ a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 := by
  obtain ⟨a, r, ha, hsmall, hr, hrough, he, haX⟩ :=
    ZetaRieszLargeSmoothDeletion.surviving_support_with_small_smooth_factor hn hc
  let X := (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2
  have hX : 0 < X := by dsimp [X]; positivity
  obtain ⟨q, b, hq, hqsmall, hb, hblarge, hrqb⟩ := exists_threshold_factorization hr (X - 1)
  refine ⟨a, q, b, ha, hsmall, hq, ?_, hb, ?_, ?_, haX⟩
  · intro p hp
    have hd : q ∣ r := by rw [hrqb]; exact dvd_mul_left q b
    have hpr := Nat.primeFactors_mono hd hr.ne_zero hp
    have hlt := hqsmall p hp
    exact ⟨hrough p hpr, by change p < X; omega⟩
  · intro p hp
    have hd : b ∣ r := by rw [hrqb]; exact dvd_mul_right b q
    have hpr := Nat.primeFactors_mono hd hr.ne_zero hp
    have hgt := hblarge p hp
    exact ⟨hrough p hpr, by change X ≤ p; omega⟩
  · rw [he, hrqb, Nat.mul_assoc]

/-- A nonzero composite-core coefficient requires a real divisor
in the strict physical window, with a nonzero shifted core profile.
This is a necessary arithmetic witness, not a floor for the signed sum. -/
theorem nonzero_composite_has_boundary_divisor {u : ℝ} {N a b q : ℕ}
    (hfull : Squarefree (b * (q * a))) (ha1 : a ≠ 1) (hap : ¬ a.Prime)
    (hlarge : ∀ p ∈ b.primeFactors,
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p)
    (hc : SquarefreeVaughanLogSource.coefficient
      (SquarefreeVaughanLogSource.length u N) (b * (q * a)) ≠ 0) :
    ∃ d ∈ q.divisors,
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < d * a ∧
      d < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ∧
      VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N - Real.log d) a ≠ 0 := by
  have hsum : (∑ d ∈ q.divisors.filter (fun d =>
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < d * a ∧
      d < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N - Real.log d) a) ≠ 0 := by
    intro hzero
    apply hc
    rw [coefficient_extreme_composite_eq_physical_window hfull ha1 hap hlarge, hzero]
    simp
  obtain ⟨d, hd, hdterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  obtain ⟨hd, hlo, hhi⟩ := Finset.mem_filter.mp hd
  exact ⟨d, hd, hlo, hhi, right_ne_zero_of_mul hdterm⟩

/-- A saturated extreme-rough coefficient has at most one logarithm
of amplitude, independently of the number of extreme prime factors.
The exact signed core formula remains available before this norm bound. -/
theorem norm_coefficient_extreme_le_log {a b : ℕ} {L : ℝ}
    (hfull : Squarefree (b * a)) (hL : 0 < L) (haL : Real.log a ≤ L)
    (hlarge : ∀ p ∈ b.primeFactors, L ≤ Real.log p) :
    ‖SquarefreeVaughanLogSource.coefficient L (b * a)‖ ≤ Real.log (b * a : ℕ) := by
  rw [coefficient_extreme_eq_core_cases hfull hL haL hlarge]
  split_ifs
  · simpa only [norm_zero] using Real.log_natCast_nonneg (b * a)
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (Real.log_natCast_nonneg _)]
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_neg,
      abs_of_nonneg (Real.log_natCast_nonneg _),
      abs_of_nonneg (Real.log_natCast_nonneg _), abs_of_pos hL]
    exact (div_le_iff₀ hL).mpr (mul_le_mul_of_nonneg_left haL (Real.log_natCast_nonneg _))
  · simpa only [norm_zero] using Real.log_natCast_nonneg (b * a)

/-- The actual physical coefficient on any saturated extreme core
has the same uniform logarithmic amplitude, including all early orders. -/
theorem norm_coefficient_physical_extreme_le_log {u : ℝ} {N a b : ℕ}
    (hfull : Squarefree (b * a))
    (haX : a ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hlarge : ∀ p ∈ b.primeFactors,
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p) :
    ‖SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) (b * a)‖ ≤
      Real.log (b * a : ℕ) := by
  apply norm_coefficient_extreme_le_log hfull (SquarefreeVaughanLogSource.length_pos u N)
  · apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hfull.of_mul_right.ne_zero)
    exact_mod_cast haX
  · intro p hp
    apply Real.log_le_log (by positivity)
    exact_mod_cast hlarge p hp

/-- Every nonzero surviving integer has a complete three-layer
factorization, and a composite small core forces a nonzero signed-profile
witness in the strict physical divisor window. All existence obligations
are discharged for the original coefficient. -/
theorem surviving_layers_with_boundary_witness {u : ℝ} {N n : ℕ}
    (hn : n ∈ ZetaRieszLargeSmoothDeletion.largeSmoothResidualBand u N)
    (hc : SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n ≠ 0) :
    ∃ a q b : ℕ,
      Squarefree a ∧ (∀ p ∈ a.primeFactors, p ≤ N ^ 2) ∧
      Squarefree q ∧ (∀ p ∈ q.primeFactors,
        N ^ 2 < p ∧ p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ∧
      Squarefree b ∧ (∀ p ∈ b.primeFactors,
        N ^ 2 < p ∧ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p) ∧
      n = b * (q * a) ∧ a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ∧
      (a ≠ 1 → ¬ a.Prime → ∃ d ∈ q.divisors,
        (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < d * a ∧
        d < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ∧
        VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N - Real.log d) a ≠ 0) := by
  obtain ⟨a, q, b, ha, hsmall, hq, hmiddle, hb, hlarge, he, haX⟩ := surviving_complete_prime_layers hn hc
  refine ⟨a, q, b, ha, hsmall, hq, hmiddle, hb, hlarge, he, haX, ?_⟩
  intro ha1 hap
  have hc' : SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) (b * (q * a)) ≠ 0 :=
    he ▸ hc
  have hfull : Squarefree (b * (q * a)) := by
    by_contra h
    exact hc' (by simp [SquarefreeVaughanLogSource.coefficient, h])
  exact nonzero_composite_has_boundary_divisor hfull ha1 hap (fun p hp => (hlarge p hp).2) hc'

end
end RiemannGaussian.ZetaRieszSurvivingPrimeLayers
