/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPhysicalAnnulus

/-!
# Exact prime completion across the common physical cutoff

Disjoint prime ranges give unique actual integer labels. The completed
cofactor head equals the original cross-cutoff coefficient series plus
its explicit finite physical prefix. Diagonal and repeated incidences
inside that prefix are retained. Genuine convergence and every fixed
factorial filter are proved; no cancellation of the prefix is assumed.
-/

namespace RiemannGaussian.ZetaRieszCrossCompletion
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszSemiprimeCompletion

/-- Actual prime cofactor incidences with the complementary prime at or
above the common physical cutoff. The selected cofactor set stays explicit. -/
def crossIncidences (A : Finset ℕ) (u : ℝ) (N n : ℕ) : Finset ℕ :=
  A.filter (fun a => a ∣ n ∧ (n / a).Prime ∧
    (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ n / a)

/-- Distinct prime ranges make the actual cross-cutoff product incidence
unique. No diagonal or unordered-pair factor is silently discarded. -/
theorem crossIncidences_unique (A : Finset ℕ) (u : ℝ) (N n : ℕ)
    (hA : ∀ a ∈ A, a.Prime ∧ a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    {a b : ℕ} (ha : a ∈ crossIncidences A u N n) (hb : b ∈ crossIncidences A u N n) : a = b := by
  obtain ⟨haA, had, hap, haX⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbA, hbd, _, _⟩ := Finset.mem_filter.mp hb
  have hdiv : b ∣ a * (n / a) := (Nat.mul_div_cancel' had).symm ▸ hbd
  rcases (hA b hbA).1.dvd_mul.mp hdiv with h | h
  · exact ((Nat.prime_dvd_prime_iff_eq (hA b hbA).1 (hA a haA).1).mp h).symm
  · have he := (Nat.prime_dvd_prime_iff_eq (hA b hbA).1 hap).mp h
    have hlt := (hA b hbA).2
    omega

/-- The complete cross-cutoff incidence set contains at most one cofactor
for each actual integer label. -/
theorem crossIncidences_card_le_one (A : Finset ℕ) (u : ℝ) (N n : ℕ)
    (hA : ∀ a ∈ A, a.Prime ∧ a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    (crossIncidences A u N n).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact crossIncidences_unique A u N n hA ha hb

/-- On every cross-cutoff incidence, the completed coefficient is exactly
the original signed Riesz coefficient at its unique integer label. -/
theorem pairLift_eq_coefficient_of_cross (A : Finset ℕ) (u : ℝ) (N n : ℕ)
    (hA : ∀ a ∈ A, a.Prime ∧ a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    {a : ℕ} (ha : a ∈ crossIncidences A u N n) :
    pairLift (SquarefreeVaughanLogSource.length u N) a n =
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n := by
  obtain ⟨haA, had, hp, hpX⟩ := Finset.mem_filter.mp ha
  have ha' := hA a haA
  have hpa : ¬ n / a ∣ a := by
    intro hd
    have hle := Nat.le_of_dvd ha'.1.pos hd
    omega
  have hLa : Real.log a ≤ SquarefreeVaughanLogSource.length u N := by
    apply Real.log_le_log (by exact_mod_cast ha'.1.pos)
    exact_mod_cast ha'.2.le
  have hLp : SquarefreeVaughanLogSource.length u N ≤ Real.log ((n / a : ℕ) : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hpX
  have h := ZetaRieszFixedCofactor.coefficient_prime_pair_above_cutoff ha'.1 hp hpa hLa hLp
  rw [Nat.div_mul_cancel had] at h
  rw [pairLift, if_pos (show a ∣ n ∧ (n / a).Prime from ⟨had, hp⟩)]
  exact h.symm

/-- The finite incidence sum is an exact mask of the ORIGINAL coefficient,
including its zero case. This is the integer-counting interface for genuine
prime completion; it supplies no cancellation estimate by itself. -/
theorem sum_crossIncidences_eq_coefficient (A : Finset ℕ) (u : ℝ) (N n : ℕ)
    (hA : ∀ a ∈ A, a.Prime ∧ a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    (∑ a ∈ crossIncidences A u N n, pairLift (SquarefreeVaughanLogSource.length u N) a n) =
      if (crossIncidences A u N n).Nonempty then
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n else 0 := by
  by_cases hS : (crossIncidences A u N n).Nonempty
  · obtain ⟨a, ha⟩ := hS
    have he : crossIncidences A u N n = {a} := by
      ext b
      simp only [Finset.mem_singleton]
      exact ⟨fun hb => crossIncidences_unique A u N n hA hb ha, fun hb => hb ▸ ha⟩
    rw [if_pos ⟨a, ha⟩, he, Finset.sum_singleton]
    exact pairLift_eq_coefficient_of_cross A u N n hA ha
  · rw [if_neg hS, Finset.not_nonempty_iff_eq_empty.mp hS, Finset.sum_empty]

/-- The cross-cutoff series is a literal mask of the original signed
coefficient. Each actual integer appears only once. -/
def crossCoefficient (A : Finset ℕ) (u : ℝ) (N n : ℕ) : ℂ :=
  if (crossIncidences A u N n).Nonempty then
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n else 0

/-- The exact physical prime prefix introduced by completing the upper
prime. Both lower primes, their logarithms and every incidence remain. -/
def prefixCoefficient (A : Finset ℕ) (u : ℝ) (N n : ℕ) : ℂ :=
  ∑ a ∈ A, if n / a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 then
    pairLift (SquarefreeVaughanLogSource.length u N) a n else 0

/-- Completing the upper prime introduces precisely the physical prefix.
This coefficient identity keeps diagonal and duplicate prefix incidences. -/
theorem integerCoefficient_eq_cross_add_prefix (A : Finset ℕ) (u : ℝ) (N n : ℕ)
    (hA : ∀ a ∈ A, a.Prime ∧ a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    integerCoefficient (SquarefreeVaughanLogSource.length u N) A n =
      crossCoefficient A u N n + prefixCoefficient A u N n := by
  unfold crossCoefficient
  rw [← sum_crossIncidences_eq_coefficient A u N n hA]
  simp only [crossIncidences, Finset.sum_filter, prefixCoefficient, integerCoefficient,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hd : a ∣ n ∧ (n / a).Prime
  · by_cases hX : (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ n / a
    · simp only [hd.1, hd.2, hX, true_and, if_true, Nat.not_lt.mpr hX, if_false, add_zero]
    · simp only [hd.1, hd.2, hX, true_and, if_false, lt_of_not_ge hX, if_true, zero_add]
  · have hz : pairLift (SquarefreeVaughanLogSource.length u N) a n = 0 := by
      simp only [pairLift, if_neg hd]
    rw [hz]
    split_ifs <;> simp

/-- The introduced prefix is finitely supported strictly below X_N^2.
This proves the support needed for its genuine finite/infinite subtraction. -/
theorem prefixCoefficient_eq_zero_above (A : Finset ℕ) (u : ℝ) (N n : ℕ)
    (hA : ∀ a ∈ A, a.Prime ∧ a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hn : ((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2 ≤ n) :
    prefixCoefficient A u N n = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  by_cases hX : n / a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2
  · rw [if_pos hX]
    by_cases hd : a ∣ n ∧ (n / a).Prime
    · have he := Nat.mul_div_cancel' hd.1
      have haX := (hA a ha).2
      have hX0 : 0 < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 := by positivity
      have hh := (Nat.mul_lt_mul_of_pos_left hX (hA a ha).1.pos).trans
        (Nat.mul_lt_mul_of_pos_right haX hX0)
      rw [he] at hh
      nlinarith
    · exact if_neg hd
  · exact if_neg hX

/-- The exact cross-cutoff integer series converges to the completed prime
head minus its actual finite prefix. No estimate on that prefix is assumed. -/
theorem hasSum_crossCoefficient (A : Finset ℕ) (u : ℝ) (N : ℕ) (P : Polynomial ℂ)
    (hA : ∀ a ∈ A, a.Prime ∧ a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => crossCoefficient A u N n * zetaPrimeFilterKernel P N s n)
      (ZetaPrimeCofactorCompletion.completedCofactorHead A P N s (SquarefreeVaughanLogSource.length u N) -
        ∑ n ∈ Finset.range (((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2),
          prefixCoefficient A u N n * zetaPrimeFilterKernel P N s n) := by
  have hprefix : HasSum (fun n : ℕ => prefixCoefficient A u N n * zetaPrimeFilterKernel P N s n)
      (∑ n ∈ Finset.range (((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2),
        prefixCoefficient A u N n * zetaPrimeFilterKernel P N s n) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    rw [prefixCoefficient_eq_zero_above A u N n hA (by simpa only [Finset.mem_range, not_lt] using hn),
      zero_mul]
  have hfull := hasSum_integerCoefficient A (fun a ha => (hA a ha).1.pos)
    (SquarefreeVaughanLogSource.length u N) P N hs
  apply (hfull.sub hprefix).congr_fun
  intro n
  rw [integerCoefficient_eq_cross_add_prefix A u N n hA]
  ring

/-- The completed cross-cutoff series still admits the original divisor
majorant. Thus its independent absolute convergence is also explicit. -/
theorem norm_crossCoefficient_le (A : Finset ℕ) (u : ℝ) (N n : ℕ) :
    ‖crossCoefficient A u N n‖ ≤ zetaMoebiusLogMajorant n := by
  unfold crossCoefficient
  split_ifs
  · exact SquarefreeVaughanLogSource.norm_coefficient_le (SquarefreeVaughanLogSource.length_pos u N) n
  · simpa only [norm_zero] using zetaMoebiusLogMajorant_nonneg n

end
end RiemannGaussian.ZetaRieszCrossCompletion
