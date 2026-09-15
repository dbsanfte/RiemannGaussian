/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszAnnulusJoint

/-!
# Exact correlations of both intermediate-prime incidences

At each distinct selected-prime product, both prefix incidences sum to
-log(n)^2/L. Combining them with the original Riesz coefficient gives
log(n)*min(1,log(n)/L) across the entire physical prefix. The coefficient
is nonnegative; its full cosine-weighted response still has no proved floor.
-/

namespace RiemannGaussian.ZetaRieszPrefixCorrelation
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszSemiprimeCompletion

/-- When both primes lie below the physical cutoff and their product
lies above it, the signed Riesz profile has an exact linear remainder. -/
theorem riesz_semiprime_inner {a p : ℕ} (ha : a.Prime) (hp : p.Prime)
    (hpa : ¬ p ∣ a) {L : ℝ} (haL : Real.log a ≤ L) (hpL : Real.log p ≤ L)
    (hLn : L ≤ Real.log (p * a : ℕ)) :
    VaughanLogAverage.riesz L (p * a) = Real.log (p * a : ℕ) - L := by
  have hlog : Real.log (p * a : ℕ) = Real.log p + Real.log a := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast ha.ne_zero)]
  have hshift : VaughanLogAverage.riesz (L - Real.log p) a = L - Real.log p := by
    rw [VaughanLogAverage.riesz, ha.sum_divisors]
    simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, Nat.cast_one,
      Real.log_one, sub_zero, one_mul, ArithmeticFunction.moebius_apply_prime ha, Int.cast_neg,
      max_eq_right (sub_nonneg.mpr hpL),
      max_eq_left (show L - Real.log p - Real.log a ≤ 0 by rw [hlog] at hLn; linarith),
      mul_zero, zero_add]
  rw [ZetaSquarefreeRieszWindows.riesz_prime_mul L hp hpa,
    ZetaRieszExtremePrimeProfile.riesz_prime_of_saturated ha haL, hshift, hlog]
  ring

/-- The actual squarefree semiprime coefficient in the inner physical
region retains the logarithm of the complete product. -/
theorem coefficient_semiprime_inner {a p : ℕ} (ha : a.Prime) (hp : p.Prime)
    (hpa : ¬ p ∣ a) {L : ℝ} (haL : Real.log a ≤ L) (hpL : Real.log p ≤ L)
    (hLn : L ≤ Real.log (p * a : ℕ)) :
    SquarefreeVaughanLogSource.coefficient L (p * a) =
      ((-Real.log (p * a : ℕ) * (Real.log (p * a : ℕ) - L) / L : ℝ) : ℂ) := by
  have hsf : Squarefree (p * a) := Nat.squarefree_mul_iff.mpr
    ⟨hp.coprime_iff_not_dvd.mpr hpa, hp.squarefree, ha.squarefree⟩
  rw [SquarefreeVaughanLogSource.coefficient, if_pos ⟨hsf, Nat.not_prime_mul hp.ne_one ha.ne_one⟩,
    riesz_semiprime_inner ha hp hpa haL hpL hLn]

/-- Retaining BOTH completed prime incidences cancels the cutoff-dependent
quadratic coefficient exactly, leaving log(n). This is an identity for the
actual coefficients, not a lower bound after the oscillating phase is applied. -/
theorem coefficient_sub_two_prime_lifts {a p : ℕ} (ha : a.Prime) (hp : p.Prime)
    (hpa : ¬ p ∣ a) {L : ℝ} (hL : 0 < L)
    (haL : Real.log a ≤ L) (hpL : Real.log p ≤ L)
    (hLn : L ≤ Real.log (p * a : ℕ)) :
    SquarefreeVaughanLogSource.coefficient L (p * a) -
      pairLift L a (p * a) - pairLift L p (p * a) = (Real.log (p * a : ℕ) : ℂ) := by
  have hq : p * a / a = p := by rw [mul_comm p a, Nat.mul_div_cancel_left _ ha.pos]
  have hpaLift : pairLift L a (p * a) = ((-Real.log (p * a : ℕ) * Real.log a / L : ℝ) : ℂ) := by
    rw [pairLift, if_pos ⟨dvd_mul_left a p, by simpa only [hq] using hp⟩]
  have hppLift : pairLift L p (p * a) = ((-Real.log (p * a : ℕ) * Real.log p / L : ℝ) : ℂ) := by
    rw [pairLift, if_pos ⟨dvd_mul_right p a, by simpa only [Nat.mul_div_cancel_left _ hp.pos] using ha⟩]
  rw [coefficient_semiprime_inner ha hp hpa haL hpL hLn, hpaLift, hppLift]
  have hlog : Real.log (p * a : ℕ) = Real.log p + Real.log a := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast ha.ne_zero)]
  simp only [hlog, ← Complex.ofReal_sub]
  congr 1
  field_simp
  ring

/-- At a product of two distinct primes below the physical cutoff, the
actual prefix contains exactly its two prime incidences. All other selected
prime cofactors contribute zero, without an absolute-value estimate. -/
theorem prefixCoefficient_prime_pair (A : Finset ℕ) (u : ℝ) (N : ℕ)
    (hA : ∀ b ∈ A, b.Prime) {a p : ℕ} (ha : a.Prime) (hp : p.Prime)
    (hpa : ¬ p ∣ a) (haA : a ∈ A) (hpA : p ∈ A)
    (haX : a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hpX : p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    ZetaRieszCrossCompletion.prefixCoefficient A u N (p * a) =
      pairLift (SquarefreeVaughanLogSource.length u N) a (p * a) +
      pairLift (SquarefreeVaughanLogSource.length u N) p (p * a) := by
  let f := fun b => if p * a / b < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 then
    pairLift (SquarefreeVaughanLogSource.length u N) b (p * a) else 0
  have hsub : ({a, p} : Finset ℕ) ⊆ A := by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨haA, hpA⟩
  have hsum : ∑ b ∈ ({a, p} : Finset ℕ), f b = ∑ b ∈ A, f b := by
    apply Finset.sum_subset hsub
    intro b hb hnot
    have hnd : ¬ b ∣ p * a := by
      intro hd
      rcases (hA b hb).dvd_mul.mp hd with hd | hd
      · have he := (Nat.prime_dvd_prime_iff_eq (hA b hb) hp).mp hd
        exact hnot (by simp [he])
      · have he := (Nat.prime_dvd_prime_iff_eq (hA b hb) ha).mp hd
        exact hnot (by simp [he])
    have hz : pairLift (SquarefreeVaughanLogSource.length u N) b (p * a) = 0 := by
      exact if_neg (fun h => hnd h.1)
    simp only [f, hz, ite_self]
  have hap : a ≠ p := by
    intro he
    exact hpa (he ▸ dvd_refl p)
  have hqa : p * a / a = p := by rw [mul_comm p a, Nat.mul_div_cancel_left _ ha.pos]
  have hqp : p * a / p = a := Nat.mul_div_cancel_left _ hp.pos
  simpa only [Finset.sum_pair hap, f, hqa, hqp, if_pos haX, if_pos hpX,
    ZetaRieszCrossCompletion.prefixCoefficient] using hsum.symm

/-- The actual coefficient minus its complete selected-prime prefix
simplifies to log(n) on an inner semiprime whenever both incidences are
present. The potentially large cutoff-dependent terms cancel exactly. -/
theorem coefficient_sub_prefix_prime_pair (A : Finset ℕ) (u : ℝ) (N : ℕ)
    (hA : ∀ b ∈ A, b.Prime) {a p : ℕ} (ha : a.Prime) (hp : p.Prime)
    (hpa : ¬ p ∣ a) (haA : a ∈ A) (hpA : p ∈ A)
    (haX : a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hpX : p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hnX : (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p * a) :
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) (p * a) -
      ZetaRieszCrossCompletion.prefixCoefficient A u N (p * a) = (Real.log (p * a : ℕ) : ℂ) := by
  rw [prefixCoefficient_prime_pair A u N hA ha hp hpa haA hpA haX hpX, sub_add_eq_sub_sub]
  apply coefficient_sub_two_prime_lifts ha hp hpa (SquarefreeVaughanLogSource.length_pos u N)
  · apply Real.log_le_log (by exact_mod_cast ha.pos)
    exact_mod_cast haX.le
  · apply Real.log_le_log (by exact_mod_cast hp.pos)
    exact_mod_cast hpX.le
  · apply Real.log_le_log (by positivity)
    exact_mod_cast hnX

/-- For the canonical intermediate prime set, both incidences really are
present. Thus the finite correction in the WHOLE completed carrier has this
exact logarithmic simplification on every corresponding semiprime label.
The cosine of the product phase is still signed and is not bounded here. -/
theorem coefficient_sub_intermediate_prefix (u : ℝ) (N : ℕ) {a p : ℕ}
    (ha : a.Prime) (hp : p.Prime) (hpa : ¬ p ∣ a) (hNa : N ^ 2 < a) (hNp : N ^ 2 < p)
    (haX : a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hpX : p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hnX : (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p * a) :
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) (p * a) -
      ZetaRieszCrossCompletion.prefixCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N) u N (p * a) =
        (Real.log (p * a : ℕ) : ℂ) := by
  apply coefficient_sub_prefix_prime_pair _ u N
    (fun b hb => ((ZetaRieszAnnulusJoint.mem_intermediatePrimes u N b).mp hb).1) ha hp hpa
  · exact (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N a).mpr ⟨ha, hNa, haX⟩
  · exact (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mpr ⟨hp, hNp, hpX⟩
  · exact haX
  · exact hpX
  · exact hnX

end

noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszSemiprimeCompletion

/-- Both physical-prefix incidences at a distinct-prime product add to
exactly minus the square of its COMPLETE logarithm divided by L_N. -/
theorem prefixCoefficient_prime_pair_eq_log_square (A : Finset ℕ) (u : ℝ) (N : ℕ)
    (hA : ∀ b ∈ A, b.Prime) {a p : ℕ} (ha : a.Prime) (hp : p.Prime)
    (hpa : ¬ p ∣ a) (haA : a ∈ A) (hpA : p ∈ A)
    (haX : a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hpX : p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    ZetaRieszCrossCompletion.prefixCoefficient A u N (p * a) =
      ((-(Real.log (p * a : ℕ)) ^ 2 / SquarefreeVaughanLogSource.length u N : ℝ) : ℂ) := by
  rw [prefixCoefficient_prime_pair A u N hA ha hp hpa haA hpA haX hpX]
  have hqa : p * a / a = p := by rw [mul_comm p a, Nat.mul_div_cancel_left _ ha.pos]
  have hqp : p * a / p = a := Nat.mul_div_cancel_left _ hp.pos
  rw [pairLift, if_pos ⟨dvd_mul_left a p, by simpa only [hqa] using hp⟩,
    pairLift, if_pos ⟨dvd_mul_right p a, by simpa only [hqp] using ha⟩]
  rw [← Complex.ofReal_add]
  congr 1
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast ha.ne_zero)]
  ring

/-- Across the ENTIRE physical prefix, the coefficient minus both prime
incidences is the same clipped logarithmic weight. Both sides of the
original product cutoff are retained in one exact identity. -/
theorem coefficient_sub_prefix_eq_clipped_log (A : Finset ℕ) (u : ℝ) (N : ℕ)
    (hA : ∀ b ∈ A, b.Prime) {a p : ℕ} (ha : a.Prime) (hp : p.Prime)
    (hpa : ¬ p ∣ a) (haA : a ∈ A) (hpA : p ∈ A)
    (haX : a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hpX : p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) (p * a) -
      ZetaRieszCrossCompletion.prefixCoefficient A u N (p * a) =
      ((Real.log (p * a : ℕ) * min 1
        (Real.log (p * a : ℕ) / SquarefreeVaughanLogSource.length u N) : ℝ) : ℂ) := by
  have hL := SquarefreeVaughanLogSource.length_pos u N
  by_cases hn : p * a ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2
  · have hlog : Real.log (p * a : ℕ) ≤ SquarefreeVaughanLogSource.length u N := by
      apply Real.log_le_log (by exact_mod_cast mul_pos hp.pos ha.pos)
      exact_mod_cast hn
    have hr : Real.log (p * a : ℕ) / SquarefreeVaughanLogSource.length u N ≤ 1 :=
      (div_le_one hL).mpr hlog
    rw [ZetaRieszPhysicalProductBounds.coefficient_eq_zero_below_physical hn,
      prefixCoefficient_prime_pair_eq_log_square A u N hA ha hp hpa haA hpA haX hpX,
      min_eq_right hr, zero_sub, ← Complex.ofReal_neg]
    congr 1
    ring
  · have hnX := (lt_of_not_ge hn).le
    have hlog : SquarefreeVaughanLogSource.length u N ≤ Real.log (p * a : ℕ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast hnX
    have hr : 1 ≤ Real.log (p * a : ℕ) / SquarefreeVaughanLogSource.length u N :=
      (le_div_iff₀ hL).mpr (by simpa using hlog)
    rw [coefficient_sub_prefix_prime_pair A u N hA ha hp hpa haA hpA haX hpX hnX,
      min_eq_left hr, mul_one]

/-- The canonical intermediate-prime correction has a nonnegative
clipped coefficient at every distinct-prime product, while its original
product phase remains fully oscillatory. This is not a signed-sum floor. -/
theorem re_coefficient_sub_prefix_nonneg (A : Finset ℕ) (u : ℝ) (N : ℕ)
    (hA : ∀ b ∈ A, b.Prime) {a p : ℕ} (ha : a.Prime) (hp : p.Prime)
    (hpa : ¬ p ∣ a) (haA : a ∈ A) (hpA : p ∈ A)
    (haX : a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hpX : p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    0 ≤ (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) (p * a) -
      ZetaRieszCrossCompletion.prefixCoefficient A u N (p * a)).re := by
  rw [coefficient_sub_prefix_eq_clipped_log A u N hA ha hp hpa haA hpA haX hpX, Complex.ofReal_re]
  exact mul_nonneg (Real.log_natCast_nonneg _) (le_min (by norm_num)
    (div_nonneg (Real.log_natCast_nonneg _) (SquarefreeVaughanLogSource.length_pos u N).le))

end

end RiemannGaussian.ZetaRieszPrefixCorrelation
