/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLargeSmoothDeletion

/-!
# Exact Riesz profiles after extreme-prime insertion

Any number of primes beyond the common physical cutoff disappears from
the divisor profile exactly. The total integer and all downstream phases
remain. Saturated composite cores vanish; unit and prime cores retain
their explicit signed coefficients. Nonzero surviving composite cores
must contain an actual intermediate rough prime.
-/

namespace RiemannGaussian.ZetaRieszExtremePrimeProfile
noncomputable section
open Filter Topology
open scoped BigOperators Classical

/-- Every prime beyond the common Riesz cutoff disappears from the
cofactor profile exactly. The entire squarefree rough factor is retained
upstream, with no restriction on its number of prime factors. -/
theorem riesz_mul_eq_of_extreme_rough {a b : ℕ} {L : ℝ}
    (hfull : Squarefree (b * a)) (hlarge : ∀ p ∈ b.primeFactors, L ≤ Real.log p) :
    VaughanLogAverage.riesz L (b * a) = VaughanLogAverage.riesz L a := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
    by_cases hb : b = 1
    · simp [hb]
    have hbs : Squarefree b := hfull.of_mul_left
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hb
    obtain ⟨c, hbc⟩ := hpd
    have hs : Squarefree (p * (c * a)) := by simpa only [hbc, Nat.mul_assoc] using hfull
    have hca : Squarefree (c * a) := hs.of_mul_right
    have hc0 : 0 < c := Nat.pos_of_ne_zero hca.of_mul_left.ne_zero
    have hc_lt : c < b := by rw [hbc]; nlinarith [hp.two_le]
    have hpx : L ≤ Real.log p := hlarge p
      (Nat.mem_primeFactors.mpr ⟨hp, by rw [hbc]; exact dvd_mul_right p c, hbs.ne_zero⟩)
    have hpa : ¬ p ∣ c * a := hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)
    rw [hbc, Nat.mul_assoc, ZetaSquarefreeRieszWindows.riesz_prime_mul L hp hpa,
      ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos (sub_nonpos.mpr hpx), sub_zero]
    apply ih c hc_lt hca
    intro r hr
    apply hlarge r
    exact Nat.primeFactors_mono (by rw [hbc]; exact dvd_mul_left c p) hbs.ne_zero hr

/-- An extreme rough factor with a saturated composite core has
exactly zero original coefficient, at the same common physical length. -/
theorem coefficient_eq_zero_of_extreme_composite {a b : ℕ} {L : ℝ}
    (hfull : Squarefree (b * a)) (ha1 : a ≠ 1) (hap : ¬ a.Prime)
    (haL : Real.log a ≤ L) (hlarge : ∀ p ∈ b.primeFactors, L ≤ Real.log p) :
    SquarefreeVaughanLogSource.coefficient L (b * a) = 0 := by
  have he := riesz_mul_eq_of_extreme_rough hfull hlarge
  have hz := ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated hfull.of_mul_right ha1 hap haL
  simp [SquarefreeVaughanLogSource.coefficient, he, hz]

/-- A saturated prime core retains exactly its logarithm in the
Riesz profile, including the boundary at the common physical cutoff. -/
theorem riesz_prime_of_saturated {a : ℕ} (ha : a.Prime) {L : ℝ}
    (haL : Real.log a ≤ L) : VaughanLogAverage.riesz L a = Real.log a := by
  have hL0 : 0 ≤ L := (Real.log_natCast_nonneg a).trans haL
  rw [VaughanLogAverage.riesz, ha.sum_divisors]
  simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, Nat.cast_one,
    Real.log_one, sub_zero, max_eq_right hL0, one_mul,
    ArithmeticFunction.moebius_apply_prime ha, Int.cast_neg, neg_mul,
    max_eq_right (sub_nonneg.mpr haL)]
  ring

/-- An extreme rough factor leaves only the unit or prime core in a
saturated squarefree Riesz profile; every composite core vanishes exactly. -/
theorem riesz_extreme_eq_core_cases {a b : ℕ} {L : ℝ}
    (hfull : Squarefree (b * a)) (hL : 0 ≤ L) (haL : Real.log a ≤ L)
    (hlarge : ∀ p ∈ b.primeFactors, L ≤ Real.log p) :
    VaughanLogAverage.riesz L (b * a) = if a = 1 then L else if a.Prime then Real.log a else 0 := by
  rw [riesz_mul_eq_of_extreme_rough hfull hlarge]
  by_cases ha1 : a = 1
  · subst a
    simp [VaughanLogAverage.riesz, max_eq_right hL]
  · rw [if_neg ha1]
    by_cases hap : a.Prime
    · rw [if_pos hap, riesz_prime_of_saturated hap haL]
    · rw [if_neg hap, ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated hfull.of_mul_right ha1 hap haL]

/-- The original coefficient on the complete extreme-rough class has
an exact signed description. Prime labels remain deleted; unit and prime
cores have explicit negative weights, while composite cores contribute zero. -/
theorem coefficient_extreme_eq_core_cases {a b : ℕ} {L : ℝ}
    (hfull : Squarefree (b * a)) (hL : 0 < L) (haL : Real.log a ≤ L)
    (hlarge : ∀ p ∈ b.primeFactors, L ≤ Real.log p) :
    SquarefreeVaughanLogSource.coefficient L (b * a) =
      if (b * a).Prime then 0 else if a = 1 then ((-Real.log (b * a : ℕ) : ℝ) : ℂ)
      else if a.Prime then ((-Real.log (b * a : ℕ) * Real.log a / L : ℝ) : ℂ) else 0 := by
  by_cases hn : (b * a).Prime
  · simp [SquarefreeVaughanLogSource.coefficient, hn]
  · simp only [SquarefreeVaughanLogSource.coefficient, hfull, hn, not_false_eq_true,
      and_self, ite_true, ite_false]
    rw [riesz_extreme_eq_core_cases hfull hL.le haL hlarge]
    by_cases ha1 : a = 1
    · simp only [ha1, mul_one, ↓reduceIte, mul_div_cancel_right₀ _ hL.ne']
    · simp only [ha1, ite_false]
      split_ifs <;> simp

/-- On the exact saturated extreme-rough class, the arithmetic
coefficient is real and nonpositive before the oscillatory kernel is applied. -/
theorem coefficient_extreme_re_nonpos {a b : ℕ} {L : ℝ}
    (hfull : Squarefree (b * a)) (hL : 0 < L) (haL : Real.log a ≤ L)
    (hlarge : ∀ p ∈ b.primeFactors, L ≤ Real.log p) :
    (SquarefreeVaughanLogSource.coefficient L (b * a)).re ≤ 0 := by
  rw [coefficient_extreme_eq_core_cases hfull hL haL hlarge]
  split_ifs <;> simp only [Complex.zero_re, Complex.ofReal_re]
  · exact le_rfl
  · exact neg_nonpos.mpr (Real.log_natCast_nonneg _)
  · exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.log_natCast_nonneg _))
        (Real.log_natCast_nonneg _)) hL.le
  · exact le_rfl

/-- The complete extreme-rough coefficient vanishes for every saturated
composite core at the actual physical cutoff, including equality at either edge. -/
theorem coefficient_eq_zero_of_physical_extreme {u : ℝ} {N a b : ℕ}
    (hfull : Squarefree (b * a)) (ha1 : a ≠ 1) (hap : ¬ a.Prime)
    (haX : a ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hlarge : ∀ p ∈ b.primeFactors,
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p) :
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) (b * a) = 0 := by
  apply coefficient_eq_zero_of_extreme_composite hfull ha1 hap
  · apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hfull.of_mul_right.ne_zero)
    exact_mod_cast haX
  · intro p hp
    apply Real.log_le_log (by positivity)
    exact_mod_cast hlarge p hp

/-- A nonzero saturated composite core forces a genuine rough prime
strictly below the physical cutoff. The other rough primes remain coupled. -/
theorem nonzero_composite_core_has_subcutoff_prime {u : ℝ} {N a b : ℕ}
    (hfull : Squarefree (b * a)) (ha1 : a ≠ 1) (hap : ¬ a.Prime)
    (haX : a ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hc : SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) (b * a) ≠ 0) :
    ∃ p ∈ b.primeFactors, p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 := by
  by_contra! h
  exact hc (coefficient_eq_zero_of_physical_extreme hfull ha1 hap haX h)

/-- Every nonzero surviving integer has a complete smooth/rough
factorization whose small core is a unit, a prime, or is coupled to an actual
intermediate rough prime. No factorization or source-limit premise is assumed. -/
theorem surviving_support_core_or_intermediate {u : ℝ} {N n : ℕ}
    (hn : n ∈ ZetaRieszLargeSmoothDeletion.largeSmoothResidualBand u N)
    (hc : SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n ≠ 0) :
    ∃ a b : ℕ, Squarefree a ∧ (∀ p ∈ a.primeFactors, p ≤ N ^ 2) ∧
      Squarefree b ∧ (∀ p ∈ b.primeFactors, N ^ 2 < p) ∧ n = b * a ∧
      a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ∧
      (a = 1 ∨ a.Prime ∨ ∃ p : ℕ, p.Prime ∧ p ∣ b ∧ N ^ 2 < p ∧
        p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) := by
  obtain ⟨a, b, ha, hsmall, hb, hrough, he, haX⟩ :=
    ZetaRieszLargeSmoothDeletion.surviving_support_with_small_smooth_factor hn hc
  refine ⟨a, b, ha, hsmall, hb, hrough, he, haX, ?_⟩
  by_cases ha1 : a = 1
  · exact Or.inl ha1
  by_cases hap : a.Prime
  · exact Or.inr (Or.inl hap)
  have hc' : SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) (b * a) ≠ 0 :=
    he ▸ hc
  have hfull : Squarefree (b * a) := by
    by_contra h
    exact hc' (by simp [SquarefreeVaughanLogSource.coefficient, h])
  obtain ⟨p, hp, hpx⟩ := nonzero_composite_core_has_subcutoff_prime hfull ha1 hap haX.le hc'
  exact Or.inr (Or.inr ⟨p, (Nat.mem_primeFactors.mp hp).1,
    (Nat.mem_primeFactors.mp hp).2.1, hrough p hp, hpx⟩)

end
end RiemannGaussian.ZetaRieszExtremePrimeProfile
