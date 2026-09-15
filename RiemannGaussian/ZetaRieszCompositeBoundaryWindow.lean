/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszExtremePrimeProfile

/-!
# Signed composite-core boundary divisor windows

The exact coefficient is a complete signed divisor sum in the strict
physical window X/a<d<X. Every other divisor contributes zero. Arbitrary
intermediate and extreme prime counts remain, together with the total
integer, common length and original coefficient. No signed-floor estimate
is assumed or concluded.
-/

namespace RiemannGaussian.ZetaRieszCompositeBoundaryWindow
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszExtremePrimeProfile

/-- A single intermediate prime acts by a cutoff difference even
after any number of extreme primes have been inserted. The saturated
composite core contributes no unshifted term. -/
theorem riesz_one_intermediate_composite {a b p : ℕ} {L : ℝ}
    (hfull : Squarefree (b * (p * a))) (hp : p.Prime)
    (ha1 : a ≠ 1) (hap : ¬ a.Prime) (haL : Real.log a ≤ L)
    (hlarge : ∀ r ∈ b.primeFactors, L ≤ Real.log r) :
    VaughanLogAverage.riesz L (b * (p * a)) =
      -VaughanLogAverage.riesz (L - Real.log p) a := by
  have hpa : Squarefree (p * a) := hfull.of_mul_right
  have hnd : ¬ p ∣ a := hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hpa)
  rw [riesz_mul_eq_of_extreme_rough hfull hlarge,
    ZetaSquarefreeRieszWindows.riesz_prime_mul L hp hnd,
    ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated hpa.of_mul_right ha1 hap haL, zero_sub]

/-- The exact original coefficient retains the sign of the shifted
composite-core profile. All extreme primes remain in the total logarithm
and in the downstream oscillatory kernel. -/
theorem coefficient_one_intermediate_composite {a b p : ℕ} {L : ℝ}
    (hfull : Squarefree (b * (p * a))) (hp : p.Prime)
    (ha1 : a ≠ 1) (hap : ¬ a.Prime) (haL : Real.log a ≤ L)
    (hlarge : ∀ r ∈ b.primeFactors, L ≤ Real.log r) :
    SquarefreeVaughanLogSource.coefficient L (b * (p * a)) =
      ((Real.log (b * (p * a) : ℕ) * VaughanLogAverage.riesz (L - Real.log p) a / L : ℝ) : ℂ) := by
  have hb0 : 0 < b := Nat.pos_of_ne_zero hfull.of_mul_left.ne_zero
  have hbp : b * p ≠ 1 := by nlinarith [hp.two_le]
  have hn : ¬ (b * (p * a)).Prime := by
    rw [← Nat.mul_assoc]
    exact Nat.not_prime_mul hbp ha1
  rw [SquarefreeVaughanLogSource.coefficient, if_pos ⟨hfull, hn⟩,
    riesz_one_intermediate_composite hfull hp ha1 hap haL hlarge]
  congr 1
  ring

/-- The one-intermediate-prime coefficient can be nonzero only
inside the exact multiplicative boundary window X/a < p < X. Both
endpoints vanish; all extreme primes are still present in the integer. -/
theorem nonzero_one_intermediate_in_window {u : ℝ} {N a b p : ℕ}
    (hfull : Squarefree (b * (p * a))) (hp : p.Prime)
    (ha1 : a ≠ 1) (hap : ¬ a.Prime)
    (haX : a ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hlarge : ∀ r ∈ b.primeFactors,
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ r)
    (hc : SquarefreeVaughanLogSource.coefficient
      (SquarefreeVaughanLogSource.length u N) (b * (p * a)) ≠ 0) :
    p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ∧
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < p * a := by
  have hlargeL (r : ℕ) (hr : r ∈ b.primeFactors) :
      SquarefreeVaughanLogSource.length u N ≤ Real.log r := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hlarge r hr
  have haL : Real.log a ≤ SquarefreeVaughanLogSource.length u N := by
    apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hfull.of_mul_right.of_mul_right.ne_zero)
    exact_mod_cast haX
  constructor
  · by_contra h
    have hpL : SquarefreeVaughanLogSource.length u N ≤ Real.log p := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast le_of_not_gt h
    apply hc
    rw [coefficient_one_intermediate_composite hfull hp ha1 hap haL hlargeL,
      ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos (sub_nonpos.mpr hpL)]
    simp
  · by_contra h
    apply hc
    apply coefficient_eq_zero_of_physical_extreme hfull
    · have ha0 : 0 < a := Nat.pos_of_ne_zero hfull.of_mul_right.of_mul_right.ne_zero
      nlinarith [hp.two_le]
    · exact Nat.not_prime_mul hp.ne_one ha1
    · exact le_of_not_gt h
    · exact hlarge

/-- For a composite squarefree core, every divisor outside the exact
cutoff boundary window vanishes. The complete signed divisor sum is
retained inside that window, with no restriction on the other factor. -/
theorem riesz_composite_eq_divisor_window {a q : ℕ} (L : ℝ)
    (hfull : Squarefree (q * a)) (ha1 : a ≠ 1) (hap : ¬ a.Prime) :
    VaughanLogAverage.riesz L (q * a) =
      ∑ d ∈ q.divisors.filter (fun d => L < Real.log (d * a : ℕ) ∧ Real.log d < L),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          VaughanLogAverage.riesz (L - Real.log d) a := by
  rw [ZetaSquarefreeRieszWindows.riesz_coprime_mul L (Nat.coprime_of_squarefree_mul hfull)]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro d hd hnot
  have hwindow : ¬ (L < Real.log (d * a : ℕ) ∧ Real.log d < L) := by
    intro h
    exact hnot (Finset.mem_filter.mpr ⟨hd, h⟩)
  by_cases hupper : Real.log d < L
  · have hprod : Real.log (d * a : ℕ) ≤ L :=
      le_of_not_gt (fun h => hwindow ⟨h, hupper⟩)
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast hfull.of_mul_right.ne_zero
    rw [Nat.cast_mul, Real.log_mul hd0 ha0] at hprod
    rw [ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated hfull.of_mul_right ha1 hap (by linarith),
      mul_zero]
  · rw [ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos (sub_nonpos.mpr (le_of_not_gt hupper)), mul_zero]

/-- All extreme primes can be retained in the total integer while
the exact signed Riesz profile is restricted to divisors of the remaining
factor in one multiplicative boundary window. -/
theorem riesz_extreme_composite_eq_divisor_window {a b q : ℕ} {L : ℝ}
    (hfull : Squarefree (b * (q * a))) (ha1 : a ≠ 1) (hap : ¬ a.Prime)
    (hlarge : ∀ p ∈ b.primeFactors, L ≤ Real.log p) :
    VaughanLogAverage.riesz L (b * (q * a)) =
      ∑ d ∈ q.divisors.filter (fun d => L < Real.log (d * a : ℕ) ∧ Real.log d < L),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          VaughanLogAverage.riesz (L - Real.log d) a := by
  rw [riesz_mul_eq_of_extreme_rough hfull hlarge]
  exact riesz_composite_eq_divisor_window L hfull.of_mul_right ha1 hap

/-- The actual original coefficient is the exact signed boundary
divisor sum after extreme-prime elimination. Its total logarithm is kept;
the sum has not been replaced by a divisor-count majorant. -/
theorem coefficient_extreme_composite_eq_divisor_window {a b q : ℕ} {L : ℝ}
    (hfull : Squarefree (b * (q * a))) (ha1 : a ≠ 1) (hap : ¬ a.Prime)
    (hlarge : ∀ p ∈ b.primeFactors, L ≤ Real.log p) :
    SquarefreeVaughanLogSource.coefficient L (b * (q * a)) =
      ((-Real.log (b * (q * a) : ℕ) / L *
        ∑ d ∈ q.divisors.filter (fun d => L < Real.log (d * a : ℕ) ∧ Real.log d < L),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            VaughanLogAverage.riesz (L - Real.log d) a : ℝ) : ℂ) := by
  have hn : ¬ (b * (q * a)).Prime := by
    intro hn
    have hd : a ∣ b * (q * a) := dvd_mul_of_dvd_right (dvd_mul_left a q) b
    rcases (Nat.dvd_prime hn).mp hd with h | h
    · exact ha1 h
    · exact hap (h ▸ hn)
  rw [SquarefreeVaughanLogSource.coefficient, if_pos ⟨hfull, hn⟩,
    riesz_extreme_composite_eq_divisor_window hfull ha1 hap hlarge]
  congr 1
  ring

/-- The actual positive physical cutoff transports strict lower
logarithmic inequalities to strict inequalities of integers. -/
theorem physical_log_lt_iff (u : ℝ) (N : ℕ) {m : ℕ} (hm : 0 < m) :
    SquarefreeVaughanLogSource.length u N < Real.log m ↔
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < m := by
  unfold SquarefreeVaughanLogSource.length
  rw [Real.log_lt_log_iff (by positivity) (by exact_mod_cast hm)]
  norm_cast

/-- The upper edge of the actual logarithmic cutoff is also
strict, with the full integer floor retained. -/
theorem log_lt_physical_iff (u : ℝ) (N : ℕ) {m : ℕ} (hm : 0 < m) :
    Real.log m < SquarefreeVaughanLogSource.length u N ↔
      m < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 := by
  unfold SquarefreeVaughanLogSource.length
  rw [Real.log_lt_log_iff (by exact_mod_cast hm) (by positivity)]
  norm_cast

/-- The signed logarithmic window equals the literal integer
product window, including both strict cutoff edges. -/
theorem divisor_window_eq_physical (u : ℝ) (N q : ℕ) {a : ℕ} (ha : 0 < a) :
    q.divisors.filter (fun d => SquarefreeVaughanLogSource.length u N < Real.log (d * a : ℕ) ∧
      Real.log d < SquarefreeVaughanLogSource.length u N) =
    q.divisors.filter (fun d => (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < d * a ∧
      d < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) := by
  ext d
  by_cases hd : d ∈ q.divisors
  · have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    simp only [Finset.mem_filter, hd, true_and]
    rw [physical_log_lt_iff u N (Nat.mul_pos hd0 ha), log_lt_physical_iff u N hd0]
  · simp only [Finset.mem_filter, hd, false_and]

/-- An exact integer-window formula for the actual physical
coefficient, with arbitrary intermediate and extreme factors and every
Möbius sign retained. No source theorem or asymptotic limit is used. -/
theorem coefficient_extreme_composite_eq_physical_window {u : ℝ} {N a b q : ℕ}
    (hfull : Squarefree (b * (q * a))) (ha1 : a ≠ 1) (hap : ¬ a.Prime)
    (hlarge : ∀ p ∈ b.primeFactors,
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p) :
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) (b * (q * a)) =
      ((-Real.log (b * (q * a) : ℕ) / SquarefreeVaughanLogSource.length u N *
        ∑ d ∈ q.divisors.filter (fun d =>
          (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < d * a ∧
          d < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N - Real.log d) a : ℝ) : ℂ) := by
  have hlargeL (p : ℕ) (hp : p ∈ b.primeFactors) :
      SquarefreeVaughanLogSource.length u N ≤ Real.log p := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hlarge p hp
  rw [coefficient_extreme_composite_eq_divisor_window hfull ha1 hap hlargeL,
    divisor_window_eq_physical u N q (Nat.pos_of_ne_zero hfull.of_mul_right.of_mul_right.ne_zero)]

end
end RiemannGaussian.ZetaRieszCompositeBoundaryWindow
