/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaNearOneLineBudget
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Complete near-one power bounds for the actual Riemann zeta function

Every balanced line has the classical derivative-test height exponent,
uniformly above absolute height two. The coefficient is deliberately
coarse, and the eta division cost remains explicit as `1 / (1 - sigma)`.
The theorem has no finite-budget, tail, or derivative-selection premise.
It provides an input to zero detection, not a new zero-free region.
-/

namespace RiemannGaussian.ZetaNearOneLineBound
noncomputable section
open DerivativePowerExponents DirichletPowerParameters DerivativeOrderComparison
open ZetaDyadicTruncation ZetaDyadicPowerBound ZetaNearOneLineBudget
open scoped ComplexConjugate

/-- At every positive balanced derivative index, the full zeta function
has the sharp height exponent with an explicit logarithm and eta cost. -/
theorem bound (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hline : s.re = line k)
    (ht : 2 ≤ s.im) :
    ‖riemannZeta s‖ ≤ 32768 * s.im ^ alpha k * Real.log s.im / (1 - s.re) := by
  have hσhalf : 1 / 2 ≤ s.re := by rw [hline]; exact half_le_line k hk
  have hσ : 0 < s.re := by linarith
  have hσ1 : s.re < 1 := by rw [hline]; exact line_lt_one k
  have htpos : 0 < s.im := by linarith
  obtain ⟨orders, _, hb⟩ := exists_prefix_budget_bound k hk hline ht
  have hc := canonical_count_le hσ.le hσ1.le ht
  have hp : 1 ≤ s.im ^ alpha k := Real.one_le_rpow (by linarith) (alpha_pos k).le
  have hd : 1 ≤ ((depth s + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hone : 1 ≤ ((depth s + 1 : ℕ) : ℝ) * s.im ^ alpha k := by
    have h := mul_le_mul_of_nonneg_left hp
      (show 0 ≤ ((depth s + 1 : ℕ) : ℝ) by positivity)
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hc (by linarith : 0 ≤ s.im ^ alpha k)
  have hlog : 0 ≤ Real.log s.im := (Real.log_pos (by linarith : 1 < s.im)).le
  have hprod : 0 ≤ s.im ^ alpha k * Real.log s.im := mul_nonneg (by linarith) hlog
  apply (simple_bound hσ hσ1 htpos orders).trans
  apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ 1 - s.re)
  nlinarith

/-- Conjugation gives the same complete line bound at both signs of
the height, with no exceptional ordinate above absolute height two. -/
theorem bound_abs (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hline : s.re = line k)
    (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 32768 * |s.im| ^ alpha k * Real.log |s.im| / (1 - s.re) := by
  by_cases hs : 0 ≤ s.im
  · rw [abs_of_nonneg hs] at ht ⊢
    exact bound k hk hline ht
  · have hsneg : s.im < 0 := lt_of_not_ge hs
    have hline' : (conj s).re = line k := by simpa using hline
    have ht' : 2 ≤ (conj s).im := by simpa [abs_of_neg hsneg] using ht
    have h := bound k hk hline' ht'
    simpa [abs_of_neg hsneg] using h

/-- The same bound in displacement coordinates exposes the full
order dependence of the eta division cost. -/
theorem bound_displacement (k : ℕ) (hk : 1 ≤ k) {s : ℂ}
    (hline : s.re = line k) (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤
      32768 * |s.im| ^ alpha k * Real.log |s.im| / delta k := by
  rw [delta_eq_one_sub_line, ← hline]
  exact bound_abs k hk hline ht

end
end RiemannGaussian.ZetaNearOneLineBound
