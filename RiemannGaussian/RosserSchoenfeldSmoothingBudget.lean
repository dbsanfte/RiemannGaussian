/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldZeroFree
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The explicit large-argument smoothing budget

The concrete cutoff `T = exp(3*sqrt(log x)/8)` balances the proved
zero-free suppression and the complete high-zero tail. Exact rational
Taylor bounds pay every numerical anchor.
-/

namespace RiemannGaussian.RosserSchoenfeldSmoothingBudget
noncomputable section
open Real Set

private theorem pow_exp_le (n : ℕ) (hn : 1 ≤ n) {a r : ℝ}
    (ha : 0 < a) (hna : (n : ℝ) ≤ 70*a) (hr : 70 ≤ r) :
    r^n*exp (-a*r) ≤ 70^n*exp (-a*70) := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => y^n*exp (-a*y))
      (x^(n-1)*exp (-a*x)*((n : ℝ)-a*x)) x := by
    have hh := ((hasDerivAt_id x).fun_pow n).mul
      (((hasDerivAt_id x).const_mul (-a)).exp)
    apply hh.congr_deriv
    have hp : x^n = x^(n-1)*x := by rw [← pow_succ, Nat.sub_add_cancel hn]
    dsimp only [id_eq]
    rw [hp]
    ring
  have hanti : AntitoneOn (fun y : ℝ => y^n*exp (-a*y)) (Ici 70) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 70) (by fun_prop)
      (fun x _ => (hd x).hasDerivWithinAt)
    intro x hx
    have hx' : 70 ≤ x := interior_subset hx
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    nlinarith
  exact hanti (by simp) hr hr

private theorem first_anchor : (463/10000 : ℝ)*70^4*exp (-(4/15)*70) ≤ 9/1000 := by
  have he : (124000000 : ℝ) ≤ exp (56/3) := by
    apply le_trans _ (sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 56/3) 40)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [show -(4/15 : ℝ)*70 = -(56/3) by ring, exp_neg, ← div_eq_mul_inv]
  apply (div_le_div_of_nonneg_left (by positivity) (by norm_num) he).trans
  norm_num

private theorem second_anchor : ((3/4 : ℝ)*70^5+8*70^4)*exp (-(3/8)*70) ≤ 6/1000 := by
  have he : (243000000000 : ℝ) ≤ exp (105/4) := by
    apply le_trans _ (sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 105/4) 50)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [show -(3/8 : ℝ)*70 = -(105/4) by ring, exp_neg, ← div_eq_mul_inv]
  apply (div_le_div_of_nonneg_left (by positivity) (by norm_num) he).trans
  norm_num

private theorem third_anchor : (70 : ℝ)^4*exp (-70) ≤ 1/1600 := by
  have he : (100000000000 : ℝ) ≤ exp 70 := by
    apply le_trans _ (pow_div_factorial_le_exp 70 (by norm_num) 10)
    norm_num [Nat.factorial]
  rw [exp_neg, ← div_eq_mul_inv]
  apply (div_le_div_of_nonneg_left (by positivity) (by norm_num) he).trans
  norm_num

/-- The three explicit exponential allowances fit the fixed smoothing budget. -/
theorem exponential_budget {r : ℝ} (hr : 70 ≤ r) :
    (463/10000 : ℝ)*exp (-(4/15)*r)+(8+(3/4)*r)*exp (-(3/8)*r)+exp (-r^2) ≤
      1/(64*r^4) := by
  have hr0 : 0 < r := by linarith
  have h1 := mul_le_mul_of_nonneg_left
    (pow_exp_le 4 (by norm_num) (a := 4/15) (by norm_num) (by norm_num) hr)
    (by norm_num : (0 : ℝ) ≤ 463/10000)
  have h2 := mul_le_mul_of_nonneg_left
    (pow_exp_le 5 (by norm_num) (a := 3/8) (by norm_num) (by norm_num) hr)
    (by norm_num : (0 : ℝ) ≤ 3/4)
  have h3 := mul_le_mul_of_nonneg_left
    (pow_exp_le 4 (by norm_num) (a := 3/8) (by norm_num) (by norm_num) hr)
    (by norm_num : (0 : ℝ) ≤ 8)
  have h4 := pow_exp_le 4 (by norm_num) (a := 1) (by norm_num) (by norm_num) hr
  have hs : r^4*exp (-r^2) ≤ r^4*exp (-r) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply exp_le_exp.mpr
    nlinarith
  norm_num only [neg_mul, one_mul] at h4
  have ha := first_anchor
  have hb := second_anchor
  have hc := third_anchor
  apply (le_div_iff₀ (show 0 < 64*r^4 by positivity)).mpr
  nlinarith only [h1, h2, h3, h4, hs, ha, hb, hc]

/-- The fixed cutoff is in the domain of the complete tail estimate. -/
theorem cutoff_ge_two {r : ℝ} (hr : 70 ≤ r) : 2 ≤ exp ((3/8)*r) := by
  have hh := add_one_le_exp ((3/8)*r)
  linarith

/-- The proved signed-pole edge pays the concrete lower exponential rate. -/
theorem cutoff_margin {r : ℝ} (hr : 70 ≤ r) :
    (4/15)/r ≤ zetaSignedPoleZeroMargin (exp ((3/8)*r)) := by
  have hr0 : 0 < r := by linarith
  have hT := cutoff_ge_two hr
  have hl : log (exp ((3/8)*r)+2) ≤ (3/8)*r+1 := by
    calc
      _ ≤ log (2*exp ((3/8)*r)) := log_le_log (by positivity) (by linarith)
      _ = log 2+(3/8)*r := by rw [log_mul (by norm_num) (exp_pos _).ne', log_exp]
      _ ≤ _ := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  unfold zetaSignedPoleZeroMargin
  rw [abs_of_pos (exp_pos _)]
  have hd := zetaSignedPole_denominator_pos (exp ((3/8)*r))
  rw [abs_of_pos (exp_pos _)] at hd
  apply (div_le_div_iff₀ hr0 hd).mpr
  nlinarith

end
end RiemannGaussian.RosserSchoenfeldSmoothingBudget
