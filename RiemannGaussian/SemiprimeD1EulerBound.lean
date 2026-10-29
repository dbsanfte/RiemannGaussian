/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! # A finite Euler bound for weighted mode acquisition
The bound is uniform in the aspect ratio between mode multiplicity and working
precision. Optimizing the positive parameter gives a square-root exponent;
a fixed dyadic evaluation alone would lose this in unbalanced original calls.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1EulerBound
open scoped BigOperators
open Filter

/-- A finite geometric tail is bounded by the reciprocal exponential scale. -/
theorem exponential_geometric_bound (t : ℝ) (K : ℕ) :
    t*(∑ j∈Finset.range K,Real.exp (-t)^(j+1))≤1 := by
  let q := Real.exp (-t)
  have hq : 0<q := Real.exp_pos _
  have hmul : Real.exp t*q=1 := by
    dsimp only [q]
    rw [← Real.exp_add]
    simp
  have hexp := mul_le_mul_of_nonneg_right (Real.add_one_le_exp t) hq.le
  have hnorm : t*q≤1-q := by nlinarith
  have hid (m : ℕ) :
      (1-q)*(∑ j∈Finset.range m,q^(j+1))=q-q^(m+1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ,mul_add,ih]
      simp only [pow_succ]
      ring
  have hs : 0≤∑ j∈Finset.range K,q^(j+1) := by positivity
  have hg : (1-q)*(∑ j∈Finset.range K,q^(j+1))≤q := by
    rw [hid]
    exact sub_le_self _ (pow_nonneg hq.le _)
  have h := (mul_le_mul_of_nonneg_right hnorm hs).trans hg
  by_contra hbad
  have hstrict := mul_lt_mul_of_pos_right (lt_of_not_ge hbad) hq
  nlinarith

/-- An elementary telescoping majorant avoids an infinite zeta-value assumption. -/
theorem reciprocal_square_bound (x : ℝ) (hx : 1≤x) :
    1/x^2≤2/x-2/(x+1) := by
  have hx0 : 0<x := by linarith
  have hx1 : 0<x+1 := by linarith
  have he : 2/x-2/(x+1)-1/x^2=(x-1)/(x^2*(x+1)) := by
    field_simp
    ring
  have hp : 0≤(x-1)/(x^2*(x+1)) :=
    div_nonneg (sub_nonneg.mpr hx) (by positivity)
  rw [←he] at hp
  linarith

/-- Every finite reciprocal-square sum is at most two, uniformly in its length. -/
theorem reciprocal_square_sum_le (J : ℕ) :
    (∑ n∈Finset.range J,1/((n:ℝ)+1)^2)≤2 := by
  have he (m : ℕ) :
      (∑ n∈Finset.range m,(2/((n:ℝ)+1)-2/((n:ℝ)+2)))=2-2/((m:ℝ)+1) := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [Finset.sum_range_succ,ih]
      push_cast
      ring
  calc
    _ ≤ ∑ n∈Finset.range J,(2/((n:ℝ)+1)-2/((n:ℝ)+2)) := by
      apply Finset.sum_le_sum
      intro n _
      simpa only [add_assoc,one_add_one_eq_two] using
        reciprocal_square_bound ((n:ℝ)+1) (by linarith [Nat.cast_nonneg (α := ℝ) n])
    _ = 2-2/((J:ℝ)+1) := he J
    _ ≤ 2 := sub_le_self _ (by positivity)

/-- One nonnegative row in the finite logarithmic power-series expansion. -/
noncomputable def row (alpha : ℝ) (K n : ℕ) : ℝ :=
  ∑ j∈Finset.range K,Real.exp (-alpha*((j:ℝ)+1))^(n+1)/((n:ℝ)+1)

/-- Each expanded row has a reciprocal-square majorant in its degree. -/
theorem row_le (alpha : ℝ) (ha : 0<alpha) (K n : ℕ) :
    row alpha K n≤(1/alpha)*(1/((n:ℝ)+1)^2) := by
  let t := alpha*((n:ℝ)+1)
  let S := ∑ j∈Finset.range K,Real.exp (-t)^(j+1)
  have ht : 0<t := mul_pos ha (by positivity)
  have hS : S≤1/t := by
    apply (le_div_iff₀ ht).mpr
    simpa only [one_mul,mul_comm] using exponential_geometric_bound t K
  have hp (j : ℕ) :
      Real.exp (-alpha*((j:ℝ)+1))^(n+1)=Real.exp (-t)^(j+1) := by
    rw [← Real.exp_nat_mul,← Real.exp_nat_mul]
    congr 1
    dsimp only [t]
    push_cast
    ring
  have hr : row alpha K n=S/((n:ℝ)+1) := by
    unfold row
    simp_rw [hp]
    rw [Finset.sum_div]
  calc
    _ = S/((n:ℝ)+1) := hr
    _ ≤ (1/t)/((n:ℝ)+1) := div_le_div_of_nonneg_right hS (by positivity)
    _ = (1/alpha)*(1/((n:ℝ)+1)^2) := by
      dsimp only [t]
      field_simp

/-- All expanded partial sums have one uniform bound. -/
theorem row_sum_le (alpha : ℝ) (ha : 0<alpha) (K J : ℕ) :
    (∑ n∈Finset.range J,row alpha K n)≤2/alpha := by
  calc
    _ ≤ ∑ n∈Finset.range J,(1/alpha)*(1/((n:ℝ)+1)^2) :=
      Finset.sum_le_sum (fun n _ => row_le alpha ha K n)
    _ = (1/alpha)*(∑ n∈Finset.range J,1/((n:ℝ)+1)^2) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (1/alpha)*2 := mul_le_mul_of_nonneg_left (reciprocal_square_sum_le J) (by positivity)
    _ = 2/alpha := by ring

/-- The finite Euler logarithm bound used by actual weighted-mode cardinality.
Only positivity of the freely optimized scale is assumed. -/
theorem euler_log_sum_le (alpha : ℝ) (ha : 0<alpha) (K : ℕ) :
    (∑ j∈Finset.range K,-Real.log (1-Real.exp (-alpha*((j:ℝ)+1))))≤2/alpha := by
  have hs (j : ℕ) :
      HasSum (fun n : ℕ => Real.exp (-alpha*((j:ℝ)+1))^(n+1)/((n:ℝ)+1))
        (-Real.log (1-Real.exp (-alpha*((j:ℝ)+1)))) := by
    apply Real.hasSum_pow_div_log_of_abs_lt_one
    rw [abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]
    have hp : 0<alpha*((j:ℝ)+1) := mul_pos ha (by positivity)
    linarith
  have hsum : HasSum (row alpha K)
      (∑ j∈Finset.range K,-Real.log (1-Real.exp (-alpha*((j:ℝ)+1)))) :=
    hasSum_sum (fun j _ => hs j)
  exact le_of_tendsto hsum.tendsto_sum_nat
    (Eventually.of_forall (fun J => row_sum_le alpha ha K J))

end RiemannGaussian.SemiprimeD1EulerBound
