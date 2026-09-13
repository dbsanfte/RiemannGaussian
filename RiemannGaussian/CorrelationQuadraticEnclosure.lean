/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.CorrelationLinearEnclosure
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Retaining curvature in correlation enclosures

Individual second-derivative bounds yield a joint quadratic lower bound.
Its mixed terms can then be retained through a factorization and an exact
completion of squares. This avoids discarding a positive quadratic remainder
after proving convexity.
-/

namespace RiemannGaussian.CorrelationQuadraticEnclosure
noncomputable section
open Set
open scoped BigOperators

/-- A lower bound for the second derivative gives a global quadratic
support on a closed interval. The curvature bound may be negative. -/
theorem lower_from_second_derivative
    {f f' f'' : ℝ → ℝ} {a b m x c : ℝ}
    (hf : ∀ z ∈ Icc a b, HasDerivAt f (f' z) z)
    (hf' : ∀ z ∈ Icc a b, HasDerivAt f' (f'' z) z)
    (hc : ∀ z ∈ Icc a b, c ≤ f'' z)
    (hm : m ∈ Icc a b) (hx : x ∈ Icc a b) :
    f m + f' m * (x - m) + c / 2 * (x - m) ^ 2 ≤ f x := by
  let g : ℝ → ℝ := fun z => f z - c / 2 * z ^ 2
  let g' : ℝ → ℝ := fun z => f' z - c * z
  have hg : ∀ z ∈ Icc a b, HasDerivAt g (g' z) z := by
    intro z hz
    exact ((hf z hz).sub (((hasDerivAt_id z).pow 2).const_mul (c / 2))).congr_deriv
      (by dsimp [g']; ring)
  have hg' : ∀ z ∈ Icc a b, HasDerivAt g' (f'' z - c) z := by
    intro z hz
    exact ((hf' z hz).sub ((hasDerivAt_id z).const_mul c)).congr_deriv (by ring)
  have hconvex : ConvexOn ℝ (Icc a b) g :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b)
      (fun z hz => (hg z hz).continuousAt.continuousWithinAt)
      (fun z hz => (hg z (interior_subset hz)).hasDerivWithinAt)
      (fun z hz => (hg' z (interior_subset hz)).hasDerivWithinAt)
      (fun z hz => sub_nonneg.mpr (hc z (interior_subset hz)))
  rcases lt_trichotomy m x with hmx | hmx | hxm
  · have ht := hconvex.le_slope_of_hasDerivAt hm hx hmx (hg m hm)
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hmx)] at ht
    dsimp only [g, g'] at ht
    nlinarith
  · subst x
    simp
  · have ht := hconvex.slope_le_of_hasDerivAt hx hm hxm (hg m hm)
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hxm)] at ht
    dsimp only [g, g'] at ht
    nlinarith

/-- A two-sided second-derivative bound controls the signed linear
approximation at every point of the interval. -/
theorem error_from_second_derivative
    {f f' f'' : ℝ → ℝ} {a b m x M : ℝ}
    (hf : ∀ z ∈ Icc a b, HasDerivAt f (f' z) z)
    (hf' : ∀ z ∈ Icc a b, HasDerivAt f' (f'' z) z)
    (hc : ∀ z ∈ Icc a b, |f'' z| ≤ M)
    (hm : m ∈ Icc a b) (hx : x ∈ Icc a b) :
    |f x - f m - f' m * (x - m)| ≤ M / 2 * (x - m) ^ 2 := by
  have hlo := lower_from_second_derivative hf hf'
    (fun z hz => (abs_le.mp (hc z hz)).1) hm hx
  have hhi := lower_from_second_derivative
    (fun z hz => (hf z hz).neg) (fun z hz => (hf' z hz).neg)
    (c := -M) (fun z hz => by linarith [(abs_le.mp (hc z hz)).2]) hm hx
  simp only [Pi.neg_apply] at hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Exact completion of one positive quadratic square. -/
theorem linear_add_quadratic_lower {d z y : ℝ} (hd : 0 < d) :
    -(z ^ 2 / (2 * d)) ≤ z * y + d / 2 * y ^ 2 := by
  have hsq := sq_nonneg (d * y + z)
  apply (neg_le_iff_add_nonneg).mpr
  apply (nonneg_of_mul_nonneg_left (b := 2 * d))
  · field_simp [hd.ne']
    nlinarith
  · positivity

/-- A factorization pays the entire signed linear form using the inverse
quadratic energy. No individual coordinate is replaced by its absolute
value before the factors are combined. -/
theorem lower_from_factorized_quadratic {ι : Type*} [Fintype ι]
    (d z y : ι → ℝ) (hd : ∀ i, 0 < d i) {v F : ℝ}
    (hF : v + (∑ i, z i * y i) + (1 / 2 : ℝ) * (∑ i, d i * y i ^ 2) ≤ F) :
    v - (∑ i, z i ^ 2 / (2 * d i)) ≤ F := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun i _ => linear_add_quadratic_lower (z := z i) (y := y i) (hd i))
  simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib] at hsum
  have hid : (∑ i, d i / 2 * y i ^ 2) = (1 / 2 : ℝ) * (∑ i, d i * y i ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hid] at hsum
  linarith

end
end RiemannGaussian.CorrelationQuadraticEnclosure
