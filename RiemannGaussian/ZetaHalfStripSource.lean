/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaAdaptiveSigned

/-!
# A signed source from every zero right of the critical line

The adaptive disc encloses any selected actual zero with real part greater
than one half. Its complete canonical source is retained, and a proved
positive lower bound exposes the distance from the critical line explicitly.
The other zeros' negative canonical responses are paid by their genuine
Jensen weights, with a uniform logarithmic allowance.

This removes the earlier three-quarter restriction from the source
inequality. The independent arithmetic improvement needed for a
contradiction remains unproved.
-/

open Complex Filter MeasureTheory MeromorphicOn Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The inner radius lies halfway between the selected zero's distance
from the safe center and the unit circle tangent to the critical line. -/
def zetaRightHalfDiscParameter (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Set.Ico (3 / 4 : ℝ) 1 :=
  ⟨5 / 4 - rho.1.re / 2, by
    constructor
    · linarith [NontrivialZetaZero.re_lt_one rho]
    · linarith⟩

/-- Every actual zero right of the critical line is strictly inside its
selected adaptive canonical disc. -/
theorem nontrivialZero_mem_adaptiveCanonicalBall (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ((rho.1.re - 3 / 2 : ℝ) : ℂ) ∈
      ball 0 (adaptiveZetaCanonicalRadius (zetaRightHalfDiscParameter rho hrho) rho.1.im) := by
  rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith [NontrivialZetaZero.re_lt_one rho])]
  have h := (adaptiveZetaCanonicalRadius_spec (zetaRightHalfDiscParameter rho hrho) rho.1.im).1
  change 5 / 4 - rho.1.re / 2 < _ at h
  linarith

/-- The adaptive divisor records the selected actual zero's full
analytic multiplicity throughout the right half of the critical strip. -/
theorem divisor_adaptiveZetaPoleRemoved_nontrivialZero (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    divisor (localZetaPoleRemoved rho.1.im)
      (ball 0 (adaptiveZetaCanonicalRadius (zetaRightHalfDiscParameter rho hrho) rho.1.im))
      ((rho.1.re - 3 / 2 : ℝ) : ℂ) = (analyticZetaZeroMultiplicity rho : ℤ) := by
  have hmem := nontrivialZero_mem_adaptiveCanonicalBall rho hrho
  rw [((analyticOnNhd_adaptiveZetaPoleRemoved_canonicalDisc
    (zetaRightHalfDiscParameter rho hrho) rho.1.im).mono ball_subset_closedBall).meromorphicOn.divisor_apply hmem]
  have hf : localZetaPoleRemoved rho.1.im = riemannZeta₁ ∘ (· + (3 / 2 + I * (rho.1.im : ℂ))) := by
    funext z
    simp only [localZetaPoleRemoved, Function.comp_def, add_comm z]
  rw [hf, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
  have he : ((rho.1.re - 3 / 2 : ℝ) : ℂ) + (3 / 2 + I * (rho.1.im : ℂ)) = rho.1 := by
    apply Complex.ext <;> simp
  rw [he, meromorphicOrderAt_riemannZeta₁_nontrivialZero]
  simp

/-- The actual logarithmic derivative retains the complete signed source
of every selected zero right of the critical line. -/
theorem neg_logDeriv_add_halfStripCanonicalSource_le (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    (-logDeriv riemannZeta (((1 + x : ℝ) : ℂ) + I * rho.1.im)).re +
      (analyticZetaZeroMultiplicity rho : ℝ) *
        (zetaCanonicalZeroResponse
          (adaptiveZetaCanonicalRadius (zetaRightHalfDiscParameter rho hrho) rho.1.im)
          ((rho.1.re - 3 / 2 : ℝ) : ℂ) ((x - 1 / 2 : ℝ) : ℂ)).re ≤
      x / (x ^ 2 + rho.1.im ^ 2) + 448 * localZetaLogHeight rho.1.im := by
  have h := neg_logDeriv_add_adaptive_divisor_source_le (zetaRightHalfDiscParameter rho hrho)
    rho.1.im hx hx1 ((rho.1.re - 3 / 2 : ℝ) : ℂ)
  rw [divisor_adaptiveZetaPoleRemoved_nontrivialZero rho hrho, Int.cast_natCast] at h
  exact h

private theorem canonical_real_response (R u v : ℝ) :
    (zetaCanonicalZeroResponse R (-(u : ℂ)) v).re = 1 / (v + u) - u / (R ^ 2 + u * v) := by
  have he : zetaCanonicalZeroResponse R (-(u : ℂ)) v =
      ((1 / (v + u) - u / (R ^ 2 + u * v) : ℝ) : ℂ) := by
    unfold zetaCanonicalZeroResponse
    push_cast
    simp
    ring
  rw [he, Complex.ofReal_re]

private theorem canonical_real_response_lower {R u v : ℝ}
    (hu : (1 / 2 : ℝ) < u) (hu1 : u < 1) (hR : (1 + u) / 2 < R) (hR1 : R ≤ 1)
    (hvlo : -(1 / 2 : ℝ) < v) (hvhi : v ≤ 1 / 2) :
    (1 - u) / (3 * (v + u)) ≤ (zetaCanonicalZeroResponse R (-(u : ℂ)) v).re := by
  have hgap : 0 < v + u := by linarith
  have hRp : 0 < R := by linarith
  have hRsq : ((1 + u) / 2) ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ (by linarith) hR.le 2
  have hnum : (1 - u) / 2 ≤ R ^ 2 - u ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - u by linarith) (show 0 ≤ 3 * u - 1 by linarith)]
  have hdiff : 0 ≤ R ^ 2 - u ^ 2 := by linarith
  have huvlo := mul_le_mul_of_nonneg_left hvlo.le (by linarith : 0 ≤ u)
  have huvhi := mul_le_mul_of_nonneg_left hvhi (by linarith : 0 ≤ u)
  have hden : 0 < R ^ 2 + u * v := by nlinarith
  have hdenhi : R ^ 2 + u * v ≤ 3 / 2 := by nlinarith
  have he : (zetaCanonicalZeroResponse R (-(u : ℂ)) v).re =
      (R ^ 2 - u ^ 2) / ((v + u) * (R ^ 2 + u * v)) := by
    rw [canonical_real_response]
    rw [div_sub_div _ _ hgap.ne' hden.ne']
    congr 1
    ring
  rw [he]
  calc
    _ = ((1 - u) / 2) / ((v + u) * (3 / 2)) := by
      rw [div_div]
      congr 1
      ring
    _ ≤ (R ^ 2 - u ^ 2) / ((v + u) * (3 / 2)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left hdiff (mul_pos hgap hden)
      (mul_le_mul_of_nonneg_left hdenhi hgap.le)

/-- The complete selected source has an explicit positive lower bound
proportional to the actual distance from the critical line. -/
theorem halfStripCanonicalSource_lower (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    (rho.1.re - 1 / 2) / (3 * (x + 1 - rho.1.re)) ≤
      (zetaCanonicalZeroResponse
        (adaptiveZetaCanonicalRadius (zetaRightHalfDiscParameter rho hrho) rho.1.im)
        ((rho.1.re - 3 / 2 : ℝ) : ℂ) ((x - 1 / 2 : ℝ) : ℂ)).re := by
  have hR := (adaptiveZetaCanonicalRadius_spec (zetaRightHalfDiscParameter rho hrho) rho.1.im).1
  change 5 / 4 - rho.1.re / 2 < _ at hR
  have h := canonical_real_response_lower (u := 3 / 2 - rho.1.re) (v := x - 1 / 2)
    (by linarith [NontrivialZetaZero.re_lt_one rho]) (by linarith)
    (by linarith : (1 + (3 / 2 - rho.1.re)) / 2 <
      adaptiveZetaCanonicalRadius (zetaRightHalfDiscParameter rho hrho) rho.1.im)
    (adaptiveZetaCanonicalRadius_spec (zetaRightHalfDiscParameter rho hrho) rho.1.im).2.1.le
    (by linarith) (by linarith)
  have he1 : 1 - (3 / 2 - rho.1.re) = rho.1.re - 1 / 2 := by ring
  have he2 : (x - 1 / 2) + (3 / 2 - rho.1.re) = x + 1 - rho.1.re := by ring
  have he3 : -((3 / 2 - rho.1.re : ℝ) : ℂ) = ((rho.1.re - 3 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rwa [he1, he2, he3] at h

/-- Every actual zero strictly right of the critical line contributes
its full multiplicity times a positive source. The signed inequality holds
with the same uniform logarithmic allowance and for every shift up to one. -/
theorem neg_logDeriv_add_halfStripSource_le (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    (-logDeriv riemannZeta (((1 + x : ℝ) : ℂ) + I * rho.1.im)).re +
      (analyticZetaZeroMultiplicity rho : ℝ) * (rho.1.re - 1 / 2) /
        (3 * (x + 1 - rho.1.re)) ≤
      x / (x ^ 2 + rho.1.im ^ 2) + 448 * localZetaLogHeight rho.1.im := by
  have h := neg_logDeriv_add_halfStripCanonicalSource_le rho hrho hx hx1
  have hl := mul_le_mul_of_nonneg_left (halfStripCanonicalSource_lower rho hrho hx hx1)
    (show (0 : ℝ) ≤ analyticZetaZeroMultiplicity rho by positivity)
  rw [← mul_div_assoc] at hl
  linarith

end

end RiemannGaussian
