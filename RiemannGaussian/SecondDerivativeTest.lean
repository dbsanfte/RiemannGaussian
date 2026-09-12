/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.DiscreteSecondDerivativeTest
import RiemannGaussian.SecondDerivativeIncrements

/-!
# A second-derivative exponential-sum test covering every resonance

Positive two-sided curvature bounds on the actual closed phase domain
control the whole finite sum. No resonance-avoidance condition or bound
on the first derivative is assumed. Exact discrete increments and the
complete resonance partition discharge those issues inside the proof.

The allowance is free in the main theorem. For curvature at most one,
its exact square root gives the classical `N*sqrt(ell) + 1/sqrt(ell)`
scale when the ratio between upper and lower curvature is bounded.
Constants are deliberately coarse; this is classical mathematics.
-/

namespace RiemannGaussian.SecondDerivativeTest
noncomputable section
open PhaseIncrementInverse

/-- A complete second-derivative bound with a freely chosen resonance
allowance. Every analytic hypothesis is on the original closed domain. -/
theorem bound (f f' f'' : ℝ → ℝ) (a : ℝ) (N : ℕ) {η ℓ U : ℝ}
    (hη : 0 < η) (hηπ : η ≤ Real.pi) (hℓ : 0 < ℓ) (hU : 0 ≤ U)
    (hd : ∀ x ∈ Set.Icc a (a + N), HasDerivAt f (f' x) x)
    (hd' : ∀ x ∈ Set.Icc a (a + N), HasDerivAt f' (f'' x) x)
    (hr : ∀ x ∈ Set.Icc a (a + N), ℓ ≤ f'' x ∧ f'' x ≤ U) :
    ‖∑ n ∈ Finset.range N, rotation (f (a + n))‖ ≤
      (U * N / (2 * Real.pi) + 2) * (2 * η / ℓ + 1 + 2 * Real.pi / η) := by
  apply DiscreteSecondDerivativeTest.bound _ N hη hηπ hℓ hU
  · intro i _ j hj hij
    exact (SecondDerivativeIncrements.increment_gap_bounds f f' f'' a N hd hd' hr hj hij).1
  · intro i _ j hj hij
    exact (SecondDerivativeIncrements.increment_gap_bounds f f' f'' a N hd hd' hr hj hij).2

/-- Choosing the exact square root of the lower curvature gives the
usual second-derivative scale, with the curvature ratio explicit. -/
theorem square_root_bound (f f' f'' : ℝ → ℝ) (a : ℝ) (N : ℕ) {ℓ A : ℝ}
    (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hA : 0 ≤ A)
    (hd : ∀ x ∈ Set.Icc a (a + N), HasDerivAt f (f' x) x)
    (hd' : ∀ x ∈ Set.Icc a (a + N), HasDerivAt f' (f'' x) x)
    (hr : ∀ x ∈ Set.Icc a (a + N), ℓ ≤ f'' x ∧ f'' x ≤ A * ℓ) :
    ‖∑ n ∈ Finset.range N, rotation (f (a + n))‖ ≤
      (A * N * Real.sqrt ℓ / (2 * Real.pi) + 2 / Real.sqrt ℓ) *
        (3 + 2 * Real.pi) := by
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ
  have hs1 : Real.sqrt ℓ ≤ 1 := Real.sqrt_le_one.mpr hℓ1
  have hsπ : Real.sqrt ℓ ≤ Real.pi := hs1.trans (by linarith [Real.two_le_pi])
  have hs2 := Real.sq_sqrt hℓ.le
  have h := bound f f' f'' a N hs hsπ hℓ (mul_nonneg hA hℓ.le) hd hd' hr
  have hi : 2 * Real.sqrt ℓ / ℓ + 1 + 2 * Real.pi / Real.sqrt ℓ ≤
      (3 + 2 * Real.pi) / Real.sqrt ℓ := by
    apply (le_div_iff₀ hs).mpr
    have he : (2 * Real.sqrt ℓ / ℓ + 1 + 2 * Real.pi / Real.sqrt ℓ) * Real.sqrt ℓ =
        2 + Real.sqrt ℓ + 2 * Real.pi := by
      field_simp
      nlinarith [hs2]
    rw [he]
    linarith
  have he : (A * ℓ * N / (2 * Real.pi) + 2) *
      ((3 + 2 * Real.pi) / Real.sqrt ℓ) =
        (A * N * Real.sqrt ℓ / (2 * Real.pi) + 2 / Real.sqrt ℓ) *
          (3 + 2 * Real.pi) := by
    field_simp
    rw [hs2]
    ring
  exact (h.trans (mul_le_mul_of_nonneg_left hi (by positivity))).trans_eq he

end
end RiemannGaussian.SecondDerivativeTest
