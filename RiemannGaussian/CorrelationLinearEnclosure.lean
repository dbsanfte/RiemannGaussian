/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Linear enclosures that keep shared-input correlations

Independent ranges for many correlations discard first-order cancellation
near a minimizing configuration. A derivative enclosure retains a common
linear term, with an explicit error. Summing those terms before taking their
absolute values preserves cancellation across all the pair distances.
-/

namespace RiemannGaussian.CorrelationLinearEnclosure
noncomputable section
open Set
open scoped BigOperators

/-- A derivative interval gives an affine approximation with a paid error.
The center, interval endpoints and radius are all explicit. -/
theorem error_from_derivative {f : ℝ → ℝ} {a b m x d E r : ℝ}
    (hf : ∀ z ∈ Icc a b, DifferentiableAt ℝ f z)
    (hder : ∀ z ∈ Icc a b, |deriv f z - d| ≤ E)
    (hm : m ∈ Icc a b) (hx : x ∈ Icc a b)
    (hE : 0 ≤ E) (hr : |x - m| ≤ r) :
    |f x - f m - d * (x - m)| ≤ E * r := by
  let g : ℝ → ℝ := fun z => f z - d * z
  have hd : ∀ z ∈ Icc a b, HasDerivAt g (deriv f z - d) z := by
    intro z hz
    convert (hf z hz).hasDerivAt.sub ((hasDerivAt_id z).const_mul d) using 1 <;>
      first | rfl | simp only [mul_one]
  have h := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hd z hz).hasDerivWithinAt)
    (fun z hz => by simpa only [Real.norm_eq_abs] using hder z hz) hm hx
  simp only [Real.norm_eq_abs] at h
  have hid : g x - g m = f x - f m - d * (x - m) := by dsimp [g]; ring
  rw [hid] at h
  exact h.trans (mul_le_mul_of_nonneg_left hr hE)

/-- A lower bound at the center turns the affine enclosure into a lower
line valid on the complete interval. -/
theorem lower_from_derivative {f : ℝ → ℝ} {a b m x d E r v : ℝ}
    (hf : ∀ z ∈ Icc a b, DifferentiableAt ℝ f z)
    (hder : ∀ z ∈ Icc a b, |deriv f z - d| ≤ E)
    (hm : m ∈ Icc a b) (hx : x ∈ Icc a b)
    (hE : 0 ≤ E) (hr : |x - m| ≤ r) (hv : v ≤ f m) :
    v + d * (x - m) - E * r ≤ f x := by
  have h := error_from_derivative hf hder hm hx hE hr
  linarith [(abs_le.mp h).1]

/-- Collect the whole gradient before taking absolute values. This is the
shared-input identity used by the finite window checker. -/
theorem sum_linear_forms {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → ℝ) (a : ι → κ → ℝ) (u : κ → ℝ) :
    (∑ i, c i * ∑ j, a i j * u j) =
      ∑ j, (∑ i, c i * a i j) * u j := by
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_mul]

/-- An entire box is certified by its accumulated gradient and coordinate
radii. Opposing gradient contributions cancel before the radius cost. -/
theorem lower_sum_linear_forms {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → ℝ) (a : ι → κ → ℝ) (u r : κ → ℝ)
    (hr : ∀ j, |u j| ≤ r j) :
    -(∑ j, |∑ i, c i * a i j| * r j) ≤
      ∑ i, c i * ∑ j, a i j * u j := by
  rw [sum_linear_forms, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro j _
  have h : |(∑ i, c i * a i j) * u j| ≤ |∑ i, c i * a i j| * r j := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hr j) (abs_nonneg _)
  exact (abs_le.mp h).1

end
end RiemannGaussian.CorrelationLinearEnclosure
