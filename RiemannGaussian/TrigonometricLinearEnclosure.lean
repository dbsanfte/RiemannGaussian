/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.CorrelationQuadraticEnclosure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Signed interpolation between certified phases

The linear term keeps the correlation between sine and cosine. The only
discarded part is a rigorously bounded quadratic Taylor remainder. In
particular a certified phase table controls arbitrary real anchors, not
merely a finite sample of phases.
-/

namespace RiemannGaussian.TrigonometricLinearEnclosure
noncomputable section
open Set

/-- Global second-order error for the signed sine tangent. -/
theorem sin_tangent_error (x m : ℝ) :
    |Real.sin x - Real.sin m - Real.cos m * (x - m)| ≤ (x - m) ^ 2 / 2 := by
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using
    CorrelationQuadraticEnclosure.error_from_second_derivative
      (a := min m x) (b := max m x) (M := 1)
      (fun z _ => Real.hasDerivAt_sin z) (fun z _ => Real.hasDerivAt_cos z)
      (fun z _ => by simpa only [abs_neg] using Real.abs_sin_le_one z)
      ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩

/-- Global second-order error for the signed cosine tangent. -/
theorem cos_tangent_error (x m : ℝ) :
    |Real.cos x - Real.cos m + Real.sin m * (x - m)| ≤ (x - m) ^ 2 / 2 := by
  have h := CorrelationQuadraticEnclosure.error_from_second_derivative
    (a := min m x) (b := max m x) (M := 1)
    (fun z _ => Real.hasDerivAt_cos z) (fun z _ => (Real.hasDerivAt_sin z).neg)
    (fun z _ => by simpa only [abs_neg] using Real.abs_cos_le_one z)
    ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩
  simpa only [neg_mul, mul_neg, sub_neg_eq_add, one_div, div_eq_mul_inv,
    one_mul, mul_comm] using h

/-- Approximate value and slope data preserve a Taylor bound, with explicit
cost for both data errors. -/
theorem approximate_tangent_error {v v₀ d d₀ δ ε R : ℝ}
    (hv : |v - v₀| ≤ ε) (hd : |d - d₀| ≤ ε)
    {y : ℝ} (hy : |y - v - d * δ| ≤ R) :
    |y - (v₀ + d₀ * δ)| ≤ R + ε * (1 + |δ|) := by
  calc
    _ = |(y - v - d * δ) + (v - v₀) + (d - d₀) * δ| := by ring_nf
    _ ≤ |y - v - d * δ| + |v - v₀| + |(d - d₀) * δ| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ R + ε + ε * |δ| := by
      rw [abs_mul]
      exact add_le_add (add_le_add hy hv) (mul_le_mul_of_nonneg_right hd (abs_nonneg _))
    _ = _ := by ring

/-- An enclosure for one phase provides a sine enclosure at any real point. -/
theorem sin_from_phase {m c s ε : ℝ}
    (hc : |c - Real.cos m| ≤ ε) (hs : |s - Real.sin m| ≤ ε) (x : ℝ) :
    |Real.sin x - (s + c * (x - m))| ≤
      (x - m) ^ 2 / 2 + ε * (1 + |x - m|) := by
  exact approximate_tangent_error (by simpa only [abs_sub_comm] using hs)
    (by simpa only [abs_sub_comm] using hc) (sin_tangent_error x m)

/-- The companion cosine enclosure retains the opposite signed slope. -/
theorem cos_from_phase {m c s ε : ℝ}
    (hc : |c - Real.cos m| ≤ ε) (hs : |s - Real.sin m| ≤ ε) (x : ℝ) :
    |Real.cos x - (c - s * (x - m))| ≤
      (x - m) ^ 2 / 2 + ε * (1 + |x - m|) := by
  have h := approximate_tangent_error (v := Real.cos m) (d := -Real.sin m)
    (v₀ := c) (d₀ := -s) (by simpa only [abs_sub_comm] using hc)
    (by simpa only [neg_sub_neg, abs_sub_comm] using hs)
    (by simpa only [neg_mul, sub_neg_eq_add] using cos_tangent_error x m)
  simpa only [neg_mul, ← sub_eq_add_neg] using h

end
end RiemannGaussian.TrigonometricLinearEnclosure
