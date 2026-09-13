/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import LeanCert.Core.IntervalRat.Basic
import Mathlib.Tactic

/-!
# A rational box bound for a coupled affine support

The complete gradient is enclosed before applying the box cost. Signed
gradient intervals and anchors outside the target box are both supported.
-/

namespace RiemannGaussian.CorrelationAffineBox
open LeanCert.Core
open scoped BigOperators

/-- The exact lower corner product of two rational intervals. -/
def cornerLower (a b c d : ℚ) : ℚ :=
  min (min (a * c) (a * d)) (min (b * c) (b * d))

/-- All real products in a rectangle exceed its smallest corner product. -/
theorem cornerLower_le {a b c d : ℚ} {x y : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) b) (hy : y ∈ Set.Icc (c : ℝ) d) :
    (cornerLower a b c d : ℝ) ≤ x * y := by
  have hab : a ≤ b := by exact_mod_cast hx.1.trans hx.2
  have hcd : c ≤ d := by exact_mod_cast hy.1.trans hy.2
  have h := IntervalRat.mem_mul (I := ⟨a, b, hab⟩) (J := ⟨c, d, hcd⟩) hx hy
  exact h.1

/-- Evaluate a certified affine lower support on a rational closed box. -/
def lower {ι : Type*} [Fintype ι] (v : ℚ) (m l r dl du : ι → ℚ) : ℚ :=
  v + ∑ j, cornerLower (dl j) (du j) (l j - m j) (r j - m j)

/-- The rational box cost is valid for every enclosed full gradient.
No assumption that the anchor lies in the box is required. -/
theorem lower_le_tangent {ι : Type*} [Fintype ι]
    (v : ℚ) (m l r dl du : ι → ℚ) {value : ℝ} (grad x : ι → ℝ)
    (hv : (v : ℝ) ≤ value)
    (hg : ∀ j, grad j ∈ Set.Icc (dl j : ℝ) (du j))
    (hx : ∀ j, x j ∈ Set.Icc (l j : ℝ) (r j)) :
    (lower v m l r dl du : ℝ) ≤ value + ∑ j, grad j * (x j - (m j : ℝ)) := by
  simp only [lower, Rat.cast_add, Rat.cast_sum]
  apply add_le_add hv
  apply Finset.sum_le_sum
  intro j _
  apply cornerLower_le (hg j)
  simpa only [Rat.cast_sub, Set.mem_Icc] using And.intro
    (sub_le_sub_right (hx j).1 (m j : ℝ)) (sub_le_sub_right (hx j).2 (m j : ℝ))

end RiemannGaussian.CorrelationAffineBox
