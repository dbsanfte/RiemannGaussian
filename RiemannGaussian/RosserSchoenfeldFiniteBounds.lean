/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldFiniteData07

/-!
# The actual Rosser prime-count bounds through 16000

The complete finite prime enumeration and 136 checked logarithmic cells
prove both original strict inequalities at every real point of [67,16000].
The remaining unbounded range is not assumed or claimed here.
-/

namespace RiemannGaussian.RosserSchoenfeldFiniteBounds
open RosserSchoenfeldComparison
/-- Both original Rosser prime-count bounds hold on the entire stated real interval. -/
theorem bounds_through_sixteen_thousand {x : ℝ} (hx : x ∈ Set.Icc (67 : ℝ) 16000) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x := by
  exact join (join (join bounds_chunk00 bounds_chunk01) (join bounds_chunk02 bounds_chunk03))
    (join (join bounds_chunk04 bounds_chunk05) (join bounds_chunk06 bounds_chunk07)) x hx

/-- The exact complete prime count at the upper end of the finite verification. -/
theorem primeCounting_sixteen_thousand : Nat.primeCounting 16000 = 1862 := count_16000

/-- The original strict lower bound for the actual count at every real endpoint. -/
theorem lower_lt_primeCounting {x : ℝ} (hx : x ∈ Set.Icc (67 : ℝ) 16000) :
    x / (Real.log x - 1 / 2) < (Nat.primeCounting ⌊x⌋₊ : ℝ) :=
  (bounds_through_sixteen_thousand hx).1

/-- The original strict upper bound, with coefficient 3/2 unchanged. -/
theorem primeCounting_lt_upper {x : ℝ} (hx : x ∈ Set.Icc (67 : ℝ) 16000) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) <
      x / Real.log x * (1 + 3 / (2 * Real.log x)) :=
  (bounds_through_sixteen_thousand hx).2

end RiemannGaussian.RosserSchoenfeldFiniteBounds
