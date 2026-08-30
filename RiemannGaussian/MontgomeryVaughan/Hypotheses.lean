/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Adapted from the Montgomery--Vaughan interface in Anthropic's Zeta23
formalization.  This standalone module retains only the proved inequality's
public statement; it introduces no analytic hypothesis or axiom.
-/

import Mathlib

/-!
# Montgomery--Vaughan weighted Hilbert inequality interface

`MVHilbert C` states the bilinear weighted Hilbert inequality for an arbitrary
finite family of distinct real frequencies and any positive admissible gap
weights.  The implementation in this directory proves the statement with an
explicit constant.
-/

noncomputable section

open Complex
open scoped BigOperators ComplexConjugate

namespace RiemannGaussian

/-- The bilinear weighted Montgomery--Vaughan inequality with constant `C`.
The weights may be any positive lower bounds for the pairwise frequency gaps. -/
def MVHilbert (C : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (freq δ : ι → ℝ) (x z : ι → ℂ),
    Function.Injective freq → (∀ r, 0 < δ r) →
      (∀ r s, r ≠ s → δ r ≤ |freq r - freq s|) →
    ‖∑ r, ∑ s, if r = s then (0 : ℂ)
        else x r * conj (z s) / ((freq r - freq s : ℝ) : ℂ)‖
      ≤ C * Real.sqrt (∑ r, ‖x r‖ ^ 2 / δ r) *
          Real.sqrt (∑ r, ‖z r‖ ^ 2 / δ r)

end RiemannGaussian

end
