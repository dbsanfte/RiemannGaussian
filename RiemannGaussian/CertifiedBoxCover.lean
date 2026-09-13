/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# A checked exhaustive cover by closed boxes

Every split covers its parent, including the common boundary. The general
soundness theorem composes a sound numerical leaf checker into a continuous
global inequality. The tree itself may be supplied by an untrusted search.
-/

namespace RiemannGaussian.CertifiedBoxCover

/-- Closed coordinate intervals with rational endpoints. -/
abbrev Box (ι : Type*) := ι → ℚ × ℚ

/-- Membership of a real configuration in a rational closed box. -/
def Mem {ι : Type*} (x : ι → ℝ) (B : Box ι) : Prop :=
  ∀ i, (B i).1 ≤ x i ∧ x i ≤ (B i).2

/-- A finite subdivision tree, carrying a proposed certificate at each leaf. -/
inductive Tree (ι : Type*) (α : Type*) where
  | leaf (witness : α)
  | split (coordinate : ι) (cut : ℚ) (left right : Tree ι α)

/-- The portion of a box below a coordinate cut. -/
def leftBox {ι : Type*} [DecidableEq ι] (B : Box ι) (i : ι) (q : ℚ) : Box ι :=
  Function.update B i ((B i).1, q)

/-- The portion of a box above a coordinate cut. -/
def rightBox {ι : Type*} [DecidableEq ι] (B : Box ι) (i : ι) (q : ℚ) : Box ι :=
  Function.update B i (q, (B i).2)

/-- Execute the leaf checks throughout the complete subdivision. -/
def check {ι α : Type*} [DecidableEq ι] (leafCheck : Box ι → α → Bool) :
    Tree ι α → Box ι → Bool
  | .leaf a, B => leafCheck B a
  | .split i q l r, B => check leafCheck l (leftBox B i q) &&
      check leafCheck r (rightBox B i q)

/-- Every point of the parent is in at least one child. Degenerate cells
and equality with the cut are retained. -/
theorem split_covers {ι : Type*} [DecidableEq ι] {B : Box ι} {x : ι → ℝ}
    (hx : Mem x B) (i : ι) (q : ℚ) :
    Mem x (leftBox B i q) ∨ Mem x (rightBox B i q) := by
  rcases le_total (x i) (q : ℝ) with hl | hr
  · left
    intro j
    by_cases hj : j = i
    · subst j
      simpa only [leftBox, Function.update_self] using And.intro (hx i).1 hl
    · simpa only [leftBox, Function.update_of_ne hj] using hx j
  · right
    intro j
    by_cases hj : j = i
    · subst j
      simpa only [rightBox, Function.update_self] using And.intro hr (hx i).2
    · simpa only [rightBox, Function.update_of_ne hj] using hx j

/-- A sound local numerical checker and an accepted tree imply the desired
property at every real point of the root box. -/
theorem check_sound {ι α : Type*} [DecidableEq ι]
    (P : (ι → ℝ) → Prop) (leafCheck : Box ι → α → Bool)
    (hleaf : ∀ B a, leafCheck B a = true → ∀ x, Mem x B → P x)
    (tree : Tree ι α) {B : Box ι} (h : check leafCheck tree B = true) :
    ∀ x, Mem x B → P x := by
  induction tree generalizing B with
  | leaf a => exact hleaf B a h
  | split i q l r ihl ihr =>
    simp only [check, Bool.and_eq_true] at h
    intro x hx
    rcases split_covers hx i q with hx' | hx'
    · exact ihl h.1 x hx'
    · exact ihr h.2 x hx'

end RiemannGaussian.CertifiedBoxCover
