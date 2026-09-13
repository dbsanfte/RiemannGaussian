/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorIntegerBoxCertificate

/-!
# Exhaustive closed covers with integer comparisons

Accepted leaves cover every point of their parent box, including split
boundaries. The entire compact floor follows when a complete tree passes.
-/

namespace RiemannGaussian.MontgomeryTaylorIntegerBoxCertificate
open MontgomeryTaylorSevenWindowModel MontgomeryTaylorSevenWindowParameters

/-- Integer-cut subdivisions with either interval or coupled-anchor leaves. -/
inductive Tree where
  | interval
  | anchor (index : ℕ) (witness : CurvatureWitness)
  | split (coordinate : Fin 6) (cut : ℤ) (left right : Tree)

/-- The lower child includes the shared cut. -/
def leftBox (B : Box) (i : Fin 6) (q : ℤ) : Box :=
  Function.update B i ((B i).1, q)

/-- The upper child includes the same shared cut. -/
def rightBox (B : Box) (i : Fin 6) (q : ℤ) : Box :=
  Function.update B i (q, (B i).2)

/-- Every real point of a parent is in at least one closed child. -/
theorem split_covers {B : Box} {x : Fin 6 → ℝ} (hx : Mem x B) (i : Fin 6) (q : ℤ) :
    Mem x (leftBox B i q) ∨ Mem x (rightBox B i q) := by
  rcases le_total (x i) (real q) with hl | hr
  · left
    intro j
    by_cases hj : j = i
    · subst j
      simpa only [lower, upper, leftBox, Function.update_self, Set.mem_Icc] using And.intro (hx i).1 hl
    · simpa only [lower, upper, leftBox, Function.update_of_ne hj] using hx j
  · right
    intro j
    by_cases hj : j = i
    · subst j
      simpa only [lower, upper, rightBox, Function.update_self, Set.mem_Icc] using And.intro hr (hx i).2
    · simpa only [lower, upper, rightBox, Function.update_of_ne hj] using hx j

/-- All exhaustive per-box operations use exact integer comparisons. -/
def check (table : Table) (l r : ℤ) (anchors : ℕ → Option Anchor) : Tree → Box → Bool
  | .interval, B => checkInterval table l r B
  | .anchor i w, B => match anchors i with
    | none => false
    | some a => checkAnchor table l r B a w
  | .split i q left right, B =>
    check table l r anchors left (leftBox B i q) &&
      check table l r anchors right (rightBox B i q)

/-- Separately checked complete children compose without repeating leaf computations. -/
theorem check_split {table : Table} {l r : ℤ} {anchors : ℕ → Option Anchor}
    {B : Box} {i : Fin 6} {q : ℤ} {left right : Tree}
    (hl : check table l r anchors left (leftBox B i q) = true)
    (hr : check table l r anchors right (rightBox B i q) = true) :
    check table l r anchors (.split i q left right) B = true := by
  simp only [check, Bool.and_eq_true]
  exact ⟨hl, hr⟩

/-- A complete accepted integer cover proves the real model floor throughout its root. -/
theorem check_sound {table : Table} {l r : ℤ} (ht : TableValid table l r)
    (anchors : ℕ → Option Anchor)
    (ha : ∀ i a, anchors i = some a → MontgomeryTaylorAnchorBounds.Valid a.decode)
    (tree : Tree) {B : Box} (hc : check table l r anchors tree B = true) :
    ∀ x, Mem x B → modelFloor ≤ finiteModel x := by
  induction tree generalizing B with
  | interval => exact fun _ hx => checkInterval_sound ht hc hx
  | anchor i w =>
    cases hi : anchors i with
    | none => simp only [check, hi, Bool.false_eq_true] at hc
    | some a =>
      simp only [check, hi] at hc
      exact fun _ hx => checkAnchor_sound ht (ha i a hi) hc hx
  | split i q left right ihl ihr =>
    simp only [check, Bool.and_eq_true] at hc
    intro x hx
    rcases split_covers hx i q with hl | hr
    · exact ihl hc.1 x hl
    · exact ihr hc.2 x hr

/-- The exact compact root left by the analytic small- and large-gap reductions. -/
def rootBox : Box := fun _ => (10000000, 600000000)

/-- A fully accepted cover closes the complete compact analytic obligation. -/
theorem compact_floor_of_check {table : Table} {l r : ℤ} (ht : TableValid table l r)
    (anchors : ℕ → Option Anchor)
    (ha : ∀ i a, anchors i = some a → MontgomeryTaylorAnchorBounds.Valid a.decode)
    (tree : Tree) (hc : check table l r anchors tree rootBox = true) :
    ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (1 / 3) 20) → modelFloor ≤ finiteModel x := by
  intro x hx
  apply check_sound ht anchors ha tree hc x
  intro j
  convert hx j using 1
  norm_num [real, MontgomeryTaylorIntegerCoordinates.rational,
    MontgomeryTaylorIntegerCoordinates.denominator, lower, upper, rootBox,
    Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, Int.cast_ofNat, Nat.cast_ofNat]

end RiemannGaussian.MontgomeryTaylorIntegerBoxCertificate
