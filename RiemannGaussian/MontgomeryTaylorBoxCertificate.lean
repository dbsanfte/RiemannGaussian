/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorAnchorBounds
import RiemannGaussian.MontgomeryTaylorCurvatureCertificate
import RiemannGaussian.CertifiedBoxCover

/-!
# A complete continuous checker for the seven-point compact box

The two leaf mechanisms are ordinary squared-value bounds and a coupled
anchor tangent with a certified full curvature matrix. All interval
endpoints, signed gradients, table-domain conditions and common split
boundaries remain explicit. An accepted cover would close the compact
model floor; this module alone does not assert that any full cover passes.
-/

namespace RiemannGaussian.MontgomeryTaylorBoxCertificate
open MontgomeryTaylorSevenWindowForms MontgomeryTaylorSevenWindowModel
open MontgomeryTaylorSevenWindowParameters MontgomeryTaylorNumericalKernel
open MontgomeryTaylorRangeTable MontgomeryTaylorAnchorBounds
open scoped BigOperators

/-- The exact rational model floor checked at every successful leaf. -/
def target : ℚ := 395002 / 100000000

/-- The checker uses precisely the model floor in the analytic transfer. -/
theorem target_cast : (target : ℝ) = modelFloor := by norm_num [target, modelFloor]

/-- Six rational closed intervals for a candidate gap configuration. -/
abbrev Box := CertifiedBoxCover.Box (Fin 6)

/-- The lower gap endpoints of a box. -/
def lower (B : Box) (j : Fin 6) : ℚ := (B j).1

/-- The upper gap endpoints of a box. -/
def upper (B : Box) (j : Fin 6) : ℚ := (B j).2

/-- Exact pair lower endpoints from the common gap box. -/
def pairLower (B : Box) (t : Fin 19) : ℚ := linearFormRat t (lower B)

/-- Exact pair upper endpoints from the common gap box. -/
def pairUpper (B : Box) (t : Fin 19) : ℚ := linearFormRat t (upper B)

/-- The box and anchor are contained in this common coordinate hull. -/
def hull (B : Box) (a : Anchor) : Box :=
  fun j => (min (lower B j) (a.point j), max (upper B j) (a.point j))

/-- Every point of the target box remains in the anchor hull. -/
theorem mem_hull {B : Box} {x : Fin 6 → ℝ} (hx : CertifiedBoxCover.Mem x B)
    (a : Anchor) : CertifiedBoxCover.Mem x (hull B a) := by
  intro j
  simp only [hull, Rat.cast_min, Rat.cast_max]
  exact ⟨(min_le_left _ _).trans (hx j).1, (hx j).2.trans (le_max_left _ _)⟩

/-- The exact anchor is contained in its hull with every target box. -/
theorem anchor_mem_hull (B : Box) (a : Anchor) :
    CertifiedBoxCover.Mem (fun j => (a.point j : ℝ)) (hull B a) := by
  intro j
  simp only [hull, Rat.cast_min, Rat.cast_max]
  exact ⟨min_le_right _ _, le_max_right _ _⟩

/-- Execute the ordinary interval-value leaf test. -/
def checkInterval (table : Table) (l r : ℚ) (B : Box) : Bool :=
  decide (target ≤ intervalLower (lower B)
    (fun t => valueQuery table l r (pairLower B t) (pairUpper B t)))

/-- Every accepted ordinary leaf bounds the actual finite model throughout
its complete real box. -/
theorem checkInterval_sound {table : Table} {l r : ℚ}
    (htable : MontgomeryTaylorRangeTable.Valid table l r) {B : Box}
    (h : checkInterval table l r B = true) {x : Fin 6 → ℝ}
    (hx : CertifiedBoxCover.Mem x B) : modelFloor ≤ finiteModel x := by
  have hvalue (t : Fin 19) := valueQuery_le htable (linearForm_mem_box t (lower B) (upper B) hx)
  have hl := intervalLower_le (lower B) _ x hvalue (fun j => (hx j).1)
  simp only [checkInterval, decide_eq_true_eq] at h
  have htar : (target : ℝ) ≤ (intervalLower (lower B)
      (fun t => valueQuery table l r (pairLower B t) (pairUpper B t)) : ℝ) := by
    exact_mod_cast h
  rw [target_cast] at htar
  rw [finiteModel_eq_objective]
  exact htar.trans hl

/-- Integer curvature bounds and a proposed factor for their complete matrix. -/
structure CurvatureWitness where
  /-- Signed integer lower curvatures of all nineteen pair terms. -/
  curvature : Fin 19 → ℤ
  /-- A proposed integer Gram factor for the complete scaled matrix. -/
  factor : Matrix (Fin 6) (Fin 6) ℤ

/-- Check the entire table domain, all signed curvature queries, the full
integer matrix, and the cached affine support for an anchor leaf. -/
def checkAnchor (table : Table) (l r : ℚ) (B : Box) (a : Anchor)
    (w : CurvatureWitness) : Bool :=
  decide (∀ t : Fin 19,
    (1 / 3 : ℚ) ≤ pairLower (hull B a) t ∧ l ≤ pairLower (hull B a) t ∧
      pairUpper (hull B a) t ≤ r ∧
      w.curvature t ≤ (CertifiedRangeTree.query table l r
        (pairLower (hull B a) t) (pairUpper (hull B a) t)).2) &&
  MontgomeryTaylorCurvatureCertificate.check w.curvature w.factor &&
  decide (target ≤ CorrelationAffineBox.lower a.value a.point (lower B) (upper B) a.lower a.upper)

/-- Every accepted anchor leaf bounds the full real model on its box,
with all shared-coordinate curvature and gradient information retained. -/
theorem checkAnchor_sound {table : Table} {l r : ℚ}
    (htable : MontgomeryTaylorRangeTable.Valid table l r) {B : Box} {a : Anchor}
    (ha : MontgomeryTaylorAnchorBounds.Valid a) {w : CurvatureWitness}
    (h : checkAnchor table l r B a w = true) {x : Fin 6 → ℝ}
    (hx : CertifiedBoxCover.Mem x B) : modelFloor ≤ finiteModel x := by
  simp only [checkAnchor, Bool.and_eq_true, decide_eq_true_eq] at h
  have hlo (t : Fin 19) : (1 : ℝ) / 3 ≤ pairLower (hull B a) t := by
    have hc : ((1 / 3 : ℚ) : ℝ) ≤ (pairLower (hull B a) t : ℝ) :=
      Rat.cast_le.mpr (h.1.1 t).1
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hc
    exact hc
  have hdd (t : Fin 19) (z : ℝ)
      (hz : z ∈ Set.Icc (pairLower (hull B a) t : ℝ) (pairUpper (hull B a) t)) :
      (w.curvature t : ℝ) / boundScale ≤ squaredDD z := by
    have hmem : z ∈ Set.Icc (l : ℝ) r :=
      ⟨(by exact_mod_cast (h.1.1 t).2.1 : (l : ℝ) ≤ pairLower (hull B a) t).trans hz.1,
        hz.2.trans (by exact_mod_cast (h.1.1 t).2.2.1 :
          (pairUpper (hull B a) t : ℝ) ≤ r)⟩
    have hb := (MontgomeryTaylorRangeTable.query_sound htable hmem hz).2
    have hd : (w.curvature t : ℝ) ≤
        ((CertifiedRangeTree.query table l r
          (pairLower (hull B a) t) (pairUpper (hull B a) t)).2 : ℝ) := by
      exact_mod_cast (h.1.1 t).2.2.2
    exact (div_le_div_of_nonneg_right hd (Nat.cast_nonneg boundScale)).trans hb
  have ht := objective_tangent_lower (fun j => (a.point j : ℝ)) x
    (fun t => (w.curvature t : ℝ) / boundScale)
    (fun t => (pairLower (hull B a) t : ℝ)) (fun t => (pairUpper (hull B a) t : ℝ)) hlo
    (fun t => linearForm_mem_box t _ _ (anchor_mem_hull B a))
    (fun t => linearForm_mem_box t _ _ (mem_hull hx a)) hdd
    (MontgomeryTaylorCurvatureCertificate.check_sound h.1.2)
  have hb := box_tangent_lower ha (lower B) (upper B) x hx
  have htar : (target : ℝ) ≤
      (CorrelationAffineBox.lower a.value a.point (lower B) (upper B) a.lower a.upper : ℝ) := by
    exact_mod_cast h.2
  rw [target_cast] at htar
  rw [finiteModel_eq_objective]
  exact htar.trans (hb.trans ht)

/-- The two supported leaf mechanisms of the exhaustive certificate. -/
inductive Leaf where
  | interval
  | anchor (index : ℕ) (witness : CurvatureWitness)

/-- Check a leaf using an independently certified anchor catalogue. -/
def leafCheck (table : Table) (l r : ℚ) (anchors : ℕ → Option Anchor)
    (B : Box) : Leaf → Bool
  | .interval => checkInterval table l r B
  | .anchor i w => match anchors i with
    | none => false
    | some a => checkAnchor table l r B a w

/-- Every accepted leaf supplies the full continuous inequality. -/
theorem leafCheck_sound {table : Table} {l r : ℚ}
    (htable : MontgomeryTaylorRangeTable.Valid table l r) (anchors : ℕ → Option Anchor)
    (hanchors : ∀ i a, anchors i = some a → MontgomeryTaylorAnchorBounds.Valid a)
    (B : Box) (w : Leaf) (h : leafCheck table l r anchors B w = true)
    (x : Fin 6 → ℝ) (hx : CertifiedBoxCover.Mem x B) : modelFloor ≤ finiteModel x := by
  cases w with
  | interval => exact checkInterval_sound htable h hx
  | anchor i w =>
    cases hi : anchors i with
    | none => simp only [leafCheck, hi, Bool.false_eq_true] at h
    | some a =>
      simp only [leafCheck, hi] at h
      exact checkAnchor_sound htable (hanchors i a hi) h hx

/-- The explicit compact root box left by the analytic small- and large-gap reductions. -/
def rootBox : Box := fun _ => (1 / 3, 20)

/-- A fully accepted finite subdivision proves the entire compact model
floor, including every boundary point between boxes. -/
theorem compact_floor_of_check {table : Table} {l r : ℚ}
    (htable : MontgomeryTaylorRangeTable.Valid table l r) (anchors : ℕ → Option Anchor)
    (hanchors : ∀ i a, anchors i = some a → MontgomeryTaylorAnchorBounds.Valid a)
    (tree : CertifiedBoxCover.Tree (Fin 6) Leaf)
    (h : CertifiedBoxCover.check (leafCheck table l r anchors) tree rootBox = true) :
    ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (1 / 3) 20) → modelFloor ≤ finiteModel x := by
  intro x hx
  apply CertifiedBoxCover.check_sound (fun y => modelFloor ≤ finiteModel y)
    (leafCheck table l r anchors) (leafCheck_sound htable anchors hanchors) tree h x
  intro j
  simpa only [rootBox, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Set.mem_Icc] using hx j

end RiemannGaussian.MontgomeryTaylorBoxCertificate
