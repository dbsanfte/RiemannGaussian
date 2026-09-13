/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorSevenWindowForms
import RiemannGaussian.MontgomeryTaylorPointBounds
import RiemannGaussian.CorrelationAffineBox

/-!
# Reusable certificates for the complete value and gradient

The nineteen pair evaluations are checked once per anchor. The cached
output encloses the full signed gradient after all overlaps and pressures
have been summed, ready for reuse across many continuous boxes.
-/

namespace RiemannGaussian.MontgomeryTaylorAnchorBounds
open MontgomeryTaylorSevenWindowForms
open scoped BigOperators

/-- Rational anchor coordinates with cached objective and gradient bounds. -/
structure Anchor where
  /-- The six exact gap coordinates of the anchor. -/
  point : Fin 6 → ℚ
  /-- A lower bound for the complete objective there. -/
  value : ℚ
  /-- Lower endpoints for all six components of the complete gradient. -/
  lower : Fin 6 → ℚ
  /-- Upper endpoints for all six components of the complete gradient. -/
  upper : Fin 6 → ℚ

/-- Untrusted proposed point enclosures used to check an anchor's cache. -/
structure Witness where
  /-- Chosen certified phase for each of the nineteen pair separations. -/
  phase : Fin 19 → ℕ
  /-- Integer value and slope enclosures for every pair separation. -/
  samples : Fin 19 → MontgomeryTaylorPointBounds.Bounds

/-- The pair lower values plus the exact anchor pressure. -/
def valueLower (m : Fin 6 → ℚ) (b : Fin 19 → MontgomeryTaylorPointBounds.Bounds) : ℚ :=
  (∑ t, coefficient t * (b t).valueRat) + ∑ j, pressure j * m j

/-- The complete lower gradient, assembled before taking any absolute value. -/
def gradientLower (b : Fin 19 → MontgomeryTaylorPointBounds.Bounds) (j : Fin 6) : ℚ :=
  pressure j + ∑ t, coefficient t * (b t).lowerRat * direction t j

/-- The complete upper gradient with the same shared pair directions. -/
def gradientUpper (b : Fin 19 → MontgomeryTaylorPointBounds.Bounds) (j : Fin 6) : ℚ :=
  pressure j + ∑ t, coefficient t * (b t).upperRat * direction t j

/-- The exact real interpretation of the cached anchor output. -/
def Valid (a : Anchor) : Prop :=
  (a.value : ℝ) ≤ objective (fun j => (a.point j : ℝ)) ∧
    ∀ j, gradient (fun k => (a.point k : ℝ)) j ∈ Set.Icc (a.lower j : ℝ) (a.upper j)

/-- Check every point enclosure and both complete cached summaries. -/
def check (a : Anchor) (w : Witness) : Bool :=
  decide (∀ t : Fin 19, MontgomeryTaylorPointBounds.check
    (linearFormRat t a.point) (w.phase t) (w.samples t) = true) &&
  decide (a.value ≤ valueLower a.point w.samples) &&
  decide (∀ j : Fin 6, a.lower j ≤ gradientLower w.samples j ∧
    gradientUpper w.samples j ≤ a.upper j)

/-- Correct pair enclosures give exact bounds for the complete value and
signed gradient at the anchor. -/
theorem samples_sound (m : Fin 6 → ℚ) (b : Fin 19 → MontgomeryTaylorPointBounds.Bounds)
    (hb : ∀ t, MontgomeryTaylorPointBounds.Valid (linearFormRat t m) (b t)) :
    (valueLower m b : ℝ) ≤ objective (fun j => (m j : ℝ)) ∧
      ∀ j, gradient (fun k => (m k : ℝ)) j ∈
        Set.Icc (gradientLower b j : ℝ) (gradientUpper b j) := by
  have hp (t : Fin 19) :
      ((b t).valueRat : ℝ) ≤ MontgomeryTaylorNumericalKernel.kernel
        (linearForm t (fun j => (m j : ℝ))) ^ 2 ∧
        MontgomeryTaylorNumericalKernel.squaredD (linearForm t (fun j => (m j : ℝ))) ∈
          Set.Icc ((b t).lowerRat : ℝ) ((b t).upperRat) := by
    simpa only [MontgomeryTaylorPointBounds.Valid, linearFormRat_cast] using hb t
  constructor
  · apply intervalLower_le m (fun t => (b t).valueRat) _ (fun t => (hp t).1)
    intro j
    exact le_rfl
  · intro j
    simp only [gradientLower, gradientUpper, Rat.cast_add, Rat.cast_sum, Rat.cast_mul,
      MontgomeryTaylorSevenWindowForms.gradient, Set.mem_Icc]
    constructor
    · apply add_le_add le_rfl
      exact Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hp t).2.1 (coefficient_nonneg t)) (direction_nonneg t j)
    · apply add_le_add le_rfl
      exact Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hp t).2.2 (coefficient_nonneg t)) (direction_nonneg t j)

/-- A successful anchor check supplies a reusable real value and full
gradient enclosure, independently of all later box choices. -/
theorem check_sound {a : Anchor} {w : Witness} (h : check a w = true) : Valid a := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  have hs := samples_sound a.point w.samples
    (fun t => MontgomeryTaylorPointBounds.check_sound (h.1.1 t))
  refine ⟨?_, fun j => ⟨?_, ?_⟩⟩
  · exact (by exact_mod_cast h.1.2 : (a.value : ℝ) ≤ valueLower a.point w.samples).trans hs.1
  · exact (by exact_mod_cast (h.2 j).1 : (a.lower j : ℝ) ≤ gradientLower w.samples j).trans
      (hs.2 j).1
  · exact (hs.2 j).2.trans
      (by exact_mod_cast (h.2 j).2 : (gradientUpper w.samples j : ℝ) ≤ a.upper j)

/-- The cached anchor bounds evaluate a sound lower tangent on any box;
signed gradient cancellation is retained until this final box cost. -/
theorem box_tangent_lower {a : Anchor} (ha : Valid a) (l r : Fin 6 → ℚ)
    (x : Fin 6 → ℝ) (hx : ∀ j, x j ∈ Set.Icc (l j : ℝ) (r j)) :
    (CorrelationAffineBox.lower a.value a.point l r a.lower a.upper : ℝ) ≤
      objective (fun j => (a.point j : ℝ)) +
        ∑ j, gradient (fun k => (a.point k : ℝ)) j * (x j - (a.point j : ℝ)) :=
  CorrelationAffineBox.lower_le_tangent _ _ _ _ _ _ _ _ ha.1 ha.2 hx

/-- Short block indexing for a catalogue stored in chunks of thirty-two. -/
def catalogueLookup (blocks : List (List Anchor)) (i : ℕ) : Option Anchor :=
  (blocks[i / 32]?.getD [])[i % 32]?

/-- A lookup can only return one of the independently certified anchors.
Missing entries remain missing and cannot certify a leaf. -/
theorem catalogueLookup_valid (blocks : List (List Anchor))
    (hblocks : ∀ block ∈ blocks, ∀ a ∈ block, Valid a)
    {i : ℕ} {a : Anchor} (h : catalogueLookup blocks i = some a) : Valid a := by
  unfold catalogueLookup at h
  cases hb : blocks[i / 32]? with
  | none =>
    simp only [hb, Option.getD_none, List.getElem?_nil] at h
    cases h
  | some block =>
    simp only [hb, Option.getD_some] at h
    exact hblocks block (List.mem_of_getElem? hb) a (List.mem_of_getElem? h)

end RiemannGaussian.MontgomeryTaylorAnchorBounds
