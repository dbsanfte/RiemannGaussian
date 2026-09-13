/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorSevenWindowForms
import RiemannGaussian.MontgomeryTaylorRangeTable
import RiemannGaussian.CorrelationAffineBox

/-!
# Exact integer coordinates and box costs

One common denominator turns the numerical cover's repeated rational
operations into integer polynomial calculations. Every displayed cost is
proved equal to its original rational expression.
-/

namespace RiemannGaussian.MontgomeryTaylorIntegerCoordinates
open MontgomeryTaylorSevenWindowForms MontgomeryTaylorRangeTable
open scoped BigOperators

/-- Common denominator for all proposed gap coordinates and split cuts. -/
def denominator : ℕ := 30000000

/-- Decode an integer gap coordinate into its exact rational value. -/
def rational (n : ℤ) : ℚ := (n : ℚ) / denominator

/-- The nineteen exact pair sums, evaluated without redundant incidence sums. -/
def separations (g : Fin 6 → ℤ) : Fin 19 → ℤ := ![g 0, g 1, g 2, g 3, g 4, g 5, g 0 + g 1, g 1 + g 2, g 3 + g 4, g 4 + g 5, g 0 + g 1 + g 2, g 1 + g 2 + g 3, g 2 + g 3 + g 4, g 3 + g 4 + g 5, g 0 + g 1 + g 2 + g 3, g 2 + g 3 + g 4 + g 5, g 0 + g 1 + g 2 + g 3 + g 4, g 1 + g 2 + g 3 + g 4 + g 5, g 0 + g 1 + g 2 + g 3 + g 4 + g 5]

/-- Every integer pair sum retains exactly the real linear form. -/
theorem separations_cast (g : Fin 6 → ℤ) (t : Fin 19) :
    (rational (separations g t) : ℝ) = linearForm t (fun j => (rational (g j) : ℝ)) := by
  fin_cases t <;>
    norm_num [separations, rational, denominator, linearForm, direction, directionNumerator,
      start, width, Fin.sum_univ_succ, Fin.succ, Int.cast_add] <;> ring_nf <;> rfl

/-- Integer numerator of the exact gap-pressure contribution. -/
def pressureNumerator (g : Fin 6 → ℤ) : ℤ :=
  208856 * g 0 + 325508 * g 1 + 465636 * g 2 +
    465636 * g 3 + 325508 * g 4 + 208856 * g 5

/-- Integer numerator of the nineteen weighted pair lower bounds. -/
def pairNumerator (v : Fin 19 → ℤ) : ℤ :=
  21884 * v 0 + 33405 * v 1 + 44711 * v 2 + 44711 * v 3 + 33405 * v 4 + 21884 * v 5 + 74396 * v 6 + 25604 * v 7 + 25604 * v 8 + 74396 * v 9 + 32469 * v 10 + 67531 * v 11 + 67531 * v 12 + 32469 * v 13 + 100000 * v 14 + 100000 * v 15 + 100000 * v 16 + 100000 * v 17 + 200000 * v 18

/-- The complete pressure numerator equals the original finite sum. -/
theorem pressureNumerator_cast (g : Fin 6 → ℤ) :
    (pressureNumerator g : ℝ) / (1000000000 * denominator) =
      ∑ j, (pressure j : ℝ) * (rational (g j) : ℝ) := by
  norm_num [pressureNumerator, pressure, rational, denominator, Fin.sum_univ_succ, Fin.succ,
    Int.cast_add, Int.cast_mul]
  ring_nf
  rfl

/-- The complete pair numerator equals the original finite sum. -/
theorem pairNumerator_cast (v : Fin 19 → ℤ) :
    (pairNumerator v : ℝ) / (100000 * boundScale) =
      ∑ t, (coefficient t : ℝ) * ((v t : ℝ) / boundScale) := by
  norm_num [pairNumerator, boundScale, coefficient, coefficientNumerator, Fin.sum_univ_succ,
    Fin.succ, Int.cast_add, Int.cast_mul]
  ring_nf
  rfl

/-- Integer numerator of the entire interval lower bound. -/
def intervalNumerator (g : Fin 6 → ℤ) (v : Fin 19 → ℤ) : ℤ :=
  (boundScale : ℤ) * pressureNumerator g + 10000 * denominator * pairNumerator v

/-- Exact equality of integer and rational interval costs. -/
theorem intervalNumerator_cast (g : Fin 6 → ℤ) (v : Fin 19 → ℤ) :
    (intervalNumerator g v : ℝ) / (1000000000 * denominator * boundScale) =
      (intervalLower (fun j => rational (g j)) (fun t => (v t : ℚ) / boundScale) : ℝ) := by
  simp only [intervalLower, Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_div,
    Rat.cast_intCast, Rat.cast_natCast]
  rw [← pressureNumerator_cast, ← pairNumerator_cast]
  norm_num only [intervalNumerator, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    Int.cast_ofNat, denominator, boundScale, Nat.cast_ofNat]
  ring

/-- Exact lower corner product for an integer gradient interval and displacement. -/
def corner (a b c d : ℤ) : ℤ := min (min (a*c) (a*d)) (min (b*c) (b*d))

/-- Integer numerator of a complete cached tangent on a box. -/
def tangentNumerator (value : ℤ) (m l r dl du : Fin 6 → ℤ) : ℤ :=
  value * denominator + ∑ j, corner (dl j) (du j) (l j - m j) (r j - m j)

/-- Scaling a corner cost by common positive denominators is exact. -/
theorem corner_cast (a b c d : ℤ) :
    (corner a b c d : ℝ) / ((boundScale : ℝ) * denominator) =
      (CorrelationAffineBox.cornerLower ((a : ℚ) / boundScale) ((b : ℚ) / boundScale)
        (rational c) (rational d) : ℝ) := by
  simp only [corner, CorrelationAffineBox.cornerLower, rational, Int.cast_min,
    Int.cast_mul, Rat.cast_min, Rat.cast_mul, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  have h : (0 : ℝ) ≤ (boundScale : ℝ) * denominator := by
    norm_num [boundScale, denominator]
  simp only [← min_div_div_right h, mul_div_mul_comm]

/-- Integer tangent evaluation retains the exact signed rational box cost. -/
theorem tangentNumerator_cast (value : ℤ) (m l r dl du : Fin 6 → ℤ) :
    (tangentNumerator value m l r dl du : ℝ) / ((boundScale : ℝ) * denominator) =
      (CorrelationAffineBox.lower ((value : ℚ) / boundScale)
        (fun j => rational (m j)) (fun j => rational (l j)) (fun j => rational (r j))
        (fun j => (dl j : ℚ) / boundScale) (fun j => (du j : ℚ) / boundScale) : ℝ) := by
  simp only [tangentNumerator, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_sum,
    add_div, Finset.sum_div, CorrelationAffineBox.lower, Rat.cast_add, Rat.cast_sum,
    Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  congr 1
  · norm_num only [denominator, boundScale, Nat.cast_ofNat]
    ring
  · apply Finset.sum_congr rfl
    intro j _
    rw [corner_cast]
    have hsub (a b : ℤ) : rational (a - b) = rational a - rational b := by
      simp only [rational, Int.cast_sub, sub_div]
    simp only [hsub]

end RiemannGaussian.MontgomeryTaylorIntegerCoordinates
