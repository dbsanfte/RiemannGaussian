/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorSevenWindowModel
import RiemannGaussian.MontgomeryTaylorKernelDerivatives
import RiemannGaussian.CorrelationConvexEnclosure
import RiemannGaussian.CorrelationLinearEnclosure

/-!
# The complete nineteen-term correlation form

This finite representation retains all nonzero pair weights, every shared
coordinate direction, and the complete gradient and curvature matrix. It
connects the numerical box certificates to the literal six-gap model.
-/

namespace RiemannGaussian.MontgomeryTaylorSevenWindowForms
noncomputable section
open MontgomeryTaylorSevenWindowModel MontgomeryTaylorSevenWindowParameters
open MontgomeryTaylorNumericalKernel CorrelationConvexEnclosure
open scoped BigOperators

/-- Start coordinate of each nonzero pair correlation. -/
def start : Fin 19 → ℕ := ![0, 1, 2, 3, 4, 5, 0, 1, 3, 4, 0, 1, 2, 3, 0, 2, 0, 1, 0]

/-- Number of consecutive gaps in each nonzero pair correlation. -/
def width : Fin 19 → ℕ := ![1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 6]

/-- Integer numerators of the nineteen nonzero pair coefficients. -/
def coefficientNumerator : Fin 19 → ℕ :=
  ![21884, 33405, 44711, 44711, 33405, 21884, 74396, 25604, 25604, 74396,
    32469, 67531, 67531, 32469, 100000, 100000, 100000, 100000, 200000]

/-- Exact rational coefficients of the nineteen nonzero pair terms. -/
def coefficient (t : Fin 19) : ℚ := coefficientNumerator t / 100000

/-- The six exact rational gap-pressure coefficients. -/
def pressure (j : Fin 6) : ℚ :=
  (![208856, 325508, 465636, 465636, 325508, 208856] : Fin 6 → ℕ) j / 1000000000

/-- Integer incidence of a gap in a pair separation. -/
def directionNumerator (t : Fin 19) (j : Fin 6) : ℕ :=
  if start t ≤ j.val ∧ j.val < start t + width t then 1 else 0

/-- Incidence of a gap in a pair separation, retaining shared coordinates. -/
def direction (t : Fin 19) (j : Fin 6) : ℚ := directionNumerator t j

/-- The literal pair separation as a linear form on the six gaps. -/
def linearForm (t : Fin 19) (g : Fin 6 → ℝ) : ℝ :=
  ∑ j, (direction t j : ℝ) * g j

/-- The same exact linear form evaluated on rational coordinates. -/
def linearFormRat (t : Fin 19) (g : Fin 6 → ℚ) : ℚ :=
  ∑ j, direction t j * g j

/-- Rational evaluation casts to the literal real pair separation. -/
theorem linearFormRat_cast (t : Fin 19) (g : Fin 6 → ℚ) :
    (linearFormRat t g : ℝ) = linearForm t (fun j => (g j : ℝ)) := by
  simp only [linearFormRat, linearForm, Rat.cast_sum, Rat.cast_mul]

/-- The complete finite numerical objective. -/
def objective (g : Fin 6 → ℝ) : ℝ :=
  (∑ t, (coefficient t : ℝ) * kernel (linearForm t g) ^ 2) +
    ∑ j, (pressure j : ℝ) * g j

/-- Every pair coefficient is nonnegative. -/
theorem coefficient_nonneg (t : Fin 19) : 0 ≤ (coefficient t : ℝ) := by
  unfold coefficient
  positivity

/-- Every pressure coefficient is nonnegative. -/
theorem pressure_nonneg (j : Fin 6) : 0 ≤ (pressure j : ℝ) := by
  unfold pressure
  positivity

/-- Every shared coordinate direction is nonnegative. -/
theorem direction_nonneg (t : Fin 19) (j : Fin 6) : 0 ≤ (direction t j : ℝ) := by
  unfold direction
  positivity

/-- Removing only identically zero terms preserves the actual model exactly. -/
theorem finiteModel_eq_objective (g : Fin 6 → ℝ) : finiteModel g = objective g := by
  norm_num [finiteModel, model, energy, separation, objective, linearForm,
    direction, directionNumerator, coefficient, coefficientNumerator, pressure,
    start, width, pairWeight, pairNumerator,
    pressureWeight, pressureNumerator, Finset.sum_range_succ, Fin.sum_univ_succ, Fin.succ]
  ring_nf

/-- Differences of pair separations preserve the exact common gap increments. -/
theorem linearForm_sub (t : Fin 19) (x m : Fin 6 → ℝ) :
    linearForm t x - linearForm t m = ∑ j, (direction t j : ℝ) * (x j - m j) := by
  simp only [linearForm, mul_sub, Finset.sum_sub_distrib]

/-- A rational gap box encloses every pair separation by its exact endpoint
linear forms. -/
theorem linearForm_mem_box (t : Fin 19) (l r : Fin 6 → ℚ) {x : Fin 6 → ℝ}
    (hx : ∀ j, x j ∈ Set.Icc (l j : ℝ) (r j)) :
    linearForm t x ∈ Set.Icc (linearFormRat t l : ℝ) (linearFormRat t r) := by
  simp only [linearFormRat_cast, linearForm, Set.mem_Icc]
  constructor
  · exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hx j).1 (direction_nonneg t j)
  · exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hx j).2 (direction_nonneg t j)

/-- An exact rational lower estimate from pair values and gap pressures. -/
def intervalLower (l : Fin 6 → ℚ) (v : Fin 19 → ℚ) : ℚ :=
  (∑ t, coefficient t * v t) + ∑ j, pressure j * l j

/-- Continuous pair bounds supply a genuine lower bound for the complete
objective throughout a gap box. -/
theorem intervalLower_le (l : Fin 6 → ℚ) (v : Fin 19 → ℚ) (x : Fin 6 → ℝ)
    (hv : ∀ t, (v t : ℝ) ≤ kernel (linearForm t x) ^ 2)
    (hx : ∀ j, (l j : ℝ) ≤ x j) : (intervalLower l v : ℝ) ≤ objective x := by
  simp only [intervalLower, Rat.cast_add, Rat.cast_sum, Rat.cast_mul, objective]
  apply add_le_add
  · exact Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hv t) (coefficient_nonneg t)
  · exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hx j) (pressure_nonneg j)

/-- The full gradient includes the pressure and all overlapping pair slopes. -/
def gradient (m : Fin 6 → ℝ) (j : Fin 6) : ℝ :=
  pressure j + ∑ t, (coefficient t : ℝ) * squaredD (linearForm t m) * direction t j

/-- The signed lower-curvature matrix retains every mixed gap product. -/
def lowerCurvature (d : Fin 19 → ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  curvatureMatrix (fun t => (coefficient t : ℝ) * d t) (fun t j => (direction t j : ℝ))

/-- Collecting all pair slopes gives exactly the full objective tangent,
including the pressure term. -/
theorem tangent_identity (m x : Fin 6 → ℝ) :
    objective m + (∑ j, gradient m j * (x j - m j)) =
      (∑ t, (coefficient t : ℝ) * (kernel (linearForm t m) ^ 2 +
        squaredD (linearForm t m) * (linearForm t x - linearForm t m))) +
      ∑ j, (pressure j : ℝ) * x j := by
  have hs := CorrelationLinearEnclosure.sum_linear_forms
    (fun t => (coefficient t : ℝ) * squaredD (linearForm t m))
    (fun t j => (direction t j : ℝ)) (fun j => x j - m j)
  simp only [objective, gradient, mul_add, add_mul, Finset.sum_add_distrib,
    linearForm_sub, ← mul_assoc]
  rw [hs]
  have hp : (∑ j, (pressure j : ℝ) * m j) +
      (∑ j, (pressure j : ℝ) * (x j - m j)) = ∑ j, (pressure j : ℝ) * x j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  linarith

/-- A positive semidefinite lower-curvature matrix supports the complete
objective at any anchor whose pair separations share the certified intervals.
The anchor may lie outside the target box. -/
theorem objective_tangent_lower (m x : Fin 6 → ℝ) (d lo hi : Fin 19 → ℝ)
    (hlo : ∀ t, 1 / 3 ≤ lo t)
    (hm : ∀ t, linearForm t m ∈ Set.Icc (lo t) (hi t))
    (hx : ∀ t, linearForm t x ∈ Set.Icc (lo t) (hi t))
    (hdd : ∀ t z, z ∈ Set.Icc (lo t) (hi t) → d t ≤ squaredDD z)
    (hmat : (lowerCurvature d).PosSemidef) :
    objective m + (∑ j, gradient m j * (x j - m j)) ≤ objective x := by
  have h := coupled_tangent_lower
    (f := fun z => kernel z ^ 2) (f' := squaredD) (f'' := squaredDD)
    (fun t => (coefficient t : ℝ)) d lo hi (fun t => linearForm t m)
    (fun t => linearForm t x) (fun t j => (direction t j : ℝ))
    (fun j => x j - m j) coefficient_nonneg
    (fun t z hz => squared_hasDerivAt ((hlo t).trans hz.1))
    (fun t z hz => squaredD_hasDerivAt ((hlo t).trans hz.1)) hdd hm hx
    (fun t => linearForm_sub t x m) hmat
  rw [tangent_identity]
  exact add_le_add h (le_refl (∑ j, (pressure j : ℝ) * x j))

end
end RiemannGaussian.MontgomeryTaylorSevenWindowForms
