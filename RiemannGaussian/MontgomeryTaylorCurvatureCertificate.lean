/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorSevenWindowForms
import RiemannGaussian.MontgomeryTaylorRangeTable
import RiemannGaussian.CertifiedIntegerQuadraticForm

/-!
# Exact integer checks for the complete seven-point curvature

All nineteen signed lower curvatures contribute to one integer matrix.
A scaled approximate Gram witness checks that matrix without discarding its
mixed terms. Positive scaling then recovers the real objective's matrix.
-/

namespace RiemannGaussian.MontgomeryTaylorCurvatureCertificate
open MontgomeryTaylorSevenWindowForms MontgomeryTaylorRangeTable
open scoped BigOperators

/-- Extra integer precision used by proposed approximate Gram factors. -/
def gramScale : ℕ := 4096

/-- The full signed curvature matrix before its common positive denominator. -/
def integerCurvature (d : Fin 19 → ℤ) : Matrix (Fin 6) (Fin 6) ℤ :=
  fun i j => ∑ t, (coefficientNumerator t : ℤ) * d t *
    directionNumerator t i * directionNumerator t j

/-- A common positive integer scale makes precise Gram witnesses integral. -/
def scaledCurvature (d : Fin 19 → ℤ) : Matrix (Fin 6) (Fin 6) ℤ :=
  fun i j => (gramScale : ℤ) ^ 2 * integerCurvature d i j

/-- The exact positive normalization of the integer curvature matrix. -/
theorem lowerCurvature_eq_scaled (d : Fin 19 → ℤ) :
    lowerCurvature (fun t => (d t : ℝ) / boundScale) =
      (1 / ((100000 : ℝ) * boundScale * (gramScale : ℝ) ^ 2)) •
        CertifiedIntegerQuadraticForm.realMatrix (scaledCurvature d) := by
  ext i j
  simp only [lowerCurvature, CorrelationConvexEnclosure.curvatureMatrix,
    CertifiedIntegerQuadraticForm.realMatrix, scaledCurvature, integerCurvature,
    Matrix.smul_apply, smul_eq_mul, coefficient, direction, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_ofNat, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    Int.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  norm_num only [boundScale, gramScale, Nat.cast_ofNat]
  ring

/-- Execute the polynomial integer matrix certificate. -/
def check (d : Fin 19 → ℤ) (L : Matrix (Fin 6) (Fin 6) ℤ) : Bool :=
  CertifiedIntegerQuadraticForm.check (scaledCurvature d) L

/-- A successful integer check establishes positive semidefiniteness of
the actual lower-curvature matrix used by the seven-point tangent theorem. -/
theorem check_sound {d : Fin 19 → ℤ} {L : Matrix (Fin 6) (Fin 6) ℤ}
    (h : check d L = true) :
    (lowerCurvature (fun t => (d t : ℝ) / boundScale)).PosSemidef := by
  rw [lowerCurvature_eq_scaled]
  exact (CertifiedIntegerQuadraticForm.check_sound (scaledCurvature d) L h).smul
    (by positivity)

end RiemannGaussian.MontgomeryTaylorCurvatureCertificate
