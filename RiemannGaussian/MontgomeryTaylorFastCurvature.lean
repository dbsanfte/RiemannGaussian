/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorCurvatureCertificate

/-!
# Shared integer evaluation of the complete curvature matrix

Every weighted curvature is formed once and reused at all of its matrix
entries. The equality below proves that the explicit program is exactly
the full nineteen-term form used by the analytic tangent theorem.
-/

namespace RiemannGaussian.MontgomeryTaylorFastCurvature
open MontgomeryTaylorSevenWindowForms MontgomeryTaylorCurvatureCertificate
open scoped BigOperators

/-- The full integer matrix with shared weighted curvatures. -/
def matrix (d : Fin 19 → ℤ) : Matrix (Fin 6) (Fin 6) ℤ :=
  let w0 := (21884 : ℤ) * d 0
  let w1 := (33405 : ℤ) * d 1
  let w2 := (44711 : ℤ) * d 2
  let w3 := (44711 : ℤ) * d 3
  let w4 := (33405 : ℤ) * d 4
  let w5 := (21884 : ℤ) * d 5
  let w6 := (74396 : ℤ) * d 6
  let w7 := (25604 : ℤ) * d 7
  let w8 := (25604 : ℤ) * d 8
  let w9 := (74396 : ℤ) * d 9
  let w10 := (32469 : ℤ) * d 10
  let w11 := (67531 : ℤ) * d 11
  let w12 := (67531 : ℤ) * d 12
  let w13 := (32469 : ℤ) * d 13
  let w14 := (100000 : ℤ) * d 14
  let w15 := (100000 : ℤ) * d 15
  let w16 := (100000 : ℤ) * d 16
  let w17 := (100000 : ℤ) * d 17
  let w18 := (200000 : ℤ) * d 18
  ![![w0 + w6 + w10 + w14 + w16 + w18, w6 + w10 + w14 + w16 + w18, w10 + w14 + w16 + w18, w14 + w16 + w18, w16 + w18, w18],
    ![w6 + w10 + w14 + w16 + w18, w1 + w6 + w7 + w10 + w11 + w14 + w16 + w17 + w18, w7 + w10 + w11 + w14 + w16 + w17 + w18, w11 + w14 + w16 + w17 + w18, w16 + w17 + w18, w17 + w18],
    ![w10 + w14 + w16 + w18, w7 + w10 + w11 + w14 + w16 + w17 + w18, w2 + w7 + w10 + w11 + w12 + w14 + w15 + w16 + w17 + w18, w11 + w12 + w14 + w15 + w16 + w17 + w18, w12 + w15 + w16 + w17 + w18, w15 + w17 + w18],
    ![w14 + w16 + w18, w11 + w14 + w16 + w17 + w18, w11 + w12 + w14 + w15 + w16 + w17 + w18, w3 + w8 + w11 + w12 + w13 + w14 + w15 + w16 + w17 + w18, w8 + w12 + w13 + w15 + w16 + w17 + w18, w13 + w15 + w17 + w18],
    ![w16 + w18, w16 + w17 + w18, w12 + w15 + w16 + w17 + w18, w8 + w12 + w13 + w15 + w16 + w17 + w18, w4 + w8 + w9 + w12 + w13 + w15 + w16 + w17 + w18, w9 + w13 + w15 + w17 + w18],
    ![w18, w17 + w18, w15 + w17 + w18, w13 + w15 + w17 + w18, w9 + w13 + w15 + w17 + w18, w5 + w9 + w13 + w15 + w17 + w18]]

set_option maxHeartbeats 2000000 in
/-- The explicit shared program retains every matrix entry exactly. -/
theorem matrix_eq (d : Fin 19 → ℤ) : matrix d = integerCurvature d := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrix, integerCurvature, coefficientNumerator, directionNumerator,
      start, width, Fin.sum_univ_succ, Fin.succ] <;> ring_nf <;> rfl

/-- Execute the same exact Gram-residual check on the shared matrix program. -/
def check (d : Fin 19 → ℤ) (L : Matrix (Fin 6) (Fin 6) ℤ) : Bool :=
  CertifiedIntegerQuadraticForm.check (fun i j => (gramScale : ℤ)^2 * matrix d i j) L

/-- The faster check proves the same real positive semidefinite form. -/
theorem check_sound {d : Fin 19 → ℤ} {L : Matrix (Fin 6) (Fin 6) ℤ}
    (h : check d L = true) :
    (lowerCurvature (fun t => (d t : ℝ) / MontgomeryTaylorRangeTable.boundScale)).PosSemidef := by
  unfold check at h
  rw [matrix_eq] at h
  exact MontgomeryTaylorCurvatureCertificate.check_sound h

end RiemannGaussian.MontgomeryTaylorFastCurvature
