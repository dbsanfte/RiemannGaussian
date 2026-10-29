/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeUniversalNumeratorExecution
import RiemannGaussian.SemiprimeSourceCodeArrays

/-! # Executed finite mismatch interpolation for actual universal source rows
The runtime receives finite universal register words and integer parity data.
No polynomial or requested coefficient is a runtime argument.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceInterpolationExecution
open scoped BigOperators
open Polynomial SemiprimeJetArray SemiprimeSourceCodeArrays
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes SubexpRowInterpolation SubexpAnnihilation
open SqrtLog LayoutScaledMatrices
open SemiprimeUniversalNumeratorExecution
variable {r Q Δ R : ℕ}

/-- Literal positive rational interpolation nodes. -/
def node (Q : ℕ) (t : Fin Q) : ℚ := (t.val : ℚ)+1

/-- Node and difference units computed by rational inversion, with proof-only guards. -/
def units (Q : ℕ) : NodeUnits (node Q) :=
  NodeUnits.ofField (node Q) (by
    intro a b h
    apply Fin.ext
    exact_mod_cast (add_right_cancel h : (a.val : ℚ)=(b.val : ℚ)))
    (by intro t; unfold node; positivity)

/-- Literal power-of-two clearing denominator. -/
def denominator (R : ℕ) : ℚˣ := Units.mk0 ((2 : ℚ)^(R-1)) (by positivity)

/-- Actual source prescription from the computed zero-extended integer numerator. -/
def prescription (c : Fin R → ℤ) (a : UniversalType r Q Δ) (i : Fin Δ)
    (y : UniversalType r Q Δ) (t : Fin Q) : ℚ :=
  -(↑((denominator R)⁻¹) : ℚ) * (extended c i t (y.head t) a y : ℚ)

/-- The finite executable expression for this source row column. -/
def code (c : Fin R → ℤ) (a : UniversalType r Q Δ) (i : Fin Δ)
    (y : UniversalType r Q Δ) : PolynomialCode ℚ :=
  mismatchRowCode a (fun v => v.head) (a.slot i) R (units Q) (prescription c a i) y

/-- Actual source coefficient array, including the constant and degree-R coefficient. -/
def row (c : Fin R → ℤ) (a : UniversalType r Q Δ) (i : Fin Δ)
    (y : UniversalType r Q Δ) : InverseReport := compile (R+1) (code c a i y)

/-- Explicit normalized interpolation units agree with the source's units. -/
theorem units_eq (Q : ℕ) : units Q = SemiprimeSourceLayout.sampleUnits Q := rfl

/-- Explicit power-of-two units agree with the source denominator. -/
theorem denominator_eq (R : ℕ) : denominator R = SemiprimeSourceLayout.denominatorUnit R := by
  apply Units.ext
  simp [denominator, SemiprimeSourceLayout.denominatorUnit, LayoutNumerator.denominator]

/-- Scaling and zero extension commute, including both missing-index branches. -/
theorem zeroExtend_scaled (denom : ℚˣ) (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (N : Matrix (Joint t g i) (Joint t g i) ℤ) (a y : UniversalType r Q Δ) :
    zeroExtendMatrix (joint t g i) (unitScaled denom N) a y =
      (↑(denom⁻¹) : ℚ) * ((zeroExtendMatrix (F := ℤ) (joint t g i) N a y : ℤ) : ℚ) := by
  unfold zeroExtendMatrix
  split_ifs <;> simp [unitScaled]

/-- The supplied finite parity solution yields exactly the source prescription. -/
theorem prescription_eq (A : ℕ) (c : Fin R → ℤ)
    (hc : c=BinomialInterpolation.parityCoefficients (K := ℤ) A R)
    (a : UniversalType r Q Δ) (i : Fin Δ) (y : UniversalType r Q Δ) :
    prescription c a i y = matrixPrescription (RingHom.id ℚ)
      (fun t g j => unitScaled (denominator R) (LayoutNumerator.family r Q Δ A R t g j)) a i y := by
  funext t
  unfold prescription matrixPrescription
  rw [extended_eq A c hc, zeroExtend_scaled]
  simp only [LayoutNumerator.family, RingHom.id_apply, neg_mul]

/-- The finite expression denotes the literal universal source polynomial. -/
theorem code_denote (A : ℕ) (c : Fin R → ℤ)
    (hc : c=BinomialInterpolation.parityCoefficients (K := ℤ) A R)
    (a : UniversalType r Q Δ) (i : Fin Δ) (y : UniversalType r Q Δ) :
    (code c a i y).denote = sourceRow (LayoutNumerator.family r Q Δ A R)
      (denominator R) a i R (units Q) y := by
  rw [code, mismatchRowCode_denote]
  unfold sourceRow rowForMatrices
  have hd : prescription c a i = matrixPrescription (RingHom.id ℚ)
      (fun t g j => unitScaled (denominator R) (LayoutNumerator.family r Q Δ A R t g j)) a i :=
    funext (fun y => prescription_eq A c hc a i y)
  rw [hd]

/-- Every retained array coefficient is actually acquired from the universal source formula. -/
theorem row_coefficient (A : ℕ) (c : Fin R → ℤ)
    (hc : c=BinomialInterpolation.parityCoefficients (K := ℤ) A R)
    (a : UniversalType r Q Δ) (i : Fin Δ) (y : UniversalType r Q Δ)
    (k : ℕ) (hk : k<R+1) :
    coefficient (row c a i y).coefficients k =
      (sourceRow (LayoutNumerator.family r Q Δ A R)
        (SemiprimeSourceLayout.denominatorUnit R) a i R
        (SemiprimeSourceLayout.sampleUnits Q) y).coeff k := by
  rw [row, compile_coefficient _ _ _ hk, code_denote A c hc, units_eq, denominator_eq]
  rfl

/-- The universal layout row has exactly these acquired coefficients (single incidence slot). -/
theorem universal_coefficient (A : ℕ) (c : Fin R → ℤ)
    (hc : c=BinomialInterpolation.parityCoefficients (K := ℤ) A R)
    (a y : UniversalType r Q 1) (k : ℕ) (hk : k<R+1) :
    coefficient (row c a 0 y).coefficients k =
      ((LayoutUniversal.data A R (SemiprimeSourceLayout.denominatorUnit R) rfl
        (SemiprimeSourceLayout.sampleUnits Q)).row a y).coeff k :=
  row_coefficient A c hc a 0 y k hk

#print axioms row_coefficient
end RiemannGaussian.SemiprimeSourceInterpolationExecution
