/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseContactSystem
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Contact geometry and the primal coefficient row

The diagonal contact secant has an exact nine-by-nine matrix. Its final
inverse row, when the matrix is invertible, is the unique cost-normalized
coefficient family with the specified contact values and slopes. This
preserves the link between the dual contact geometry and the primal phase
kernel; positivity of the primal kernel is a further obligation.
-/

open scoped Classical
open Matrix

namespace RiemannGaussian

noncomputable section

/-- The full diagonal linearization of the contact equations, preserving
both cosine and contact-mass columns. -/
def phaseContactJacobian (u : Fin 9 → ℝ) : Matrix (Fin 9) (Fin 9) ℝ := fun i ↦
  let n := phaseContactFrequency i
  ![-u 4 * phaseChebyshevSecant (u 0) (u 0) n,
    -u 5 * phaseChebyshevSecant (u 1) (u 1) n,
    -u 6 * phaseChebyshevSecant (u 2) (u 2) n,
    -u 7 * phaseChebyshevSecant (u 3) (u 3) n,
    -phaseChebyshevValue n (u 0), -phaseChebyshevValue n (u 1),
    -phaseChebyshevValue n (u 2), -phaseChebyshevValue n (u 3),
    phaseContactCost n]

/-- The matrix and exact diagonal secant are the same linear action. -/
theorem phaseContactJacobian_mulVec (u h : Fin 9 → ℝ) :
    phaseContactJacobian u *ᵥ h = phaseContactSecantAction u u h := by
  ext i
  simp only [phaseContactJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  unfold phaseContactSecantAction
  simp only [Fin.sum_univ_succ, phaseContactMassCoordinate, phaseContactCosineCoordinate]
  dsimp
  ring

/-- The efficiency column is exactly the cost at every support frequency. -/
theorem phaseContactJacobian_cost_column (u : Fin 9 → ℝ) (i : Fin 9) :
    phaseContactJacobian u i 8 = phaseContactCost (phaseContactFrequency i) := rfl

/-- Contact-mass columns are the signed kernel values. -/
theorem phaseContactJacobian_mass_column (u : Fin 9 → ℝ) (i : Fin 9) (j : Fin 4) :
    phaseContactJacobian u i (phaseContactMassCoordinate j) =
      -phaseChebyshevValue (phaseContactFrequency i) (u (phaseContactCosineCoordinate j)) := by
  fin_cases j <;> rfl

/-- Contact-cosine columns retain the mass and signed kernel slope. -/
theorem phaseContactJacobian_cosine_column (u : Fin 9 → ℝ) (i : Fin 9) (j : Fin 4) :
    phaseContactJacobian u i (phaseContactCosineCoordinate j) =
      -u (phaseContactMassCoordinate j) * phaseChebyshevSecant
        (u (phaseContactCosineCoordinate j)) (u (phaseContactCosineCoordinate j))
          (phaseContactFrequency i) := by
  fin_cases j <;> rfl

/-- The final inverse row is the proposed cost-normalized primal family.
Its geometric properties are proved only when the matrix is invertible. -/
def phaseContactPrimalRow (u : Fin 9 → ℝ) : Fin 9 → ℝ := (phaseContactJacobian u)⁻¹ 8

private theorem phaseContactPrimalRow_identity {u : Fin 9 → ℝ}
    (hJ : IsUnit (phaseContactJacobian u)) (k : Fin 9) :
    ∑ i : Fin 9, phaseContactPrimalRow u i * phaseContactJacobian u i k = if 8 = k then 1 else 0 := by
  have h := congrArg (fun M : Matrix (Fin 9) (Fin 9) ℝ ↦ M 8 k)
    (Matrix.nonsing_inv_mul (phaseContactJacobian u)
      ((Matrix.isUnit_iff_isUnit_det (phaseContactJacobian u)).mp hJ))
  simpa only [Matrix.mul_apply, Matrix.one_apply, phaseContactPrimalRow] using h

/-- The inverse row normalizes the actual linear height cost to one. -/
theorem phaseContactPrimalRow_cost {u : Fin 9 → ℝ} (hJ : IsUnit (phaseContactJacobian u)) :
    ∑ i : Fin 9, phaseContactPrimalRow u i * phaseContactCost (phaseContactFrequency i) = 1 := by
  simpa only [phaseContactJacobian_cost_column, ↓reduceIte] using phaseContactPrimalRow_identity hJ 8

/-- Each dual contact is an exact zero of the inverse-row phase kernel. -/
theorem phaseContactPrimalRow_contact {u : Fin 9 → ℝ} (hJ : IsUnit (phaseContactJacobian u))
    (j : Fin 4) :
    ∑ i : Fin 9, phaseContactPrimalRow u i *
      phaseChebyshevValue (phaseContactFrequency i) (u (phaseContactCosineCoordinate j)) = 0 := by
  have hne : (8 : Fin 9) ≠ phaseContactMassCoordinate j := by
    intro h
    have := congrArg Fin.val h
    dsimp [phaseContactMassCoordinate] at this
    omega
  have h := phaseContactPrimalRow_identity hJ (phaseContactMassCoordinate j)
  simp only [phaseContactJacobian_mass_column, mul_neg, Finset.sum_neg_distrib, if_neg hne,
    neg_eq_zero] at h
  exact h

/-- Nonzero contact mass forces an exact zero slope at that same contact. -/
theorem phaseContactPrimalRow_contact_slope {u : Fin 9 → ℝ} (hJ : IsUnit (phaseContactJacobian u))
    (j : Fin 4) (hm : u (phaseContactMassCoordinate j) ≠ 0) :
    ∑ i : Fin 9, phaseContactPrimalRow u i * phaseChebyshevSecant
      (u (phaseContactCosineCoordinate j)) (u (phaseContactCosineCoordinate j))
        (phaseContactFrequency i) = 0 := by
  have hne : (8 : Fin 9) ≠ phaseContactCosineCoordinate j := by
    intro h
    have := congrArg Fin.val h
    dsimp [phaseContactCosineCoordinate] at this
    omega
  have h := phaseContactPrimalRow_identity hJ (phaseContactCosineCoordinate j)
  simp only [phaseContactJacobian_cosine_column, if_neg hne] at h
  have he : (∑ i : Fin 9, phaseContactPrimalRow u i *
      (-u (phaseContactMassCoordinate j) * phaseChebyshevSecant
        (u (phaseContactCosineCoordinate j)) (u (phaseContactCosineCoordinate j))
          (phaseContactFrequency i))) =
      -u (phaseContactMassCoordinate j) * ∑ i : Fin 9, phaseContactPrimalRow u i *
        phaseChebyshevSecant (u (phaseContactCosineCoordinate j)) (u (phaseContactCosineCoordinate j))
          (phaseContactFrequency i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at h
  exact (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr hm)

/-- The final inverse row is uniquely characterized by the nine linear
contact equations and its cost normalization. -/
theorem phaseContactPrimalRow_unique {u a : Fin 9 → ℝ} (hJ : IsUnit (phaseContactJacobian u))
    (ha : ∀ k : Fin 9, ∑ i : Fin 9, a i * phaseContactJacobian u i k =
      if 8 = k then 1 else 0) : a = phaseContactPrimalRow u := by
  apply (Matrix.vecMul_injective_iff_isUnit.mpr hJ)
  ext k
  exact (ha k).trans (phaseContactPrimalRow_identity hJ k).symm

/-- At a solution of the dual system, the inverse row attains the exact
source value equal to the efficiency parameter, with cost one. This is
an algebraic equality; feasibility still requires global kernel positivity. -/
theorem phaseContactPrimalRow_source {u : Fin 9 → ℝ} (hJ : IsUnit (phaseContactJacobian u))
    (hF : phaseContactSystem u = 0) :
    ∑ i : Fin 9, phaseContactPrimalRow u i * phaseContactSourceCoeff (phaseContactFrequency i) = u 8 := by
  have hs (i : Fin 9) : phaseContactSourceCoeff (phaseContactFrequency i) =
      u 8 * phaseContactCost (phaseContactFrequency i) -
        ∑ j : Fin 4, u (phaseContactMassCoordinate j) *
          phaseChebyshevValue (phaseContactFrequency i) (u (phaseContactCosineCoordinate j)) := by
    have h := congrFun hF i
    change phaseContactSystem u i = 0 at h
    unfold phaseContactSystem at h
    linarith
  have hcontacts : (∑ i : Fin 9, phaseContactPrimalRow u i *
      (∑ j : Fin 4, u (phaseContactMassCoordinate j) *
        phaseChebyshevValue (phaseContactFrequency i) (u (phaseContactCosineCoordinate j)))) = 0 := by
    calc
      _ = ∑ i : Fin 9, ∑ j : Fin 4, u (phaseContactMassCoordinate j) *
          (phaseContactPrimalRow u i *
            phaseChebyshevValue (phaseContactFrequency i) (u (phaseContactCosineCoordinate j))) := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ j : Fin 4, u (phaseContactMassCoordinate j) *
          (∑ i : Fin 9, phaseContactPrimalRow u i *
            phaseChebyshevValue (phaseContactFrequency i) (u (phaseContactCosineCoordinate j))) := by
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
      _ = 0 := by simp only [phaseContactPrimalRow_contact hJ, mul_zero, Finset.sum_const_zero]
  have hcost : (∑ i : Fin 9, phaseContactPrimalRow u i *
      (u 8 * phaseContactCost (phaseContactFrequency i))) = u 8 := by
    calc
      _ = u 8 * (∑ i : Fin 9, phaseContactPrimalRow u i * phaseContactCost (phaseContactFrequency i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = u 8 := by rw [phaseContactPrimalRow_cost hJ, mul_one]
  simp_rw [hs, mul_sub, Finset.sum_sub_distrib]
  rw [hcost, hcontacts, sub_zero]

/-- The diagonal Chebyshev secant is the true derivative, including
at the contact coordinates where no division by a separation is allowed. -/
theorem hasDerivAt_phaseChebyshevValue (n : ℕ) (x : ℝ) :
    HasDerivAt (phaseChebyshevValue n) (phaseChebyshevSecant x x n) x := by
  induction n using Nat.twoStepInduction with
  | zero =>
    have he : phaseChebyshevValue 0 = fun _ : ℝ ↦ 1 := by ext y; simp [phaseChebyshevValue]
    rw [he, phaseChebyshevSecant]
    exact hasDerivAt_const x (1 : ℝ)
  | one =>
    have he : phaseChebyshevValue 1 = id := by ext y; simp [phaseChebyshevValue]
    rw [he, phaseChebyshevSecant]
    exact hasDerivAt_id x
  | more n ih0 ih1 =>
    have he : phaseChebyshevValue (n + 2) = fun y : ℝ ↦
        2 * y * phaseChebyshevValue (n + 1) y - phaseChebyshevValue n y := by
      ext y
      simp [phaseChebyshevValue, Polynomial.Chebyshev.T_add_two]
    rw [he, phaseChebyshevSecant]
    convert (((hasDerivAt_id x).const_mul 2).mul ih1).sub ih0 using 1 <;>
      first | rfl | (simp only [id_eq]; ring)

end

end RiemannGaussian
