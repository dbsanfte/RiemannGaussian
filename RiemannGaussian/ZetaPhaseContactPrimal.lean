/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseContactRoot

/-!
# The exact coefficient family determined by four contacts

The isolated contact solution has an invertible linearization. Its final
inverse row supplies an exact real coefficient family with cost one,
source equal to the contact efficiency, and four simultaneous zero values
and zero derivatives. The family is uniquely characterized by these
geometric conditions inside the selected nine-frequency span.

This is an exact structural candidate, not a numerical coefficient table.
All nine coefficients are strictly positive, including the tiny highest
frequency. Global kernel nonnegativity is a separate remaining obligation
for optimality.
-/

open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The exact coefficients obtained from the proved contact geometry. -/
def phaseContactExactCoefficients : Fin 9 → ℝ := phaseContactPrimalRow phaseContactExactRoot

/-- The polynomial kernel in its cosine coordinate, retaining each
selected frequency as a separate summand. -/
def phaseContactExactKernel (x : ℝ) : ℝ :=
  ∑ i : Fin 9, phaseContactExactCoefficients i * phaseChebyshevValue (phaseContactFrequency i) x

/-- Every coefficient in the exact family is strictly positive. Thus the
highest-frequency coefficient is not a floating-point or rounding artifact. -/
theorem phaseContactExactCoefficients_pos (i : Fin 9) : 0 < phaseContactExactCoefficients i := by
  have hb : (1 / 2000000 : ℝ) ≤ (phaseContactRootPreconditionerQ 8 i : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr (phaseContactRootPreconditionerQ_last_row_pos i)
  have h := (abs_le.mp (abs_phaseContactExactRoot_inverse_sub_le 8 i)).1
  change 0 < (phaseContactJacobian phaseContactExactRoot)⁻¹ 8 i
  linarith

/-- The kernel is the actual trigonometric phase sum after substituting a cosine. -/
theorem phaseContactExactKernel_cos (t : ℝ) :
    phaseContactExactKernel (Real.cos t) =
      ∑ i : Fin 9, phaseContactExactCoefficients i * Real.cos ((phaseContactFrequency i : ℝ) * t) := by
  simp only [phaseContactExactKernel, phaseChebyshevValue_cos]

/-- The mathematically defined family has exactly unit linear height cost. -/
theorem phaseContactExactCoefficients_cost :
    ∑ i : Fin 9, phaseContactExactCoefficients i * phaseContactCost (phaseContactFrequency i) = 1 :=
  phaseContactPrimalRow_cost isUnit_phaseContactExactRoot_jacobian

/-- Its source value is exactly the efficiency coordinate of the contact root. -/
theorem phaseContactExactCoefficients_source :
    ∑ i : Fin 9, phaseContactExactCoefficients i * phaseContactSourceCoeff (phaseContactFrequency i) =
      phaseContactExactRoot 8 :=
  phaseContactPrimalRow_source isUnit_phaseContactExactRoot_jacobian phaseContactExactRoot_system

/-- All four contact values vanish exactly, rather than only on a sampled grid. -/
theorem phaseContactExactKernel_contact (j : Fin 4) :
    phaseContactExactKernel (phaseContactExactRoot (phaseContactCosineCoordinate j)) = 0 :=
  phaseContactPrimalRow_contact isUnit_phaseContactExactRoot_jacobian j

/-- The same exact family has zero diagonal-secant slope at all four contacts. -/
theorem phaseContactExactCoefficients_contact_slope (j : Fin 4) :
    ∑ i : Fin 9, phaseContactExactCoefficients i * phaseChebyshevSecant
      (phaseContactExactRoot (phaseContactCosineCoordinate j))
      (phaseContactExactRoot (phaseContactCosineCoordinate j)) (phaseContactFrequency i) = 0 :=
  phaseContactPrimalRow_contact_slope isUnit_phaseContactExactRoot_jacobian j
    (ne_of_gt (phaseContactExactRoot_mass_pos j))

/-- Each contact is a true stationary point of the full polynomial kernel. -/
theorem hasDerivAt_phaseContactExactKernel_contact (j : Fin 4) :
    HasDerivAt phaseContactExactKernel 0 (phaseContactExactRoot (phaseContactCosineCoordinate j)) := by
  have h := HasDerivAt.sum (u := (Finset.univ : Finset (Fin 9)))
    (fun i _ ↦ (hasDerivAt_phaseChebyshevValue (phaseContactFrequency i)
      (phaseContactExactRoot (phaseContactCosineCoordinate j))).const_mul (phaseContactExactCoefficients i))
  rw [phaseContactExactCoefficients_contact_slope j] at h
  exact h

/-- Cost, contact values, and contact slopes determine the entire family
uniquely inside the nine-frequency span. No coefficients are supplied as hypotheses. -/
theorem phaseContactExactCoefficients_unique {a : Fin 9 → ℝ}
    (hcost : ∑ i : Fin 9, a i * phaseContactCost (phaseContactFrequency i) = 1)
    (hcontact : ∀ j : Fin 4, ∑ i : Fin 9, a i * phaseChebyshevValue (phaseContactFrequency i)
      (phaseContactExactRoot (phaseContactCosineCoordinate j)) = 0)
    (hslope : ∀ j : Fin 4, ∑ i : Fin 9, a i * phaseChebyshevSecant
      (phaseContactExactRoot (phaseContactCosineCoordinate j))
      (phaseContactExactRoot (phaseContactCosineCoordinate j)) (phaseContactFrequency i) = 0) :
    a = phaseContactExactCoefficients := by
  apply phaseContactPrimalRow_unique isUnit_phaseContactExactRoot_jacobian
  have hv (j : Fin 4) : ∑ i : Fin 9, a i *
      phaseContactJacobian phaseContactExactRoot i (phaseContactMassCoordinate j) = 0 := by
    simp only [phaseContactJacobian_mass_column, mul_neg, Finset.sum_neg_distrib, hcontact j, neg_zero]
  have hd (j : Fin 4) : ∑ i : Fin 9, a i *
      phaseContactJacobian phaseContactExactRoot i (phaseContactCosineCoordinate j) = 0 := by
    rw [show (∑ i : Fin 9, a i * phaseContactJacobian phaseContactExactRoot i (phaseContactCosineCoordinate j)) =
      -phaseContactExactRoot (phaseContactMassCoordinate j) *
        (∑ i : Fin 9, a i * phaseChebyshevSecant
          (phaseContactExactRoot (phaseContactCosineCoordinate j))
          (phaseContactExactRoot (phaseContactCosineCoordinate j)) (phaseContactFrequency i)) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [phaseContactJacobian_cosine_column]
      ring]
    rw [hslope j, mul_zero]
  intro k
  fin_cases k <;>
    first | exact hd 0 | exact hd 1 | exact hd 2 | exact hd 3 |
      exact hv 0 | exact hv 1 | exact hv 2 | exact hv 3 | exact hcost

end

end RiemannGaussian
