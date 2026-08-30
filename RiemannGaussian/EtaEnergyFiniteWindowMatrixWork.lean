import RiemannGaussian.EtaEnergyFiniteWindowBlock
import RiemannGaussian.EtaEnergyLeadingFlux

/-!
# Matrix-valued cutoff work for finite eta zero windows

The finite eta zero-window block already retains every cross-cutoff entry of
the packed hyperbolic feature.  This module gives that matrix an exact
one-step cutoff transport law.  The increment of the packed feature is first
identified with the previously proved head-plus-prefix arithmetic increment,
including its leading/remainder splitting.  Polarization is then performed
before taking traces or norms:

`v_N v_Nᵀ - v_(N+1) v_(N+1)ᵀ`

is the increment outer product plus the two successor cross terms.  Summing
this identity over a genuine finite zero window proves a matrix-valued work
law which retains all correlations between distinct cutoff coordinates.

The outer products here are complex-symmetric transpose products, exactly as
in `pairedEtaTopPrefixFiniteZeroWindowBlock`; no complex-linear Hermitian
operator interpretation is assumed.
-/

open Complex
open scoped Classical ComplexConjugate Matrix

namespace RiemannGaussian

noncomputable section

/-! ## Generic transpose-polarization algebra -/

/-- Exact one-step polarization for a complex-symmetric outer product. -/
theorem vecMulVec_sub_vecMulVec_eq_increment_add_flux
    {d : Type*} (v w : d → ℂ) :
    Matrix.vecMulVec v v - Matrix.vecMulVec w w =
      Matrix.vecMulVec (v - w) (v - w) +
        (Matrix.vecMulVec (v - w) w + Matrix.vecMulVec w (v - w)) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
    Pi.sub_apply]
  ring

/-! ## Exact arithmetic feature increment -/

/-- Remove the parity convention from the arithmetic conjugate-original
increment, in the same way as for the static aligned term. -/
def pairedEtaTopPrefixFiniteAlignedConjugateArithmeticIncrement
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  pairedEtaTopPrefixFiniteParity rho *
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
      rho N

/-- The two-coordinate arithmetic increment corresponding to the eta
hyperbolic feature. -/
def pairedEtaTopPrefixFiniteHyperbolicArithmeticIncrement
    (rho : NontrivialZetaZero) (N : ℕ) : Fin 2 → ℂ :=
  ![
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
        rho N +
      pairedEtaTopPrefixFiniteAlignedConjugateArithmeticIncrement rho N,
    I *
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
          rho N -
        pairedEtaTopPrefixFiniteAlignedConjugateArithmeticIncrement rho N)
  ]

/-- The actual difference of consecutive eta hyperbolic features is exactly
the previously proved finite arithmetic increment in both coordinates. -/
theorem topPrefixFiniteHyperbolicFeature_sub_succ_eq_arithmeticIncrement
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaTopPrefixFiniteHyperbolicFeature rho N -
        pairedEtaTopPrefixFiniteHyperbolicFeature rho (N + 1) =
      pairedEtaTopPrefixFiniteHyperbolicArithmeticIncrement rho N := by
  funext j
  fin_cases j <;>
    simp [pairedEtaTopPrefixFiniteHyperbolicFeature,
      pairedEtaTopPrefixFiniteEvenCoordinate,
      pairedEtaTopPrefixFiniteOddCoordinate,
      pairedEtaTopPrefixFiniteAlignedConjugateTerm,
      pairedEtaTopPrefixFiniteHyperbolicArithmeticIncrement,
      pairedEtaTopPrefixFiniteAlignedConjugateArithmeticIncrement,
      Pi.sub_apply] <;>
    rw [← topPrefixFinitePartnerIncrement_eq_arithmeticIncrement,
      ← topPrefixFiniteConjugateIncrement_eq_arithmeticIncrement] <;>
    unfold
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement <;>
    ring

/-- The parity-aligned leading conjugate-original arithmetic increment. -/
def pairedEtaTopPrefixFiniteAlignedConjugateLeadingArithmeticIncrement
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  pairedEtaTopPrefixFiniteParity rho *
    pairedEtaTopPrefixFiniteConjugateLeadingArithmeticIncrement rho N

/-- The parity-aligned remainder conjugate-original arithmetic increment. -/
def pairedEtaTopPrefixFiniteAlignedConjugateRemainderArithmeticIncrement
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  pairedEtaTopPrefixFiniteParity rho *
    pairedEtaTopPrefixFiniteConjugateRemainderArithmeticIncrement rho N

/-- Leading two-coordinate part of the arithmetic feature increment. -/
def pairedEtaTopPrefixFiniteHyperbolicLeadingArithmeticIncrement
    (rho : NontrivialZetaZero) (N : ℕ) : Fin 2 → ℂ :=
  ![
    pairedEtaTopPrefixFinitePartnerLeadingArithmeticIncrement rho N +
      pairedEtaTopPrefixFiniteAlignedConjugateLeadingArithmeticIncrement rho N,
    I *
      (pairedEtaTopPrefixFinitePartnerLeadingArithmeticIncrement rho N -
        pairedEtaTopPrefixFiniteAlignedConjugateLeadingArithmeticIncrement rho N)
  ]

/-- Remainder two-coordinate part of the arithmetic feature increment. -/
def pairedEtaTopPrefixFiniteHyperbolicRemainderArithmeticIncrement
    (rho : NontrivialZetaZero) (N : ℕ) : Fin 2 → ℂ :=
  ![
    pairedEtaTopPrefixFinitePartnerRemainderArithmeticIncrement rho N +
      pairedEtaTopPrefixFiniteAlignedConjugateRemainderArithmeticIncrement rho N,
    I *
      (pairedEtaTopPrefixFinitePartnerRemainderArithmeticIncrement rho N -
        pairedEtaTopPrefixFiniteAlignedConjugateRemainderArithmeticIncrement rho N)
  ]

/-- The arithmetic hyperbolic increment is exactly its leading part plus its
remainder part, coordinate by coordinate. -/
theorem topPrefixFiniteHyperbolicArithmeticIncrement_eq_leading_add_remainder
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaTopPrefixFiniteHyperbolicArithmeticIncrement rho N =
      pairedEtaTopPrefixFiniteHyperbolicLeadingArithmeticIncrement rho N +
        pairedEtaTopPrefixFiniteHyperbolicRemainderArithmeticIncrement rho N := by
  funext j
  fin_cases j <;>
    simp [pairedEtaTopPrefixFiniteHyperbolicArithmeticIncrement,
      pairedEtaTopPrefixFiniteAlignedConjugateArithmeticIncrement,
      pairedEtaTopPrefixFiniteHyperbolicLeadingArithmeticIncrement,
      pairedEtaTopPrefixFiniteAlignedConjugateLeadingArithmeticIncrement,
      pairedEtaTopPrefixFiniteHyperbolicRemainderArithmeticIncrement,
      pairedEtaTopPrefixFiniteAlignedConjugateRemainderArithmeticIncrement,
      Pi.add_apply] <;>
    rw [topPrefixFinitePartnerArithmeticIncrement_eq_leading_add_remainder,
      topPrefixFiniteConjugateArithmeticIncrement_eq_leading_add_remainder] <;>
    ring

/-! ## Packed increments and the finite-window matrix law -/

/-- Shift every member of a finite cutoff family forward by one. -/
def pairedEtaTopPrefixFiniteSuccessorCutoff
    {d : Type*} (cutoff : d → ℕ) : d → ℕ :=
  fun j ↦ cutoff j + 1

/-- The literal difference between a packed cutoff feature and its
simultaneously shifted successor. -/
def pairedEtaTopPrefixFiniteCutoffFamilyIncrement
    {d : Type*} (cutoff : d → ℕ) (rho : NontrivialZetaZero) :
    d × Fin 2 → ℂ :=
  pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho -
    pairedEtaTopPrefixFiniteCutoffFamilyFeature
      (pairedEtaTopPrefixFiniteSuccessorCutoff cutoff) rho

/-- Pack the exact arithmetic hyperbolic increments at a finite family of
cutoffs. -/
def pairedEtaTopPrefixFiniteCutoffFamilyArithmeticIncrement
    {d : Type*} (cutoff : d → ℕ) (rho : NontrivialZetaZero) :
    d × Fin 2 → ℂ :=
  fun j ↦
    pairedEtaTopPrefixFiniteHyperbolicArithmeticIncrement rho (cutoff j.1) j.2

/-- The packed literal feature increment is exactly the packed arithmetic
increment at every cutoff and hyperbolic coordinate. -/
theorem topPrefixFiniteCutoffFamilyIncrement_eq_arithmeticIncrement
    {d : Type*} (cutoff : d → ℕ) (rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteCutoffFamilyIncrement cutoff rho =
      pairedEtaTopPrefixFiniteCutoffFamilyArithmeticIncrement cutoff rho := by
  funext j
  exact congrFun
    (topPrefixFiniteHyperbolicFeature_sub_succ_eq_arithmeticIncrement
      rho (cutoff j.1)) j.2

/-- Consecutive work of the complete finite eta zero-window matrix when every
cutoff in the packed family advances by one. -/
def pairedEtaTopPrefixFiniteZeroWindowMatrixWork
    {d : Type*} (cutoff : d → ℕ) (T : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T -
    pairedEtaTopPrefixFiniteZeroWindowBlock
      (pairedEtaTopPrefixFiniteSuccessorCutoff cutoff) T

/-- Multiplicity-weighted outer-product energy of the exact packed arithmetic
feature increments on a finite zero window. -/
def pairedEtaTopPrefixFiniteZeroWindowMatrixIncrementEnergy
    {d : Type*} (cutoff : d → ℕ) (T : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    (analyticZetaZeroMultiplicity rho : ℂ) •
      Matrix.vecMulVec
        (pairedEtaTopPrefixFiniteCutoffFamilyIncrement cutoff rho)
        (pairedEtaTopPrefixFiniteCutoffFamilyIncrement cutoff rho)

/-- The two successor cross terms in the matrix-valued cutoff transport law. -/
def pairedEtaTopPrefixFiniteZeroWindowMatrixFlux
    {d : Type*} (cutoff : d → ℕ) (T : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    (analyticZetaZeroMultiplicity rho : ℂ) •
      (Matrix.vecMulVec
          (pairedEtaTopPrefixFiniteCutoffFamilyIncrement cutoff rho)
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature
            (pairedEtaTopPrefixFiniteSuccessorCutoff cutoff) rho) +
        Matrix.vecMulVec
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature
            (pairedEtaTopPrefixFiniteSuccessorCutoff cutoff) rho)
          (pairedEtaTopPrefixFiniteCutoffFamilyIncrement cutoff rho))

/-- Exact matrix-valued cutoff work: the difference of consecutive finite
zero-window blocks is increment energy plus successor cross flux. -/
theorem topPrefixFiniteZeroWindowMatrixWork_eq_incrementEnergy_add_flux
    {d : Type*} (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowMatrixWork cutoff T =
      pairedEtaTopPrefixFiniteZeroWindowMatrixIncrementEnergy cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowMatrixFlux cutoff T := by
  unfold pairedEtaTopPrefixFiniteZeroWindowMatrixWork
    pairedEtaTopPrefixFiniteZeroWindowBlock
    pairedEtaTopPrefixFiniteZeroWindowMatrixIncrementEnergy
    pairedEtaTopPrefixFiniteZeroWindowMatrixFlux
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho _hrho
  rw [← smul_sub,
    vecMulVec_sub_vecMulVec_eq_increment_add_flux,
    smul_add]
  rfl

/-- Entrywise form of the matrix cutoff work law.  In particular, choosing
distinct cutoff coordinates retains their cross-scale correlation rather than
collapsing the identity to a trace. -/
theorem topPrefixFiniteZeroWindowMatrixWork_apply
    {d : Type*} (cutoff : d → ℕ) (T : ℝ) (i j : d × Fin 2) :
    pairedEtaTopPrefixFiniteZeroWindowMatrixWork cutoff T i j =
      pairedEtaTopPrefixFiniteZeroWindowMatrixIncrementEnergy cutoff T i j +
        pairedEtaTopPrefixFiniteZeroWindowMatrixFlux cutoff T i j := by
  exact congrArg (fun M : Matrix (d × Fin 2) (d × Fin 2) ℂ ↦ M i j)
    (topPrefixFiniteZeroWindowMatrixWork_eq_incrementEnergy_add_flux cutoff T)

/-- Fully opened entrywise arithmetic form of the matrix work.  Each entry
retains the correlation between its two independently selected cutoff and
hyperbolic coordinates. -/
theorem topPrefixFiniteZeroWindowMatrixWork_apply_eq_arithmeticCorrelation
    {d : Type*} (cutoff : d → ℕ) (T : ℝ) (i j : d × Fin 2) :
    pairedEtaTopPrefixFiniteZeroWindowMatrixWork cutoff T i j =
      ∑ rho ∈ spectralZetaZeroWindow T,
        (analyticZetaZeroMultiplicity rho : ℂ) *
          (pairedEtaTopPrefixFiniteCutoffFamilyArithmeticIncrement cutoff rho i *
                pairedEtaTopPrefixFiniteCutoffFamilyArithmeticIncrement cutoff rho j +
            pairedEtaTopPrefixFiniteCutoffFamilyArithmeticIncrement cutoff rho i *
                pairedEtaTopPrefixFiniteCutoffFamilyFeature
                  (pairedEtaTopPrefixFiniteSuccessorCutoff cutoff) rho j +
            pairedEtaTopPrefixFiniteCutoffFamilyFeature
                  (pairedEtaTopPrefixFiniteSuccessorCutoff cutoff) rho i *
                pairedEtaTopPrefixFiniteCutoffFamilyArithmeticIncrement cutoff rho j) := by
  rw [topPrefixFiniteZeroWindowMatrixWork_apply]
  unfold pairedEtaTopPrefixFiniteZeroWindowMatrixIncrementEnergy
    pairedEtaTopPrefixFiniteZeroWindowMatrixFlux
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho _hrho
  rw [topPrefixFiniteCutoffFamilyIncrement_eq_arithmeticIncrement]
  ring

end

end RiemannGaussian
