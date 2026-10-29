/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PhysicalRecoveryLocalBudget
import RiemannGaussian.SemiprimeReportPolynomialGrowth

/-! # Fixed polynomial of actual original physical recovery dimensions
The original grid size is a separate dimension N, rather than replacing it by
2^S in a diagonal envelope. All producer/metadata/copy reports remain included.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1PhysicalRecoveryPolynomial
open SemiprimeReportPolynomialGrowth

/-- Original-derived scalar store width with the literal grid size explicit. -/
def scalarWidth (a M N P : ℕ) : ℕ :=
  SemiprimeD1RecoveryNodeBits.widthPolynomial a M N+
    SemiprimeD1IntegerRecoveryHeight.recoveryPolynomial a M N P+P+
    SemiprimeD1HermiteWeightBits.weightPolynomial a M N+20

/-- Actual node arithmetic/copy polynomial with explicit grid dimension. -/
def nodeClock (a M N W : ℕ) : ℕ :=
  let m:=4*M
  (2*a+1)*(20000*(W+1)^3+4)+N*SemiprimeD1RecoveryGridBits.frameBudget W m+
  6*(20000*(W+1)^3)+40+
  (4+N*m*SemiprimeAffineJetBits.stepBudget W m)+
  (1+m*SemiprimeNormalizedInverseBitsBounds.stepBudget W (m+1) m)+
  (m*(8*W+9)+1)+(m*(m*(20000*(W+1)^3+4)+6)+1)+
  (m*(m*SemiprimeD1RecoveryScalarWeightBits.sumStepBudget W m m+20000*(W+1)^3+10)+1)+3*W+30

/-- Original full-grid row producer polynomial. -/
def rowsClock (a M N : ℕ) : ℕ :=
  let W:=SemiprimeD1RecoveryNodeBits.widthPolynomial a M N
  N*(nodeClock a M N W+(4*M)*(8*W+9)+4)+4

/-- Actual physical common-denominator arithmetic and finalizer polynomial. -/
def scalarClock (a M N p P : ℕ) : ℕ :=
  let m:=4*M
  let W:=scalarWidth a M N P
  let K:=N*m
  rowsClock a M N+
  (K*(SemiprimeD1RecoveryPhysicalBounds.readBudget N m P (N+m+1)+4)+1)+
  (K*(40*(W+1)^2+23)+3)+(K*(300*(W+1)^2+100)+3)+
  SemiprimeD1RecoveryStripBits.budget p W+3*W+10

/-- Actual source-node metadata polynomial at explicit grid size. -/
def nodeMetadata (a M N : ℕ) : ℕ :=
  3*a+308+SemiprimeD1RecoveryMetadataBudget.nodeBodyBudget a N (4*M)
    (SemiprimeD1RecoveryNodeBits.widthPolynomial a M N)

/-- Actual full-grid source metadata polynomial. -/
def rowsMetadata (a M N : ℕ) : ℕ :=
  (3*a+8+(N*N+4*N+1)+4*N+3)+N*(nodeMetadata a M N+5*(4*M)+7)+4

/-- Actual whole scalar-recovery metadata polynomial. -/
def scalarMetadata (a M N : ℕ) : ℕ :=
  rowsMetadata a M N+N*(4*M)*(8*(N+4*M+1)+6)+1+9*a+744

/-- Every original coordinate report, with all physical/native/copy work. -/
def coordinateBudget (a M N p rank P : ℕ) : ℕ :=
  N*(4*M*(3*rank+3*P+10)+8)+3+scalarClock a M N p P+scalarMetadata a M N+
    (5*N+5*(N*(4*M))+3)+7

/-- The resource polynomial is exactly the existing ACTUAL original local budget. -/
theorem budget_eq (a M p rank P : ℕ) :
    SemiprimeD1PhysicalRecoveryLocalBudget.budget a M p rank P=
      coordinateBudget a M (SemiprimeD1WireKernelOriginal.size a) p rank P := by
  simp only [SemiprimeD1PhysicalRecoveryLocalBudget.budget,
    SemiprimeD1RecoveryPhysicalBounds.budget,SemiprimeD1RecoveryRowsBits.budget,
    SemiprimeD1RecoveryRowsBits.nodeBudget,SemiprimeD1RecoveryNodeBitsBounds.budget,
    SemiprimeD1RecoveryGridBitsBounds.budget,SemiprimeD1RecoveryNodeBits.slopeCount,
    SemiprimeD1RecoveryNodeBits.m,SemiprimeD1RecoveryNodeBits.width,
    SemiprimeD1RecoveryPhysicalRun.width,SemiprimeD1IntegerRecoveryHeight.recoveryExponent_eq,
    SemiprimeD1HermiteWeightBits.weightEnvelope_eq,
    SemiprimeD1RecoveryMetadataBudget.budget,SemiprimeD1RecoveryMetadataBudget.rowsBudget,
    SemiprimeD1RecoveryMetadataBudget.nodeBudget,coordinateBudget,scalarClock,scalarMetadata,
    rowsClock,nodeClock,rowsMetadata,nodeMetadata,scalarWidth,Nat.mul_one]

/-- Componentwise nonnegative scalar monotonicity, independent of runtime contexts. -/
theorem coordinateBudget_mono {a M N p rank P a' M' N' p' rank' P' : ℕ}
    (ha : a ≤ a') (hM : M ≤ M') (hN : N ≤ N') (hp : p ≤ p')
    (hrank : rank ≤ rank') (hP : P ≤ P') :
    coordinateBudget a M N p rank P ≤ coordinateBudget a' M' N' p' rank' P' := by
  unfold coordinateBudget scalarClock scalarMetadata rowsClock nodeClock rowsMetadata nodeMetadata
    scalarWidth SemiprimeD1RecoveryNodeBits.widthPolynomial
    SemiprimeD1IntegerRecoveryHeight.recoveryPolynomial
    SemiprimeD1HermiteWeightBits.weightPolynomial SemiprimeD1HermiteWeightBits.inversePolynomial
    SemiprimeAffineJetBits.width SemiprimeNormalizedInverseBits.inverseWidth
    SemiprimeD1RecoveryGridBits.frameBudget SemiprimeAffineJetBits.stepBudget
    SemiprimeNormalizedInverseBitsBounds.stepBudget SemiprimeD1RecoveryScalarWeightBits.sumStepBudget
    SemiprimeD1RecoveryPhysicalBounds.readBudget SemiprimeD1RecoveryStripBits.budget
    SemiprimeD1RecoveryMetadataBudget.nodeBodyBudget SemiprimeD1RecoveryMetadataBudget.gridBudget
  dsimp only
  gcongr

/-- Fixed diagonal resource envelope of all actual coordinate work. -/
def envelope (S : ℕ) : ℕ := coordinateBudget S S S S S S

/-- The actual recovery budget is fixed-polynomial in original scalar/grid/rank caps. -/
theorem budget_le_envelope (a M p rank P S : ℕ)
    (ha : a ≤ S) (hM : M ≤ S) (hN : SemiprimeD1WireKernelOriginal.size a ≤ S)
    (hp : p ≤ S) (hrank : rank ≤ S) (hP : P ≤ S) :
    SemiprimeD1PhysicalRecoveryLocalBudget.budget a M p rank P ≤ envelope S := by
  rw [budget_eq]
  exact coordinateBudget_mono ha hM hN hp hrank hP

/-- Fixed monomial witnesses are derived from the literal polynomial expression. -/
theorem envelope_monomial : Bound envelope := by
  unfold envelope coordinateBudget scalarClock scalarMetadata rowsClock nodeClock rowsMetadata nodeMetadata
    scalarWidth SemiprimeD1RecoveryNodeBits.widthPolynomial
    SemiprimeD1IntegerRecoveryHeight.recoveryPolynomial
    SemiprimeD1HermiteWeightBits.weightPolynomial SemiprimeD1HermiteWeightBits.inversePolynomial
    SemiprimeAffineJetBits.width SemiprimeNormalizedInverseBits.inverseWidth
    SemiprimeD1RecoveryGridBits.frameBudget SemiprimeAffineJetBits.stepBudget
    SemiprimeNormalizedInverseBitsBounds.stepBudget SemiprimeD1RecoveryScalarWeightBits.sumStepBudget
    SemiprimeD1RecoveryPhysicalBounds.readBudget SemiprimeD1RecoveryStripBits.budget
    SemiprimeD1RecoveryMetadataBudget.nodeBodyBudget SemiprimeD1RecoveryMetadataBudget.gridBudget
  dsimp only
  boundArithmetic

end RiemannGaussian.SemiprimeD1PhysicalRecoveryPolynomial
