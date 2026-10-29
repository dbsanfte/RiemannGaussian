/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeFullSetupBudget

/-! # Fixed polynomial closure of the actual setup envelope
Only the bit-width bound enters the selector dimensions. The large integer
measurement magnitude is not an independent dimension here. This comparison
bounds the existing mixed execution ledger, not a literal machine clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace RiemannGaussian.SemiprimeSetupPolynomialEnvelope

/-- Diagonal fixed-polynomial setup envelope. Its dependencies contain only
addition, multiplication and fixed natural powers, after the paid universal
alphabet has replaced the variable-size subset expansion. -/
def polynomialEnvelope (S : ℕ) : ℕ :=
  SemiprimeFullSetupBudget.setupBudget S S S S S S S S S

/-- Every actual setup dimension may be replaced by a common upper bound.
The selector width is recomputed from B,Q,R; no measurement-magnitude advice,
intermediate Fits or precomputed setup result is assumed. -/
theorem setupBudget_le_envelope (n F M r Q R B D A S : ℕ)
    (hn : n≤S) (hF : F≤S) (hM : M≤S) (hr : r≤S) (hQ : Q≤S)
    (hR : R≤S) (hB : B≤S) (hD : D≤S) (hA : A≤S) :
    SemiprimeFullSetupBudget.setupBudget n F M r Q R B D A ≤ polynomialEnvelope S := by
  unfold polynomialEnvelope
  simp only [SemiprimeFullSetupBudget.setupBudget,SemiprimeFullSetupBudget.sourceBudget,
    SemiprimeFullSetupBudget.rawBudget,SemiprimeFullSetupBudget.designBudget,
    SemiprimePaidFiniteEnumerations.polynomial,SemiprimePaidFiniteEnumerations.incidenceBudget,
    SemiprimePaidFiniteEnumerations.wordPolynomial,SemiprimePaidFiniteEnumerations.universalPolynomial,
    SemiprimePaidFiniteEnumerations.scoreBudget,SemiprimePaidSourceMetadata.budget,
    SemiprimePaidOriginalConstraints.polynomial,SemiprimePaidConstraintAcquisition.polynomial,
    SemiprimePaidConstraintAcquisition.universalPolynomial,SemiprimePaidConstraintAcquisition.tableBudget,
    SemiprimeMaterializedSourceWords.producerBudget,SemiprimeMaterializedScoreSearch.evaluatorBudget,
    SemiprimeMaterializedScoreEnvironment.terminalBudget,
    SemiprimeMaterializedSourceAcquisition.packingBudget,
    SemiprimeMaterializedSourceRows.rowPolynomial,SemiprimeMaterializedSourceRows.rowAuxiliary,
    SemiprimeMaterializedSourceUniversal.entryPolynomial,
    SemiprimePaidMeasurementBound.bits,SemiprimePaidRuntimeDesign.groupBudget,
    SemiprimeEncodedRowSelection.budget,SemiprimeRowSelectionBits.runBudget,
    SemiprimeRowSelectionBits.insertBudget,SemiprimeRowSelectionBits.residualRowBudget,
    SemiprimeRowSelectionBits.normalizeRowBudget,SemiprimeRowSelectionBits.updateRowBudget,
    SemiprimeRowSelectionBitArithmetic.residualBudget,
    SemiprimeMaterializedSelectionTemporaries.selectorWidth,
    SemiprimeMaterializedSelectionTemporaries.leafBits,
    SemiprimeMaterializedSelectionTemporaries.residualBits,
    SemiprimeMaterializedSelectionTemporaries.normalizeBits,
    SemiprimeMaterializedSelectionTemporaries.updateBits]
  gcongr

/-- A larger common resource bound increases the same fixed setup polynomial. -/
theorem polynomialEnvelope_mono : Monotone polynomialEnvelope := by
  intro S T h
  exact setupBudget_le_envelope S S S S S S S S S T h h h h h h h h h

end RiemannGaussian.SemiprimeSetupPolynomialEnvelope
