/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceClassifiedSearchBudget

/-! # Uniform original-resource bound for the actual acquired-ID source caller
Only original dimension caps occur in the final executed-report theorem. No unary universal-alphabet initialization is used. All
constants in the diagonal monomial precede the entire family of original inputs.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
namespace RiemannGaussian.SemiprimeSourceClassifiedResources
open scoped BigOperators
open SemiprimeReportPolynomialGrowth

/-- Actual complete original-caller budget is monotone in its nine independent resources. -/
theorem indexedBudget_mono {n F r Q lam M L T N n' F' r' Q' lam' M' L' T' N' : ℕ}
    (hn : n≤n') (hF : F≤F') (hr : r≤r') (hQ : Q≤Q') (hlam : lam≤lam')
    (hM : M≤M') (hL : L≤L') (hT : T≤T') (hN : N≤N') :
    SemiprimeSourceClassifiedSearchBudget.indexedBudget n F r Q lam M L T N ≤
      SemiprimeSourceClassifiedSearchBudget.indexedBudget n' F' r' Q' lam' M' L' T' N' := by
  simp only [SemiprimeSourceClassifiedSearchBudget.indexedBudget,
    SemiprimeSourceClassifiedSearchBudget.runBudget,SemiprimeSourceClassifiedSearchBudget.controlBudget,
    SemiprimeSourceClassifiedSearchBudget.wordCap,SemiprimeSourceClassifiedSearchBudget.weightCap,
    SemiprimeSourceWordIdMetadata.budget,SemiprimePaidFiniteEnumerations.incidenceBudget,
    SemiprimePaidFiniteEnumerations.scoreBudget,SemiprimeSourceWordBankAcquisitionBudget.budget,
    SemiprimeSourceWordBankAcquisitionBudget.colourBudget,SemiprimeSourceWordBankAcquisitionBudget.rowStage,
    SemiprimeSourceCountPowers.budget,SemiprimeSourceCountPowers.stepBudget,SemiprimeSourceCountPowers.width,
    SemiprimeSourceClassifiedWeights.budget,SemiprimeSourceClassifiedWeights.inputWidth,
    SemiprimeSourceScoreWeightBits.weightWidth,SemiprimeSourceScoreWeightBits.weightBudget,
    SemiprimeSourceScoreWeightBits.combineBudget,SemiprimeSourceClassifiedCountsClock.operandWidth,
    SemiprimeSourceClassifiedCountsClock.laneWidth,SemiprimeSourceClassifiedCountsClock.scoreBudget,
    SemiprimeSourceClassifiedCountsClock.sequentialBudget,SemiprimeSourceClassifiedCountsClock.evaluateBudget,
    SemiprimeSourceClassifiedCountsClock.localBudget,SemiprimeSourceHeadCountBitsBounds.budget,
    SemiprimeSourceIncidenceCountBitsBounds.countBudget,SemiprimeSourceIncidenceCountBitsBounds.edgeBudget,
    SemiprimeSourceWordIdPredicateBounds.terminalBudget,SemiprimeSourceWordIdPredicateBounds.programBudget,
    SemiprimeSourceWordIdPredicateBounds.terminalStepBudget,SemiprimeSourceWordIdPredicateBounds.bankReadBudget,
    SemiprimeSourceWordIdPredicateBounds.colourReadBudget,SemiprimeSourceWordIdEnvironmentBounds.readBudget,
    SemiprimeSourceWordIdEnvironmentBounds.keyBudget,SemiprimeSourceWordIdEnvironmentBounds.idCopyBudget,
    SemiprimeSourceWordIdEnvironmentBounds.scanStep,SemiprimeSourceWordIdEnvironmentBounds.eqBudget,
    SemiprimeSourceScorePredicateBitsBounds.copyBudget,SemiprimeSourceScorePredicateBitsBounds.equalityBudget]
  gcongr

/-- Diagonal bound of the ACTUAL displayed original-input caller budget. -/
def envelope (S : ℕ) : ℕ :=
  SemiprimeSourceClassifiedSearchBudget.indexedBudget S S S S S S S S S

/-- Controller majorant replaces only the sole truncated tail length by its full length. -/
def controllerMajorant (S : ℕ) : ℕ :=
  2*S+3+S*(S*(2*SemiprimeSourceClassifiedCountsClock.scoreBudget S S S S S
    (SemiprimeSourceClassifiedSearchBudget.weightCap S S S S S)+
    200*(SemiprimeSourceClassifiedSearchBudget.wordCap S S S S S S+1)^2+4*(2*S)+5)+
    4*(2*S)+2+S*(4*(2*S)+4)+4)+S*(4*(2*S)+4)+1

/-- Subtraction-free diagonal with exactly the same acquired bank/weight/callback costs. -/
def diagonalMajorant (S : ℕ) : ℕ :=
  SemiprimeSourceWordIdMetadata.budget S S S S+S*(8*S+15)+1+
    (SemiprimeSourceWordBankAcquisitionBudget.budget S S S+
      SemiprimeSourceCountPowers.budget S S+
      SemiprimeSourceClassifiedWeights.budget S S S S S+
      controllerMajorant S+S+7)+3

/-- Replacing S-1 by S never discards any actual work. -/
theorem envelope_le_majorant (S : ℕ) : envelope S≤diagonalMajorant S := by
  unfold envelope diagonalMajorant controllerMajorant
    SemiprimeSourceClassifiedSearchBudget.indexedBudget SemiprimeSourceClassifiedSearchBudget.runBudget
    SemiprimeSourceClassifiedSearchBudget.controlBudget
  gcongr
  omega

/-- A fixed monomial bounds the full actual-family resource envelope. -/
theorem envelope_monomial : ∃ C k : ℕ,∀ S,envelope S≤C*(S+1)^k := by
  have hp : Bound diagonalMajorant := by
    change Bound (fun S => diagonalMajorant S)
    simp only [diagonalMajorant,controllerMajorant,SemiprimeSourceClassifiedSearchBudget.wordCap,SemiprimeSourceClassifiedSearchBudget.weightCap,
    SemiprimeSourceWordIdMetadata.budget,SemiprimePaidFiniteEnumerations.incidenceBudget,
    SemiprimePaidFiniteEnumerations.scoreBudget,SemiprimeSourceWordBankAcquisitionBudget.budget,
    SemiprimeSourceWordBankAcquisitionBudget.colourBudget,SemiprimeSourceWordBankAcquisitionBudget.rowStage,
    SemiprimeSourceCountPowers.budget,SemiprimeSourceCountPowers.stepBudget,SemiprimeSourceCountPowers.width,
    SemiprimeSourceClassifiedWeights.budget,SemiprimeSourceClassifiedWeights.inputWidth,
    SemiprimeSourceScoreWeightBits.weightWidth,SemiprimeSourceScoreWeightBits.weightBudget,
    SemiprimeSourceScoreWeightBits.combineBudget,SemiprimeSourceClassifiedCountsClock.operandWidth,
    SemiprimeSourceClassifiedCountsClock.laneWidth,SemiprimeSourceClassifiedCountsClock.scoreBudget,
    SemiprimeSourceClassifiedCountsClock.sequentialBudget,SemiprimeSourceClassifiedCountsClock.evaluateBudget,
    SemiprimeSourceClassifiedCountsClock.localBudget,SemiprimeSourceHeadCountBitsBounds.budget,
    SemiprimeSourceIncidenceCountBitsBounds.countBudget,SemiprimeSourceIncidenceCountBitsBounds.edgeBudget,
    SemiprimeSourceWordIdPredicateBounds.terminalBudget,SemiprimeSourceWordIdPredicateBounds.programBudget,
    SemiprimeSourceWordIdPredicateBounds.terminalStepBudget,SemiprimeSourceWordIdPredicateBounds.bankReadBudget,
    SemiprimeSourceWordIdPredicateBounds.colourReadBudget,SemiprimeSourceWordIdEnvironmentBounds.readBudget,
    SemiprimeSourceWordIdEnvironmentBounds.keyBudget,SemiprimeSourceWordIdEnvironmentBounds.idCopyBudget,
    SemiprimeSourceWordIdEnvironmentBounds.scanStep,SemiprimeSourceWordIdEnvironmentBounds.eqBudget,
    SemiprimeSourceScorePredicateBitsBounds.copyBudget,SemiprimeSourceScorePredicateBitsBounds.equalityBudget]
    boundArithmetic
  obtain ⟨C,k,h⟩ := hp
  exact ⟨C,k,fun S => (envelope_le_majorant S).trans (h S)⟩

/-- The actual original indexed caller is uniformly bounded using only original
network/alphabet/descriptor dimensions, without a report/word/output oracle. -/
theorem indexed_report_actual (n F r Q lam : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (S : ℕ)
    (hn : n≤S) (hF : F≤S) (hr : r≤S) (hQ : Q≤S) (hlam : lam≤S)
    (hM : (∑ e,arity e)≤S) (hL : r^Q≤S)
    (hT : (∑ e,arity e)^2+Q*n^2≤S) (hN : n+F≤S) :
    (SemiprimeSourceClassifiedCaller.indexed n F r Q lam arity owner).work≤envelope S := by
  exact (SemiprimeSourceClassifiedSearchBudget.indexed_work n F r Q lam arity owner).trans
    (indexedBudget_mono hn hF hr hQ hlam hM hL hT hN)

end RiemannGaussian.SemiprimeSourceClassifiedResources
