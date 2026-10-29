/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceScorePhysicalBudget

/-! # Uniform original-family polynomial for physical integer-count selection
All dimensions and the actual original alphabet/universal bank are substituted.
The theorem bounds the actual retained circuit and native-metadata ledger;
complete original-input primitive-machine refinement remains separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
namespace RiemannGaussian.SemiprimeSourceScorePhysicalResources
open SemiprimeSourceScorePhysicalBudget SemiprimeSourceScoreCountBitsBounds
open SemiprimeReportPolynomialGrowth

/-- Coarse fixed-polynomial original-resource envelope, including all cached setup. -/
def envelope (S : ℕ) : ℕ :=
  S*(8*S+15)+1+SemiprimeSourceScoreWeightAcquisition.acquisitionBudget S S S S S S+
    (S*(S*(2*scoreBudget S S S S S (weightCap S S S S)+
      200*(wordCap S S S S S S+1)^2+3)+4)+1)+3

/-- The complete displayed original-source search budget is monotone into
the single resource parameter; no execution field is used as an assumed cap. -/
theorem computedBudget_le (M n r Q lam U L T N S : ℕ)
    (hM : M ≤ S) (hn : n ≤ S) (hr : r ≤ S) (hQ : Q ≤ S) (hlam : lam ≤ S)
    (hU : U ≤ S) (hL : L ≤ S) (hT : T ≤ S) (hN : N ≤ S) :
    computedBudget M n r Q lam U L T N ≤ envelope S := by
  have hK : weightCap M n lam U ≤ weightCap S S S S := by
    unfold weightCap SemiprimeSourceScoreWeightBits.weightWidth SemiprimeSourceScoreWeightAcquisition.inputWidth
    gcongr
  have hF := scoreBudget_mono hr hQ hN hL hT hK
  have hW : wordCap L T M n lam U ≤ wordCap S S S S S S := by
    unfold wordCap scoreOperandWidth localWidth
    gcongr
  have hA := SemiprimeSourceScoreWeightAcquisition.acquisitionBudget_mono hM hn hr hQ hlam hU
  have hLm : L-1 ≤ S := (Nat.sub_le L 1).trans hL
  have hD := Nat.mul_le_mul hT (Nat.add_le_add_right (Nat.mul_le_mul_left 8 hN) 15)
  unfold computedBudget runBudget envelope
  have hcontrol := Nat.mul_le_mul hN
    (Nat.add_le_add_right
      (Nat.mul_le_mul hLm (Nat.add_le_add_right
        (Nat.add_le_add (Nat.mul_le_mul_left 2 hF)
          (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left (Nat.add_le_add_right hW 1) 2))) 3)) 4)
  omega

/-- ACTUAL original caller costs are uniformly polynomial in original finite resources. -/
theorem caller_work {I E : Type} [DecidableEq E] {n r Q : ℕ} [NeZero r]
    (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (lam S : ℕ)
    (hM : en.incidences.values.length ≤ S) (hn : n ≤ S) (hr : r ≤ S)
    (hQ : Q ≤ S) (hlam : lam ≤ S) (hU : en.types.values.length ≤ S)
    (hL : (en.wordFirst::en.wordTail).length ≤ S)
    (hT : en.terms.values.length ≤ S) (hN : en.indices.values.length ≤ S) :
    (SemiprimeSourceScorePhysicalCaller.computed owner factor en lam).work ≤ envelope S :=
  (computed_work owner factor en lam).trans
    (computedBudget_le _ _ _ _ _ _ _ _ _ S hM hn hr hQ hlam hU hL hT hN)

/-- A fixed coefficient and exponent bound every original-family retained report. -/
theorem envelope_monomial : ∃ C k : ℕ,∀ S,envelope S ≤ C*(S+1)^k := by
  change Bound (fun S => envelope S)
  simp only [envelope,SemiprimeSourceScoreWeightAcquisition.acquisitionBudget,
    weightCap,wordCap,scoreOperandWidth,scoreBudget,sequentialBudget,evaluateBudget,
    localBudget,paddingBudget,localWidth,SemiprimeSourceScoreCountBitsBudget.countBudget,
    SemiprimeSourceScorePredicateBitsBounds.terminalBudget,
    SemiprimeSourceScorePredicateBitsBounds.acquisitionBudget,
    SemiprimeSourceScorePredicateBitsBounds.terminalStepBudget,
    SemiprimeSourceScorePredicateBitsBounds.workingWidth,
    SemiprimeSourceScorePredicateBitsBounds.wordBudget,
    SemiprimeSourceScorePredicateBitsBounds.idBudget,
    SemiprimeSourceScorePredicateBitsBounds.readBudget,
    SemiprimeSourceScorePredicateBitsBounds.rowEqualityBudget,
    SemiprimeSourceScorePredicateBitsBounds.coordinateBudget,
    SemiprimeSourceScorePredicateBitsBounds.equalityBudget,
    SemiprimeSourceScorePredicateBitsBounds.copyBudget,
    SemiprimeSourceScorePredicateBitsBounds.scanStep,
    SemiprimeSourceScoreWeightBits.weightWidth,
    SemiprimeSourceScoreWeightBits.weightBudget,
    SemiprimeSourceScoreWeightBits.combineBudget,
    SemiprimeSourceScoreWeightAcquisition.inputWidth]
  boundArithmetic

end RiemannGaussian.SemiprimeSourceScorePhysicalResources
