/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSetupPolynomialEnvelope
import RiemannGaussian.SemiprimeNativeCounterBudget
import RiemannGaussian.SemiprimePublicBudgetDimensions

/-! # Fixed monomial growth of the actual report envelopes
The witnesses are obtained from the concrete fixed arithmetic expressions,
not from a supplied cost or growth hypothesis. This is a numeric growth result.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeReportPolynomialGrowth

/-- Uniform natural monomial envelope, using a positive argument even at zero. -/
def Bound (f : ℕ → ℕ) : Prop := ∃ C k : ℕ, ∀ S, f S≤C*(S+1)^k

/-- Every fixed constant has a monomial envelope. -/
theorem constant_bound (c : ℕ) : Bound (fun _ => c) := by
  exact ⟨c,0,by intro S; simp⟩

/-- The resource argument has a monomial envelope. -/
theorem identity_bound : Bound (fun S => S) := by
  exact ⟨1,1,by intro S; simp⟩

/-- Sum closure constructs its fixed coefficient and exponent. -/
theorem add_bound {f g : ℕ → ℕ} (hf : Bound f) (hg : Bound g) :
    Bound (fun S => f S+g S) := by
  obtain ⟨C,k,hf⟩ := hf
  obtain ⟨D,l,hg⟩ := hg
  refine ⟨C+D,k+l,?_⟩
  intro S
  have hk := Nat.pow_le_pow_right (by omega : 0<S+1) (Nat.le_add_right k l)
  have hl := Nat.pow_le_pow_right (by omega : 0<S+1) (Nat.le_add_left l k)
  calc
    f S+g S ≤ C*(S+1)^k+D*(S+1)^l := Nat.add_le_add (hf S) (hg S)
    _ ≤ C*(S+1)^(k+l)+D*(S+1)^(k+l) :=
      Nat.add_le_add (Nat.mul_le_mul_left C hk) (Nat.mul_le_mul_left D hl)
    _ = (C+D)*(S+1)^(k+l) := by ring

/-- Product closure constructs its fixed coefficient and exponent. -/
theorem mul_bound {f g : ℕ → ℕ} (hf : Bound f) (hg : Bound g) :
    Bound (fun S => f S*g S) := by
  obtain ⟨C,k,hf⟩ := hf
  obtain ⟨D,l,hg⟩ := hg
  refine ⟨C*D,k+l,?_⟩
  intro S
  calc
    f S*g S ≤ (C*(S+1)^k)*(D*(S+1)^l) := Nat.mul_le_mul (hf S) (hg S)
    _ = C*D*(S+1)^(k+l) := by rw [pow_add]; ring

/-- Fixed natural powers preserve monomial growth. -/
theorem pow_bound {f : ℕ → ℕ} (hf : Bound f) (m : ℕ) :
    Bound (fun S => (f S)^m) := by
  obtain ⟨C,k,hf⟩ := hf
  refine ⟨C^m,k*m,?_⟩
  intro S
  calc
    (f S)^m ≤ (C*(S+1)^k)^m := Nat.pow_le_pow_left (hf S) m
    _ = C^m*(S+1)^(k*m) := by rw [mul_pow,pow_mul]

open Lean Elab Tactic

/-- Syntax-directed closure for a fixed expression of natural arithmetic. -/
syntax "boundArithmetic" : tactic

elab_rules : tactic
  | `(tactic| boundArithmetic) => do
    let target ← Lean.instantiateMVars (← getMainTarget)
    let f := target.getArg! 0
    let f ← Lean.instantiateMVars f
    let body := (Lean.mkApp (f.liftLooseBVars 0 1) (Lean.mkBVar 0)).headBeta
    if !body.hasLooseBVars then
      evalTactic (← `(tactic| exact constant_bound _))
    else if body matches .bvar 0 then
      evalTactic (← `(tactic| exact identity_bound))
    else
      let name := body.getAppFn.constName?
      if name == some ``HAdd.hAdd || name == some ``Nat.add then
        evalTactic (← `(tactic| apply add_bound <;> boundArithmetic))
      else if name == some ``HMul.hMul || name == some ``Nat.mul then
        evalTactic (← `(tactic| apply mul_bound <;> boundArithmetic))
      else if name == some ``HPow.hPow || name == some ``Pow.pow || name == some ``Nat.pow then
        evalTactic (← `(tactic| apply pow_bound <;> boundArithmetic))
      else
        throwError "unsupported arithmetic node: {body}"

/-- Concrete setup and native polynomial envelopes have uniform fixed monomial growth. -/
theorem setup_native_monomial : ∃ C k : ℕ, ∀ S,
    SemiprimeSetupPolynomialEnvelope.polynomialEnvelope S+
      SemiprimeNativeCounterBudget.polynomialEnvelope S ≤ C*(S+1)^k := by
  change Bound (fun S => SemiprimeSetupPolynomialEnvelope.polynomialEnvelope S+
    SemiprimeNativeCounterBudget.polynomialEnvelope S)
  simp only [SemiprimeSetupPolynomialEnvelope.polynomialEnvelope,
    SemiprimeNativeCounterBudget.polynomialEnvelope,SemiprimeNativeCounterBudget.polynomialBudget,
    SemiprimeFullSetupBudget.setupBudget,SemiprimeFullSetupBudget.sourceBudget,
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
  boundArithmetic

/-- The concrete public entry and decoder envelopes have fixed monomial growth too. -/
theorem entry_decoder_monomial : ∃ C k : ℕ, ∀ S,
    SemiprimePublicBudgetDimensions.entryEnvelope S+
      SemiprimePublicBudgetDimensions.decoderEnvelope S ≤ C*(S+1)^k := by
  change Bound (fun S => SemiprimePublicBudgetDimensions.entryEnvelope S+
    SemiprimePublicBudgetDimensions.decoderEnvelope S)
  simp only [SemiprimePublicBudgetDimensions.entryEnvelope,
    SemiprimePublicBudgetDimensions.decoderEnvelope,SemiprimePublicBudgetDimensions.scopeEnvelope]
  boundArithmetic

end RiemannGaussian.SemiprimeReportPolynomialGrowth
