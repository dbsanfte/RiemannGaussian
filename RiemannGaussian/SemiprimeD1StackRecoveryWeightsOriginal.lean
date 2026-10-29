/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsExecution
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsLegacy
/-! # Complete original local-weight bytes and dimension-derived validity at the SAME actual source
The six upstream acquired inputs remain an explicit prepared boundary. Their
physical Grid/affine/inverse/power caller is separate; no N-only claim is made.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsOriginal
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsExecution
open SemiprimeD1StackRecoveryWeightsLegacy SemiprimeD1StackRecoveryWeightsIndices
/-- All six actual input words are retained literally in the complete stopped bank. -/
theorem retained_inputs (inverse powers:List SemiprimeRationalBits.RationalWord) (scalar:SemiprimeRationalBits.RationalWord) (q:Nat) (width:List Bool):
    result inverse powers scalar q width (aux .denominator)=SemiprimeD1StackNormalizedInverse.tape inverse ∧
    result inverse powers scalar q width (aux .prefixReverse)=SemiprimeD1StackNormalizedInverse.tape powers ∧
    result inverse powers scalar q width (SemiprimeD1StackRecoveryWeights.scalar .signed)=SemiprimeD1StackNormalizedInverse.signed scalar ∧
    result inverse powers scalar q width (SemiprimeD1StackRecoveryWeights.scalar .den)=scalar.denominator ∧
    result inverse powers scalar q width (aux .originalQ)=unary q ∧ result inverse powers scalar q width template=width:=⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
/-- Every actual private/helper/shadow field is empty, with immutable powers explicitly retained. -/
theorem work_clear (inverse powers:List SemiprimeRationalBits.RationalWord) (scalar:SemiprimeRationalBits.RationalWord) (q:Nat) (width:List Bool)
    (k:I.Stack) (hk:¬SemiprimeD1StackRecoveryWeightsInventory.kept k):result inverse powers scalar q width (helper k)=[]:=
  SemiprimeD1StackRecoveryWeightsFinishView.empty_private inverse powers scalar q width _ k hk
/-- Honest six actual original input words, with every other54 physical role EMPTY. -/
def originalInput (width:List Bool) (a M u:Nat) (t:Fin (2^(a+1))):C.State Stack Label:=
  initial (SemiprimeD1StackNormalizedInverse.tape (inverse width a M u t))
    (SemiprimeD1StackNormalizedInverse.tape (powers width a M u t))
    (SemiprimeD1StackNormalizedInverse.signed (grid width a M u t).scalar) (grid width a M u t).scalar.denominator
    (unary (retained a M u t)) width
/-- Exact stopped ordered array bytes, retaining ALL actual inverse/power/scalar/q/W source words. -/
theorem output_original (width:List Bool) (a M u:Nat) (t:Fin (2^(a+1))):
    result (inverse width a M u t) (powers width a M u t) (grid width a M u t).scalar (retained a M u t) width (aux .output)=
      SemiprimeD1StackNormalizedInverse.tape (SemiprimeD1RecoveryNodeBits.acquireAt width a M u t).words:=by
  change SemiprimeD1StackNormalizedInverse.tape (SemiprimeD1StackRecoveryWeightsSpec.array width
    (retained a M u t) (grid width a M u t).scalar (inverse width a M u t) (powers width a M u t))=_
  rw [array_acquireAt]
/-- The whole actual prepared source internally acquires exact old weights, not merely an endpoint value equation. -/
theorem source_run_original (width:List Bool) (a M u:Nat) (t:Fin (2^(a+1))):
    ∃time ≤ timeBound (inverse width a M u t) (powers width a M u t) (grid width a M u t).scalar (retained a M u t) width,
      SemiprimeD1StackCalls.run program time (originalInput width a M u t)=some
        (done (inverse width a M u t) (powers width a M u t) (grid width a M u t).scalar (retained a M u t) width):=
  source_run _ _ _ _ _
/-- Original dimensions alone discharge all semantic Valid/Fits/canonical rational obligations, for every local coefficient. -/
theorem original_values (width:List Bool) (a M u:Nat) (t:Fin (2^(a+1))) (hu:u ≤ M)
    (hW:SemiprimeD1RecoveryNodeBits.width a M ≤ width.length):
    let words:=SemiprimeD1StackRecoveryWeightsSpec.array width (retained a M u t) (grid width a M u t).scalar
      (inverse width a M u t) (powers width a M u t)
    let expected:=(SemiprimeD1JetRecoveryWeights.acquire a (SemiprimeD1TaperedLoss.height M u) u t.val).weights.toList
    words.map SemiprimeRationalBits.RationalWord.value=expected ∧ (∀x∈words,x.Valid) ∧
      (∀x∈words,SemiprimeRationalBits.Width x width.length) ∧
      words.map (fun x=>(x.numerator.value,SemiprimeBitArithmetic.bitValue x.denominator))=expected.map (fun x=>(x.num,x.den)):=
  array_values width a M u t hu hW
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsOriginal
