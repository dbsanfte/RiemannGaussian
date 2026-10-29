/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsSpec
import RiemannGaussian.SemiprimeD1RecoveryNodeBitsCorrectness
/-! # Exact six acquired original input-word boundaries for the local-weight source
These are proof specifications of words produced by the separate actual upstream
Grid/affine/inverse/powers callers. They are not runtime coefficient suppliers.
Original dimension/width bounds discharge every semantic fit internally.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsLegacy
open SemiprimeRationalBits
open SemiprimeD1StackRecoveryWeightsSpec
/-- Original actually acquired multiplicity, retained as unary metadata by its physical caller. -/
def retained (a M u:Nat) (t:Fin (2^(a+1))):Nat:=
  SemiprimeD1JetRecoveryGrid.nodeMultiplicity a (SemiprimeD1TaperedLoss.height M u) u t.val
/-- Exact original acquired Grid cache, never a rational value supplied to the source. -/
def grid (width:List Bool) (a M u:Nat) (t:Fin (2^(a+1))):SemiprimeD1RecoveryGridBits.Report:=
  SemiprimeD1RecoveryGridBits.acquire width a M u t
/-- Exact upstream inverse array WORDS from the acquired affine denominator. -/
def inverse (width:List Bool) (a M u:Nat) (t:Fin (2^(a+1))):List RationalWord:=
  let den:=SemiprimeAffineJetBits.build width (retained a M u t) (grid width a M u t).grid.slopes
  (SemiprimeNormalizedInverseBits.build width den.words (retained a M u t)).words.toList
/-- Exact upstream cached-power WORDS, with literalONE seed and actual normalized successor bytes. -/
def powers (width:List Bool) (a M u:Nat) (t:Fin (2^(a+1))):List RationalWord:=
  SemiprimeD1StackRecoveryPowersSpec.array width (grid width a M u t).argument (retained a M u t)
/-- Entire prepared local-weight array equals the authoritative original acquireAt bytes, with no value-only shortcut. -/
theorem array_acquireAt (width:List Bool) (a M u:Nat) (t:Fin (2^(a+1))):
    array width (retained a M u t) (grid width a M u t).scalar (inverse width a M u t) (powers width a M u t)=
      (SemiprimeD1RecoveryNodeBits.acquireAt width a M u t).words:=by
  rw [array_original]
  unfold powers
  rw [SemiprimeD1StackRecoveryPowersSpec.array_native]
  have h:=SemiprimeD1RecoveryNodeBitsCorrectness.acquireAt_words width a M u t
  dsimp only at h
  rw [SemiprimeSourceMemoryBits.copyMemory_words] at h
  exact h.symm
/-- ALL original-family canonical numerator/denominator fields, values, Valid and fitted widths follow from original dimensions only. -/
theorem array_values (width:List Bool) (a M u:Nat) (t:Fin (2^(a+1))) (hu:u ≤ M)
    (hW:SemiprimeD1RecoveryNodeBits.width a M ≤ width.length):
    let words:=array width (retained a M u t) (grid width a M u t).scalar (inverse width a M u t) (powers width a M u t)
    let expected:=(SemiprimeD1JetRecoveryWeights.acquire a (SemiprimeD1TaperedLoss.height M u) u t.val).weights.toList
    words.map RationalWord.value=expected ∧ (∀x∈words,x.Valid) ∧ (∀x∈words,Width x width.length) ∧
      words.map (fun x=>(x.numerator.value,SemiprimeBitArithmetic.bitValue x.denominator))=
        expected.map (fun x=>(x.num,x.den)):=by
  dsimp only
  rw [array_acquireAt]
  exact SemiprimeD1RecoveryNodeBitsCorrectness.acquireAt_correct width a M u t hu hW
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsLegacy
