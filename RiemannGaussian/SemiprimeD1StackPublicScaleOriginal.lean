/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicScaleExecution
/-! # Exact original scale verdict on the actual physical output cells -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicScaleOriginal
open SemiprimeD1StackPublicScale SemiprimeD1StackPublicScaleState SemiprimeD1StackPublicScaleDot
open SemiprimeD1StackPublicScaleTail SemiprimeD1StackPublicScaleInputs SemiprimeD1StackPublicScaleExecution
open SemiprimeBitArithmetic
/-- The real read leaves the evaluated result untouched until numeric comparison. -/
theorem read_left (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ) :
    readData bits raw stride frequency inverse j k (equalStack .left)=
      evaluated bits raw stride frequency inverse j k (dotStack I.output) := by
  simp only [readData,Function.update_of_ne (by decide : equalStack .left≠blockStack 4),
    Function.update_of_ne (by decide : equalStack .left≠blockStack 0),branched,
    Function.update_of_ne (by decide : equalStack .left≠dotStack I.status)]
  rfl
/-- Actual unread raw output-word bytes are extracted with actual acquired width. -/
theorem read_right (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ) :
    readData bits raw stride frequency inverse j k (equalStack .right)=outputWord bits raw := by
  change readData bits raw stride frequency inverse j k (blockStack 4)=_
  rw [readData,Function.update_same,branch_modulus]
  have he : branched bits raw stride frequency inverse j k (blockStack 0)=raw.drop (cached bits).length := by
    change Function.update (evaluated bits raw stride frequency inverse j k) (dotStack I.status) [] (dotStack I.suffixRole)=_
    rw [Function.update_of_ne (by decide : dotStack I.suffixRole≠dotStack I.status),suffix_value]
  rw [he]
  rfl
/-- Literal actual final output is the guarded computed dot/numeric equality,
including false status and every noncanonical original output word. -/
theorem verdict_value (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ) :
    (done bits raw stride frequency inverse j k).data (auxRole .output)=
      [SemiprimeD1StackPublicScaleMeaning.answer (cached bits) (expression bits inverse) j k
        (inputWord bits raw) (outputWord bits raw)] := by
  change finalData bits raw stride frequency inverse j k (equalStack .output)=_
  cases he : flag bits raw with
  | false=>
    rw [finalData,he]
    change [false]=_
    simp only [SemiprimeD1StackPublicScaleMeaning.answer,show
      SemiprimeD1StackPublicScaleMeaning.guard (cached bits) (inputWord bits raw)=false from he,Bool.false_and]
  | true=>
    rw [finalData,he]
    change [equalAnswer bits raw stride frequency inverse j k]=_
    dsimp only [equalAnswer]
    rw [read_left,read_right,result_value]
    have hg : SemiprimeD1StackPublicScaleMeaning.guard (cached bits) (inputWord bits raw)=true := he
    rw [hg]
    simp only [ite_true,SemiprimeD1StackPublicScaleMeaning.answer,hg,Bool.true_and]
/-- Actual complete scale output equals the ORIGINAL guarded scale equation.
The modulus/source/operand vector/canonicality/result are all acquired, with no
such answer or solved guard premise at this endpoint. -/
theorem original_equation (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    (done bits raw stride frequency inverse j k).data (auxRole .output)=
      [(SemiprimeMacroEntryBitCheck.equationRun (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN)
        (fun _ : Fin 1=>inputWord bits raw) (outputWord bits raw)
        (.mul (.literal (inputWord bits raw)) (SemiprimeMacroEntryBitPrimitives.powerExpr
          (SemiprimeMacroEntryBitCheck.rootExpr (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN)
            (transform inverse)) (j*k)))).accepted] := by
  rw [verdict_value]
  rw [original_modulus bits hc hN,expression_original bits hc hN inverse,SemiprimeD1StackPublicScaleMeaning.old_scale]
end RiemannGaussian.SemiprimeD1StackPublicScaleOriginal
