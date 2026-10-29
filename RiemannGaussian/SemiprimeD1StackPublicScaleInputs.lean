/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicScaleState
import RiemannGaussian.SemiprimeD1StackPublicScaleMeaning
import RiemannGaussian.SemiprimeD1StackRootSourceOriginal
/-! # Derived original scale source and input-vector interfaces -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicScaleInputs
open SemiprimeD1StackPublicScale SemiprimeD1StackPublicScaleState
open SemiprimeMacroEntryBitPrimitives SemiprimeBitArithmetic SemiprimeMacroParameters
/-- Equal-width literal Boolean representations are determined by integer value. -/
theorem words_eq {xs ys : List Bool} (hl : xs.length=ys.length) (hv : bitValue xs=bitValue ys) : xs=ys := by
  induction xs generalizing ys with
  | nil=>cases ys <;> simp_all
  | cons b xs ih=>
    cases ys with
    | nil=>simp at hl
    | cons c ys=>
      have ht : xs.length=ys.length := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hl
      cases b <;> cases c <;> simp only [bitValue,bitNat,Bool.false_eq_true,ite_false,ite_true] at hv
      · exact congrArg (List.cons false) (ih ht (by omega))
      · omega
      · omega
      · exact congrArg (List.cons true) (ih ht (by omega))
/-- Physical selector representation of the original transform direction.
Both forward sides use the same literal root as the original checker. -/
def transform (inverse : Bool) : SemiprimeMacroGraph.Transform := if inverse then .inr () else .inl 0
/-- Computable expression specification of the actually acquired root code. -/
def expression (bits : List Bool) (inverse : Bool) : Expr :=
  if inverse then powerExpr SemiprimeMacroEntryBitCheck.fourExpr (transformLength bits.length-1)
  else SemiprimeMacroEntryBitCheck.fourExpr
/-- Actual source bytes agree with their computable original expression for ALL
binary inputs; no prepared AST/source is an executing argument. -/
theorem source_code (bits : List Bool) (inverse : Bool) :
    baseCode bits inverse=SemiprimeD1StackExprCodec.encode (expression bits inverse) [] := by
  cases inverse
  · rfl
  · change SemiprimeD1StackExprPowerSpec.result _
      (SemiprimeD1StackExprCodec.encode SemiprimeMacroEntryBitCheck.fourExpr []) []=_
    rw [SemiprimeD1StackExprPowerSpec.result_original]
    have hp:=(SemiprimeD1StackRootSourceOriginal.marker_lengths bits).1
    change (SemiprimeD1StackRootSourceExecution.rootMarkers
      (SemiprimeD1BinaryPublicAcquisitionComponents.result bits)).length=transformLength bits.length-1 at hp
    rw [hp]
    rfl
/-- Original geometry identifies the acquired expression with the exact old root. -/
theorem expression_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (inverse : Bool) :
    expression bits inverse=SemiprimeMacroEntryBitCheck.rootExpr
      (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN) (transform inverse) := by
  have hp:=(SemiprimeD1StackRootSourceOriginal.original_parameters bits hc hN).1
  cases inverse
  · rfl
  · simp only [expression,transform,ite_true,SemiprimeMacroEntryBitCheck.rootExpr,hp]
/-- Actual root-source bytes are exactly the ORIGINAL selected expression bytes. -/
theorem original_code (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (inverse : Bool) :
    baseCode bits inverse=SemiprimeD1StackExprCodec.encode
      (SemiprimeMacroEntryBitCheck.rootExpr (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN) (transform inverse)) [] := by
  cases inverse
  · exact SemiprimeD1StackRootSourceOriginal.forward_root bits hN 0
  · exact SemiprimeD1StackRootSourceOriginal.inverse_root bits hc hN
/-- Acquired original M has EXACT old physical modulus bytes, not just a supplied
ring interpretation. The equality follows from actual width and value proofs. -/
theorem original_modulus (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    cached bits=SemiprimeMacroEntryBitCheck.modulus (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN) := by
  let p:=SemiprimePublicFactorCount.publicConfig (bitValue bits) hN
  have hp:=(SemiprimeD1StackRootSourceOriginal.original_parameters bits hc hN).1
  apply words_eq
  · change (SemiprimeD1StackRootSourceOriginal.actualCache bits R.modulusKey).length=_
    rw [SemiprimeD1StackRootSourceOriginal.modulus_length,SemiprimeMacroEntryBitCheck.modulus_length,hp]
  · change bitValue (SemiprimeD1StackFermatWords.modulusWord (transformLength bits.length))=_
    rw [SemiprimeD1StackFermatWords.modulus_value _ (by unfold transformLength;positivity),
      SemiprimeMacroEntryBitCheck.modulus_value,hp,(SemiprimePublicFactorCount.publicConfig _ hN).shape]
/-- Original positivity and base validity are derived from the ACTUAL original
acquisition. They are not canonicality, modulus or whole-source advice inputs. -/
theorem original_valid (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) (inverse : Bool) :
    1<bitValue (cached bits) ∧ Valid (cached bits)
      (SemiprimeMacroEntryBitCheck.rootExpr (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN) (transform inverse)) := by
  rw [original_modulus bits hc hN]
  exact ⟨by have h:=SemiprimeMacroEntryBitCheck.modulus_gt_four (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN);omega,
    SemiprimeMacroEntryBitCheck.rootExpr_valid _ _⟩
/-- Fitting a complete front returns exactly those original literal bytes. -/
theorem block_prefix (cached front raw : List Bool) (hl : front.length=cached.length) :
    SemiprimeD1StackWordBlockExecution.result (front++raw) cached=front := by
  induction cached generalizing front with
  | nil=>cases front <;> simp_all [SemiprimeD1StackWordBlockExecution.result,SemiprimeBitDivision.fitBits]
  | cons b cached ih=>
    cases front with
    | nil=>simp at hl
    | cons c front=>
      rw [List.cons_append,SemiprimeD1StackWordBlockExecution.fit_cons]
      simp only [List.head?_cons,Option.getD_some,List.tail_cons]
      rw [ih front (by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hl)]
/-- The ACTUALLY ACQUIRED two-word vector is literal zero/input in that order;
missing source cells remain physically false-padded, not ignored. -/
theorem acquired_words (bits raw : List Bool) :
    SemiprimeD1StackInputDotExecution.words (paddedRaw bits raw)
      ⟨[],[],[],[true,true]⟩ (cached bits)=
      [SemiprimeD1StackPublicScaleMeaning.zeroWord (cached bits),SemiprimeD1StackWordBlockExecution.result raw (cached bits)] := by
  have h0:=block_prefix (cached bits) (List.replicate (cached bits).length false) raw (by simp)
  have hd : (paddedRaw bits raw).drop (cached bits).length=raw := by
    simp [paddedRaw]
  change [SemiprimeD1StackWordBlockExecution.result (paddedRaw bits raw) (cached bits),
    SemiprimeD1StackWordBlockExecution.result ((paddedRaw bits raw).drop (cached bits).length) (cached bits)]=_
  change SemiprimeD1StackWordBlockExecution.result (paddedRaw bits raw) (cached bits)=
    SemiprimeD1StackPublicScaleMeaning.zeroWord (cached bits) at h0
  rw [h0,hd]
end RiemannGaussian.SemiprimeD1StackPublicScaleInputs
