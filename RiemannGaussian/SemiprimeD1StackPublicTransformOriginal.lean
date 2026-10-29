/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformArrays
/-! # Exact original transform equations from actual acquired vectors -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformOriginal
open SemiprimeD1StackPublicTransformMetadata SemiprimeD1StackPublicTransformWords
open SemiprimeD1StackPublicTransformGuards SemiprimeD1StackPublicTransformQuery
open SemiprimeD1StackPublicTransformRead SemiprimeD1StackPublicTransformMeaning
open SemiprimeD1StackPublicTransformArrays SemiprimeMacroEntryBitPrimitives SemiprimeMacroEntryBitCheck SemiprimeBitArithmetic
/-- Original finite input view of the actual acquired vector. -/
def input (bits raw : List Bool) (second : Bool) (j : Fin (size bits second)) : List Bool :=
  SemiprimeD1StackExprDotSpec.wordAt (inputs (rootData bits) raw second) j.val
/-- Original finite output view of the actual acquired vector. -/
def output (bits raw : List Bool) (second : Bool) (j : Fin (size bits second)) : List Bool :=
  outputWord bits raw second j.val
/-- Exact original normalization source, used only in this semantic comparison. -/
noncomputable def factor (bits : List Bool) (hN : 0<bitValue bits) (second inverse : Bool) : Expr :=
  if second then normalizationExpr (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN) (transform inverse) else oneExpr
/-- Original source alignment is a literal expression equality over the actual
ordered word family. No compiled AST or word-list answer is supplied. -/
theorem dot_original (bits raw : List Bool) (second inverse : Bool) (k : ℕ)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    dotExpression bits raw second inverse k=dotExpr
      (rootExpr (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN) (transform inverse))
      (size bits (!second)) k (wordAt (input bits raw second)) (size bits second) := by
  change dotExpr (expression bits inverse) _ _ _ _=_
  have he:=SemiprimeD1StackPublicScaleInputs.expression_original bits hc hN inverse
  change expression bits inverse=_ at he
  rw [he]
  exact dot_finite _ _ _ _ (inputs_length bits raw second)
/-- The actual normalized integer comparison equals the original residue
check at each original output coordinate, after the actual frontend guards. -/
theorem query_original (bits raw : List Bool) (second inverse : Bool)
    (k : Fin (size bits second)) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (hi : inputFlag (rootData bits) raw second=true)
    (ho : outputFlag (rootData bits) raw second=true) :
    queryAnswer bits raw second inverse k.val=
      (residueEqualityBits (modulus (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN))
        (.literal (output bits raw second k))
        (.mul (factor bits hN second inverse) (dotExpression bits raw second inverse k.val))).accepted := by
  let p:=SemiprimePublicFactorCount.publicConfig (bitValue bits) hN
  have hm : 0<bitValue (cached bits) := by have h:=(original_valid bits hc hN inverse).1;omega
  have hv:=SemiprimeD1StackGuardedDotExecution.defaulted_canonical (cached bits)
    (outputs (rootData bits) raw second) hm ho k.val
  have hd:=dot_valid bits raw second inverse k.val hc hN hi
  have hf : Valid (cached bits) (factor bits hN second inverse) := by
    rw [original_modulus bits hc hN]
    cases second
    · change 1<bitValue (modulus p)
      have h:=modulus_gt_four p;omega
    · exact normalizationExpr_valid p (transform inverse)
  apply Bool.eq_iff_iff.mpr
  rw [query_true bits raw second inverse k.val hc hN hi ho]
  rw [←original_modulus bits hc hN]
  have hl : Valid (cached bits) (.literal (output bits raw second k)) := hv
  have hp : Valid (cached bits) (.mul (factor bits hN second inverse) (dotExpression bits raw second inverse k.val)) := ⟨hf,hd⟩
  rw [residueEqualityBits_correct _ hm _ _ hl hp]
  change meaning (cached bits) (factor bits hN second inverse)*meaning (cached bits) (dotExpression bits raw second inverse k.val)=_ ↔
    _=meaning (cached bits) (factor bits hN second inverse)*meaning (cached bits) (dotExpression bits raw second inverse k.val)
  exact eq_comm
/-- Verdict specification of the closed physical frontend and descending loop. -/
def verdict (bits raw : List Bool) (second inverse : Bool) : Bool :=
  SemiprimeD1StackPublicTransformExecution.acceptedInputs bits raw second &&
    SemiprimeD1StackPublicTransformLoop.answer bits raw second inverse (size bits second)
/-- Exact old transform checker on the ACTUALLY acquired finite word families.
This is semantics only: no old report or clock is transferred. -/
theorem transform_original (bits raw : List Bool) (second inverse : Bool)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    verdict bits raw second inverse=
      (transformRun (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN) (transform inverse)
        (size bits (!second)) (factor bits hN second inverse) (input bits raw second) (output bits raw second)).accepted := by
  have hi : inputFlag (rootData bits) raw second=true ↔
      ∀j : Fin (size bits second),bitValue (input bits raw second j)<bitValue (cached bits) :=
    guard_finite _ _ (inputs_length bits raw second)
  have ho : outputFlag (rootData bits) raw second=true ↔
      ∀j : Fin (size bits second),bitValue (output bits raw second j)<bitValue (cached bits) :=
    guard_finite _ _ (outputs_length bits raw second)
  apply Bool.eq_iff_iff.mpr
  simp only [verdict,SemiprimeD1StackPublicTransformExecution.acceptedInputs,Bool.and_eq_true,
    loop_answer_true,transformRun,guardRun_correct,andRun,canonicalRun_correct,allRun_correct]
  rw [←original_modulus bits hc hN]
  constructor
  · rintro ⟨⟨hig,hog⟩,hq⟩
    refine ⟨⟨hi.mp hig,ho.mp hog⟩,?_⟩
    intro k
    have he:=query_original bits raw second inverse k hc hN hig hog
    rw [dot_original bits raw second inverse k.val hc hN,←original_modulus bits hc hN] at he
    rw [←he]
    exact hq k.val k.isLt
  · rintro ⟨⟨hig,hog⟩,hq⟩
    have hig':=hi.mpr hig
    have hog':=ho.mpr hog
    refine ⟨⟨hig',hog'⟩,?_⟩
    intro k hk
    have he:=query_original bits raw second inverse ⟨k,hk⟩ hc hN hig' hog'
    rw [dot_original bits raw second inverse k hc hN,←original_modulus bits hc hN] at he
    rw [he]
    exact hq ⟨k,hk⟩
/-- Literal final output stack contains the proved checker verdict. -/
theorem final_output (bits raw : List Bool) (second inverse : Bool) :
    SemiprimeD1StackPublicTransformState.data
      (SemiprimeD1StackPublicTransformExecution.finalParts bits raw second inverse)
      (.aux .output)=[verdict bits raw second inverse] := by
  unfold SemiprimeD1StackPublicTransformExecution.finalParts verdict
  cases h : SemiprimeD1StackPublicTransformExecution.acceptedInputs bits raw second <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,Bool.false_and,Bool.true_and,
      SemiprimeD1StackPublicTransformLoopControl.finished,SemiprimeD1StackPublicTransformState.data_set,
      Function.update_of_ne (by decide : SemiprimeD1StackPublicTransform.Stack.aux .output≠.dot (.inl .frequency)),
      Function.update_of_ne (by decide : SemiprimeD1StackPublicTransform.Stack.aux .output≠.aux .remaining),Function.update_same]
end RiemannGaussian.SemiprimeD1StackPublicTransformOriginal
