/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransform
/-! # Original acquired axes and canonical normalizer for the closed transform
All functions below are specifications of ACTUAL original-N acquisition fields.
No metadata, normalization value, source AST or canonicality answer is a runtime
argument. The binary normalizer is the already executed Fermat construction.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformMetadata
open SemiprimeD1StackPublicTransform SemiprimeBitArithmetic SemiprimeMacroParameters
open SemiprimeMacroEntryBitPrimitives SemiprimeMacroEntryBitCheck
/-- Actual completed root/source bank, proof view only. -/
def rootData (bits : List Bool) : R.Stack→List Bool := SemiprimeD1StackPublicScaleState.roots bits
/-- Actual acquired original M word, not a supplied modulus. -/
def cached (bits : List Bool) : List Bool := SemiprimeD1StackPublicScaleState.cached bits
/-- Actual acquired original root-code bytes, proof view only. -/
def baseCode (bits : List Bool) (inverse : Bool) : List Bool := SemiprimeD1StackPublicScaleState.baseCode bits inverse
/-- Computable expected expression of the ACTUAL code, never runtime AST control. -/
def expression (bits : List Bool) (inverse : Bool) : Expr := SemiprimeD1StackPublicScaleInputs.expression bits inverse
/-- Actual acquired n marker cells: t at first, r at second. -/
def count (bits : List Bool) (second : Bool) : List Bool := rootData bits (axisRole second)
/-- Actual acquired complementary stride marker cells. -/
def stride (bits : List Bool) (second : Bool) : List Bool := count bits (!second)
/-- Numerical specification of actual acquired marker count; not a runtime field. -/
def size (bits : List Bool) (second : Bool) : ℕ := if second then firstAxis bits.length else secondAxis bits.length
/-- Actual normalization bytes: one literal cell, or the physically acquired
canonical inverse normalizer word, never a numerical/evaluator answer input. -/
def normalizer (bits : List Bool) (second inverse : Bool) : List Bool :=
  if second && inverse then rootData bits (.inl (SemiprimeD1BinaryPublicAcquisition.fermatStack (.inr true))) else [true]
/-- Original transform direction, with shared forward root4. -/
def transform (inverse : Bool) : SemiprimeMacroGraph.Transform := SemiprimeD1StackPublicScaleInputs.transform inverse
/-- The actual n cache contains exactly original physically acquired unary cells. -/
theorem count_unary (bits : List Bool) (second : Bool) : count bits second=SemiprimeD1StackUnaryDivmod.unary (size bits second) := by
  cases second <;> rfl
/-- Complementary stride is acquired exactly as physical unary markers. -/
theorem stride_unary (bits : List Bool) (second : Bool) : stride bits second=SemiprimeD1StackUnaryDivmod.unary (size bits (!second)) :=
  count_unary bits (!second)
/-- The actual cached M is exactly original physical modulus bytes. -/
theorem original_modulus (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    cached bits=modulus (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN) :=
  SemiprimeD1StackPublicScaleInputs.original_modulus bits hc hN
/-- The actual selected source bytes are exact, with no external AST/source. -/
theorem source_code (bits : List Bool) (inverse : Bool) :
    baseCode bits inverse=SemiprimeD1StackExprCodec.encode (expression bits inverse) [] :=
  SemiprimeD1StackPublicScaleInputs.source_code bits inverse
/-- Every base-validity and modulus requirement is original-derived. -/
theorem original_valid (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) (inverse : Bool) :
    1<bitValue (cached bits) ∧ Valid (cached bits) (expression bits inverse) := by
  have h:=SemiprimeD1StackPublicScaleInputs.original_valid bits hc hN inverse
  rw [←SemiprimeD1StackPublicScaleInputs.expression_original bits hc hN inverse] at h
  exact h
/-- Actual acquired inverse-normalizer word has the OLD original normalizer value. -/
theorem normalizer_source_value (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    bitValue (rootData bits (.inl (SemiprimeD1BinaryPublicAcquisition.fermatStack (.inr true))))=
      (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN).normalizer.val :=
  SemiprimeD1BinaryPublicAcquisitionBounds.public_normalizer bits hc hN
/-- Canonicality of actual acquired normalization is derived, not guard advice. -/
theorem normalizer_canonical (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (second inverse : Bool) : bitValue (normalizer bits second inverse)<bitValue (cached bits) := by
  rw [original_modulus bits hc hN]
  cases second <;> cases inverse
  · change 1<bitValue (modulus _)
    have h:=modulus_gt_four (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN);omega
  · change 1<bitValue (modulus _)
    have h:=modulus_gt_four (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN);omega
  · change 1<bitValue (modulus _)
    have h:=modulus_gt_four (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN);omega
  · change bitValue (rootData bits (.inl (SemiprimeD1BinaryPublicAcquisition.fermatStack (.inr true))))<_
    rw [normalizer_source_value bits hc hN,modulus_value]
    exact ZMod.val_lt _
private theorem cast_heq {M N : ℕ} [NeZero N] (h : M=N) (x : ZMod N) : HEq (x.val : ZMod M) x := by
  cases h
  exact heq_of_eq (ZMod.natCast_zmod_val x)
/-- Acquired normalization WORD is semantically the exact original factor,
without re-evaluating its larger AST or transporting any old execution clock. -/
theorem normalizer_meaning (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (second inverse : Bool) :
    meaning (cached bits) (.literal (normalizer bits second inverse))=
      meaning (cached bits) (if second then normalizationExpr
        (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN) (transform inverse) else oneExpr) := by
  cases second <;> cases inverse
  · rfl
  · rfl
  · rfl
  · rw [original_modulus bits hc hN]
    let p:=SemiprimePublicFactorCount.publicConfig (bitValue bits) hN
    have hv:=normalizer_source_value bits hc hN
    have h1 : HEq (meaning (modulus p) (.literal (normalizer bits true true))) p.normalizer := by
      change HEq (bitValue (rootData bits (.inl (SemiprimeD1BinaryPublicAcquisition.fermatStack (.inr true)))) :
        ZMod (bitValue (modulus p))) p.normalizer
      rw [hv]
      exact cast_heq (modulus_value p) p.normalizer
    have h2:=ringMeaning_eq p (normalizationExpr p (.inr ()))
    rw [normalizationExpr_meaning] at h2
    change HEq (meaning (modulus p) (normalizationExpr p (.inr ()))) p.normalizer at h2
    exact eq_of_heq (h1.trans h2.symm)
end RiemannGaussian.SemiprimeD1StackPublicTransformMetadata
