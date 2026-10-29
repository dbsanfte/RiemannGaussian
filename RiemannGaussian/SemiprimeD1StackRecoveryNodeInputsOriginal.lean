/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsStorage
/-! # Six actual cached Node operands, exact original array bytes and derived Valid/Fits
The whole source has five physical original inputs. The optional Grid-ready
entry accepts only the actual whole Grid cache. A literal N-only controller and
the subsequent complete weight-array call are separate constructive joins.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsOriginal
open SemiprimeD1StackRecoveryNodeInputs SemiprimeD1StackRecoveryNodeInputsEncoding
open SemiprimeD1StackRecoveryNodeInputsBounds SemiprimeD1StackRecoveryNodeInputsResource
/-- Both whole calls leave EVERY old112 Grid/affine input/cache/shadow byte unchanged. -/
theorem old_retained (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) (k : A.Stack) :
    result a M u selected t width (affine k)=E.result a M u selected t width k :=
  SemiprimeD1StackRecoveryNodeInputsView.old_retained _ _ _ k
/-- The actual inverse output is the exact whole native chronological inverse tape. -/
theorem inverse_output (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) :
    result a M u selected t width inverseOutput=inverseTape a M u selected width := by
  unfold result V.result
  rw [Function.update_of_ne (by decide:inverseOutput≠powersOutput)]
  change Function.update _ inverseOutput _ inverseOutput=_
  rw [Function.update_self]
/-- The actual powers output is the exact whole chronological power tape. -/
theorem powers_output (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) :
    result a M u selected t width powersOutput=powerTape a M u selected width := by
  unfold result V.result
  rw [Function.update_self]
/-- The actual Ezero sign/magnitude field is retained from Grid, not supplied by the caller. -/
theorem scalar_signed (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) :
    result a M u selected t width scalarSigned=SemiprimeD1StackRecoveryPowersSpec.signed (scalar a M u selected width) :=
  old_retained a M u selected t width _
/-- The actual Ezero denominator remains binary and byte-exact. -/
theorem scalar_den (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) :
    result a M u selected t width scalarDen=(scalar a M u selected width).denominator :=
  old_retained a M u selected t width _
/-- Retained q is acquired by the real affine ready source, never an additional original input. -/
theorem q_output (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) :
    result a M u selected t width qWord=List.replicate (E.retained a M u selected) true :=
  old_retained a M u selected t width _
/-- The original physical W bits are preserved literally, including W0 and arbitrary template bits. -/
theorem width_output (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool) :
    result a M u selected t width widthWord=width :=
  old_retained a M u selected t width _
/-- Complete inverse words are identical to the native Node's actual local denominator/inverse construction. -/
theorem inverse_native (a M u : ℕ) (selected : Fin (2^(a+1))) (width : List Bool) :
    inverseWords a M u selected width=
      (SemiprimeNormalizedInverseBits.build width
        (SemiprimeAffineJetBits.build width (E.retained a M u selected)
          (SemiprimeD1RecoveryGridBits.acquire width a M u selected).grid.slopes).words
        (E.retained a M u selected)).words.toList := by
  simp only [inverseWords,SemiprimeD1StackNormalizedInverseEncoding.outputWords,
    SemiprimeD1StackNormalizedInverseAcquisition.acquired,E.array,Array.toArray_toList]
/-- Complete powers retain the native index0 literal ONE and every original ordered byte, even W0. -/
theorem powers_native (a M u : ℕ) (selected : Fin (2^(a+1))) (width : List Bool) :
    powerWords a M u selected width=
      (SemiprimeD1RecoveryScalarWeightBits.powers width (argument a M u selected width)
        (SemiprimeD1RecoveryScalarRun.indices (E.retained a M u selected)).value).words :=
  SemiprimeD1StackRecoveryPowersSpec.array_native _ _ _
/-- Original dimensions alone discharge inverse Valid/Bounded and exact original inverse values. -/
theorem inverse_valid (a M u : ℕ) (selected : Fin (2^(a+1))) (width : List Bool)
    (hu : u≤M) (hW : SemiprimeD1RecoveryNodeBits.width a M≤width.length) :
    SemiprimeJetBits.decode (inverseWords a M u selected width).toArray=
      (SemiprimeD1JetRecoveryWeights.acquire a (SemiprimeD1TaperedLoss.height M u) u selected.val).inverse.coefficients ∧
      SemiprimeJetBits.Valid (inverseWords a M u selected width).toArray ∧
      SemiprimeJetBits.Bounded (inverseWords a M u selected width).toArray width.length := by
  rw [inverse_native,Array.toArray_toList]
  exact SemiprimeD1StackNormalizedInverseLegacy.original_valid width a M u selected hu hW
/-- Actual stopped Grid argument agrees with the frozen powers semantic bridge. -/
theorem argument_original (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) :
    SemiprimeD1StackRecoveryPowersValues.argument a M u t width=argument a M u selected width := by
  unfold SemiprimeD1StackRecoveryPowersValues.argument
  rw [SemiprimeD1StackRecoveryGridOriginal.result_original a M u selected t width ht]
  rfl
/-- Actual original metadata/width, not a supplied sequence of fit witnesses, validates every cached power. -/
theorem powers_valid (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) (hu : u≤M)
    (hW : SemiprimeD1RecoveryNodeBits.width a M≤width.length) :
    (powerWords a M u selected width).map SemiprimeRationalBits.RationalWord.value=
      (SemiprimeD1RecoveryWeightRun.powersRun (SemiprimeD1WeightPrecision.argument a selected.val) (E.retained a M u selected)).value.toList ∧
      (∀x∈powerWords a M u selected width,x.Valid) ∧
      (∀x∈powerWords a M u selected width,SemiprimeRationalBits.Width x width.length) := by
  have h:=SemiprimeD1StackRecoveryPowersValues.original_values a M u selected t width ht hu hW
  rw [argument_original a M u selected t width ht] at h
  exact h
/-- Whole real source and all six actually acquired ready operands hold for the SAME execution. -/
theorem source_run_original (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) :
    ∃s≤polynomial a M u t width,SemiprimeD1StackCalls.run program s
      (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)=some (done a M u selected t width) ∧
      (done a M u selected t width).data inverseOutput=inverseTape a M u selected width ∧
      (done a M u selected t width).data powersOutput=powerTape a M u selected width ∧
      (done a M u selected t width).data scalarSigned=SemiprimeD1StackRecoveryPowersSpec.signed (scalar a M u selected width) ∧
      (done a M u selected t width).data scalarDen=(scalar a M u selected width).denominator ∧
      (done a M u selected t width).data qWord=List.replicate (E.retained a M u selected) true ∧
      (done a M u selected t width).data widthWord=width ∧
      (∀k,(done a M u selected t width).data (affine k)=E.result a M u selected t width k) := by
  obtain ⟨s,hs,hr⟩:=source_run_bounded a M u selected t width ht
  exact ⟨s,hs,hr,inverse_output a M u selected t width,powers_output a M u selected t width,
    scalar_signed a M u selected t width,scalar_den a M u selected t width,q_output a M u selected t width,
    width_output a M u selected t width,old_retained a M u selected t width⟩
end RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsOriginal
