/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridOriginal
import RiemannGaussian.SemiprimeD1RecoveryNodeBits
/-! # Original-dimension Valid/Fits discharge for the actual whole grid source
Width comes from the literal original a/M polynomial, and u≤M from guard
lineage. No operation-by-operation Fits or coefficient answer is assumed.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridValues
open SemiprimeD1StackRecoveryGrid
namespace Exec
export SemiprimeD1StackRecoveryGridExecution (result payload)
end Exec
namespace E
export SemiprimeD1StackRecoveryGridEncoding (outputWord)
end E
namespace Old
export SemiprimeD1RecoveryGridBits (acquire gridWidth acquire_grid_correct acquire_scalar_correct acquire_argument_correct)
end Old
/-- The actual original width producer supplies the whole grid's normalization/fit capacity from dimensions alone. -/
theorem width_sufficient (a M u:Nat) (width:List Bool) (hu:u≤M)
    (hW:SemiprimeD1RecoveryNodeBits.width a M≤width.length) :Old.gridWidth a (SemiprimeD1TaperedLoss.height M u) u≤width.length:=
  (SemiprimeD1RecoveryNodeBits.grid_width_le a M u hu).trans hW
/-- Both physically acquired grid products have exact original values and positive actual binary denominators. -/
theorem grid_products (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val) (hu:u≤M)
    (hW:SemiprimeD1RecoveryNodeBits.width a M≤width.length) :
    let native:=SemiprimeD1RecoveryWeightRun.gridRows (SemiprimeD1RecoveryWeightRun.geometry a selected.val)
      (SemiprimeD1TaperedLoss.height M u) u selected.val
      (SemiprimeD1RecoveryScalarRun.indices (SemiprimeD1RecoveryWeightRun.geometry a selected.val).size).value
    (E.outputWord (Exec.result a M u t width) .gridNum).value=(native.numerator:ℚ) ∧
    (E.outputWord (Exec.result a M u t width) .gridDen).value=(native.denominator:ℚ) ∧
    (E.outputWord (Exec.result a M u t width) .gridNum).Valid ∧
    (E.outputWord (Exec.result a M u t width) .gridDen).Valid:=by
  have h:=Old.acquire_grid_correct width a M u selected (width_sufficient a M u width hu hW)
  dsimp only
  rw [SemiprimeD1StackRecoveryGridOriginal.result_original a M u selected t width ht,
    SemiprimeD1StackRecoveryGridEncoding.numerator_original a M u selected t width,SemiprimeD1StackRecoveryGridEncoding.denominator_original a M u selected t width]
  exact ⟨h.1,h.2.1,h.2.2.2.1,h.2.2.2.2.1⟩
/-- Every physically framed slope, including all repetitions and original forward order, is valid and has the exact original rational value. -/
theorem slope_values (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val) (hu:u≤M)
    (hW:SemiprimeD1RecoveryNodeBits.width a M≤width.length) :
    (Exec.payload a M u t width).slopes.map SemiprimeRationalBits.RationalWord.value=
      (SemiprimeD1RecoveryWeightRun.gridRows (SemiprimeD1RecoveryWeightRun.geometry a selected.val)
        (SemiprimeD1TaperedLoss.height M u) u selected.val
        (SemiprimeD1RecoveryScalarRun.indices (SemiprimeD1RecoveryWeightRun.geometry a selected.val).size).value).slopes ∧
    (∀x∈(Exec.payload a M u t width).slopes,x.Valid):=by
  have h:=Old.acquire_grid_correct width a M u selected (width_sufficient a M u width hu hW)
  rw [SemiprimeD1StackRecoveryGridLoopMeaning.acquire_payload a M u selected t width ht]
  exact ⟨h.2.2.1,h.2.2.2.2.2.1⟩
/-- Actual Ezero is normalized and fitted with capacity derived from the original dimensions; no raw answer or Fits sequence is supplied. -/
theorem scalar_value (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val) (hu:u≤M)
    (hW:SemiprimeD1RecoveryNodeBits.width a M≤width.length) :
    (E.outputWord (Exec.result a M u t width) .scalar).value=
      SemiprimeD1JetRecoveryGrid.Ezero a (SemiprimeD1TaperedLoss.height M u) u selected.val ∧
    (E.outputWord (Exec.result a M u t width) .scalar).Valid ∧
    SemiprimeRationalBits.Width (E.outputWord (Exec.result a M u t width) .scalar) width.length:=by
  rw [SemiprimeD1StackRecoveryGridOriginal.result_original a M u selected t width ht,
    SemiprimeD1StackRecoveryGridEncoding.scalar_original a M u selected t width]
  exact Old.acquire_scalar_correct width a M u selected (width_sufficient a M u width hu hW)
/-- Actual local argument retains the same exact original value, valid denominator and paid fitted width. -/
theorem argument_value (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val) (hu:u≤M)
    (hW:SemiprimeD1RecoveryNodeBits.width a M≤width.length) :
    (E.outputWord (Exec.result a M u t width) .argument).value=SemiprimeD1WeightPrecision.argument a selected.val ∧
    (E.outputWord (Exec.result a M u t width) .argument).Valid ∧
    SemiprimeRationalBits.Width (E.outputWord (Exec.result a M u t width) .argument) width.length:=by
  rw [SemiprimeD1StackRecoveryGridOriginal.result_original a M u selected t width ht,
    SemiprimeD1StackRecoveryGridEncoding.argument_original a M u selected t width]
  exact Old.acquire_argument_correct width a M u selected (width_sufficient a M u width hu hW)
end RiemannGaussian.SemiprimeD1StackRecoveryGridValues
