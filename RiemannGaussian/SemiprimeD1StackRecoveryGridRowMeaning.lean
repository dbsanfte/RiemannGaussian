/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridRow
import RiemannGaussian.SemiprimeD1StackRecoveryGridModel
/-! # Exact complete physical row-state refinement
All rational/list expressions below describe actual cache words already proved
acquired by the same finite row program. No expression here is a runtime input.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridRowMeaning
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView
namespace Model
export SemiprimeD1StackRecoveryGridModel (Payload view center alpha node)
end Model
namespace Row
export SemiprimeD1StackRecoveryGridRow (order centerBit geometry indexed result)
end Row
namespace Old
export SemiprimeRationalBits (executeOperation)
export SemiprimeD1RecoveryPowerBits (power)
end Old
/-- Actual multiplicity value, acquired by the same physical retained-height/order/u loop. -/
def multiplicity (a M u:Nat) (q:List Bool) :Nat:=SemiprimeD1TaperedLoss.height M u*(u-Row.order a q)
/-- Exact copied sign-prefixed current integer. -/
def index (q:List Bool) :SemiprimeRationalBits.RationalWord:=⟨⟨false,q⟩,[true]⟩
/-- Actual fitted negated q cache. -/
def negative (width q:List Bool) :SemiprimeRationalBits.RationalWord:=(Old.executeOperation .neg (index q) (index q) width).word
/-- Actual fitted center-minus-q cache. -/
def numeratorBase (a:Nat) (q width:List Bool) :SemiprimeRationalBits.RationalWord:=
  (Old.executeOperation .add (Model.center a width) (negative width q) width).word
/-- Actual fitted original-node-minus-q cache. -/
def denominatorBase (a:Nat) (t q width:List Bool) :SemiprimeRationalBits.RationalWord:=
  (Old.executeOperation .add (Model.node a t) (negative width q) width).word
/-- Actual numerator power with accumulator FIRST and difference base SECOND. -/
def numeratorPower (a M u:Nat) (q width:List Bool) :SemiprimeRationalBits.RationalWord:=
  (Old.power width (numeratorBase a q width) (multiplicity a M u q)).word
/-- Actual denominator power with accumulator FIRST and difference base SECOND. -/
def denominatorPower (a M u:Nat) (t q width:List Bool) :SemiprimeRationalBits.RationalWord:=
  (Old.power width (denominatorBase a t q width) (multiplicity a M u q)).word
/-- Actual cached denominator reciprocal. -/
def reciprocal (a:Nat) (t q width:List Bool) :SemiprimeRationalBits.RationalWord:=
  (Old.executeOperation .inv (denominatorBase a t q width) (denominatorBase a t q width) width).word
/-- Actual fitted slope from the same acquired alpha/base caches. -/
def slope (a:Nat) (t q width:List Bool) :SemiprimeRationalBits.RationalWord:=
  (Old.executeOperation .mul (Model.alpha a width) (reciprocal a t q width) width).word
/-- Actual non-skipped three-cache update; both right folds retain power FIRST/tail SECOND order. -/
def work (a M u:Nat) (t q width:List Bool) (p:Model.Payload) :Model.Payload:=
  ⟨(Old.executeOperation .mul (numeratorPower a M u q width) p.numerator width).word,
    (Old.executeOperation .mul (denominatorPower a M u t q width) p.denominator width).word,
    List.replicate (multiplicity a M u q) (slope a t q width)++p.slopes⟩
/-- Actual two finite skip tests, followed only when both fail by the literal acquired row body. -/
def step (a M u:Nat) (t q width:List Bool) (p:Model.Payload) :Model.Payload:=
  if Row.centerBit a q then p else if SemiprimeBitArithmetic.bitValue q=SemiprimeBitArithmetic.bitValue t then p
  else work a M u t q width p
/-- Physical repeated-row framing is EXACT chronological vector concatenation, including every empty field and repeat. -/
theorem rows_tape (x:SemiprimeRationalBits.RationalWord) (n:Nat) (xs:List SemiprimeRationalBits.RationalWord) :
    SemiprimeD1StackRecoveryGridRepeats.rows x n (slopeTape xs)=slopeTape (List.replicate n x++xs):=by
  rw [SemiprimeD1StackRecoveryGridRepeats.rows_replicate]
  simp only [slopeTape,List.foldr_append]
/-- Both actual skip paths restore the full row invariant and preserve the unchanged payload. -/
theorem skipped_eq (a M u n:Nat) (t q width:List Bool) (p:Model.Payload) :
    bank (SemiprimeD1StackRecoveryGridRowCleanup.result (Row.geometry (Model.view a M u (n+1) t q width p) a n q))=
      bank (Model.view a M u n t q width p):=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · cases k <;> rfl
        · rcases k with k|k
          · rcases k with ⟨r,b⟩
            cases r <;> cases b <;> rfl
          · cases k <;> rfl
/-- The full actual work path updates EXACT numerator/denominator/slope bytes and restores every other source/work field. -/
theorem worked_eq (a M u n:Nat) (t q width:List Bool) (p:Model.Payload) :
    bank (SemiprimeD1StackRecoveryGridRowWork.result (Row.indexed (Model.view a M u (n+1) t q width p) a n q)
      width (SemiprimeD1TaperedLoss.height M u) u (Row.order a q))=
      bank (Model.view a M u n t q width (work a M u t q width p)):=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · cases k <;> rfl
        · rcases k with k|k
          · rcases k with ⟨r,b⟩
            cases r <;> cases b <;> rfl
          · cases k <;> first | rfl | exact rows_tape _ _ _
/-- Complete actual row has exactly one true metadata visit and the original unchanged or updated chronological payload. -/
theorem row_eq (a M u n:Nat) (t q width:List Bool) (p:Model.Payload) :
    bank (Row.result (Model.view a M u (n+1) t q width p) width a (SemiprimeD1TaperedLoss.height M u) u n q t)=
      bank (Model.view a M u n t q width (step a M u t q width p)):=by
  unfold Row.result step
  split
  · exact skipped_eq a M u n t q width p
  · split
    · exact skipped_eq a M u n t q width p
    · exact worked_eq a M u n t q width p
end RiemannGaussian.SemiprimeD1StackRecoveryGridRowMeaning
