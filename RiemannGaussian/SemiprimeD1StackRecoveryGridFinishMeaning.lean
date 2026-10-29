/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridExecution
/-! # Complete exact stopped grid bank and scalar/argument bytes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridFinishMeaning
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView
namespace Model
export SemiprimeD1StackRecoveryGridModel (Payload view center alpha node)
end Model
namespace Old
export SemiprimeRationalBits (executeOperation)
end Old
/-- Exact actual Ezero word acquired by the real inverse and multiplication. -/
def scalar (width:List Bool) (p:Model.Payload) :SemiprimeRationalBits.RationalWord:=
  (Old.executeOperation .mul p.numerator (Old.executeOperation .inv p.denominator p.denominator width).word width).word
/-- Exact actual original-node negation, with legacy zero sign/width preserved. -/
def negative (a:Nat) (t width:List Bool) :SemiprimeRationalBits.RationalWord:=
  (Old.executeOperation .neg (Model.node a t) (Model.node a t) width).word
/-- Exact actual center-minus-node local point. -/
def point (a:Nat) (t width:List Bool) :SemiprimeRationalBits.RationalWord:=
  (Old.executeOperation .add (Model.center a width) (negative a t width) width).word
/-- Exact actual inverse alpha. -/
def inverse (a:Nat) (width:List Bool) :SemiprimeRationalBits.RationalWord:=
  (Old.executeOperation .inv (Model.alpha a width) (Model.alpha a width) width).word
/-- Exact actual local argument, from the real point and reciprocal caches. -/
def argument (a:Nat) (t width:List Bool) :SemiprimeRationalBits.RationalWord:=
  (Old.executeOperation .mul (point a t width) (inverse a width) width).word
/-- Complete104-word final bank: original sources retained, q/work cleared and both exact final outputs acquired. -/
def result (a M u:Nat) (t width:List Bool) (p:Model.Payload) :Words:=
  putReg (putReg (Model.view a M u 0 t [] width p) .scalar (scalar width p)) .argument (argument a t width)
/-- Same actual six operations and all physical cleanup produce exactly the canonical complete stopped bank. -/
theorem finish_eq (a M u:Nat) (t width:List Bool) (p:Model.Payload) :
    bank (SemiprimeD1StackRecoveryGridFinal.result
      (Model.view a M u 0 t (SemiprimeD1StackRecoveryGridLoopPrimitives.zeroWord a) width p) width)=
      bank (result a M u t width p):=by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · rcases k with k|k
          · rcases k with ⟨r,b⟩
            cases r <;> cases b <;> rfl
          · cases k <;> rfl
/-- Exact whole-source final bank for every actual metadata/index/template input, with no unacquired coefficient supplier. -/
theorem source_result (a M u:Nat) (t width:List Bool) :
    SemiprimeD1StackRecoveryGridExecution.result a M u t width=
      bank (result a M u t width (SemiprimeD1StackRecoveryGridExecution.payload a M u t width)):=
  finish_eq a M u t width _
end RiemannGaussian.SemiprimeD1StackRecoveryGridFinishMeaning
