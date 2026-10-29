/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridFront
import RiemannGaussian.SemiprimeD1StackRecoveryGridByteBounds
/-! # Complete original-input physical grid-loop bank
The payload is a proof invariant over actual acquired words. No payload, grid
report, dimension, rational evaluator or cache answer enters finite control.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridModel
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView
open SemiprimeD1StackRecoveryGridOperationInput
/-- Only the three actual evolving grid outputs, described solely for source trace induction. -/
structure Payload where
  /-- Actual acquired signed numerator product. -/
  numerator:SemiprimeRationalBits.RationalWord
  /-- Actual acquired signed denominator product. -/
  denominator:SemiprimeRationalBits.RationalWord
  /-- Exact chronological/repeated actual slope words. -/
  slopes:List SemiprimeRationalBits.RationalWord
/-- Literal initial right-fold bases and no acquired slopes. -/
def one :Payload:=⟨SemiprimeJetBits.oneWord,SemiprimeJetBits.oneWord,[]⟩
/-- Actual acquired fitted center, with literal a0 one preserved at W0. -/
def center (a:Nat) (width:List Bool) :SemiprimeRationalBits.RationalWord:=
  (SemiprimeD1RecoveryPowerBits.power width SemiprimeD1RecoveryGridBits.twoWord a).word
/-- Actual acquired alpha power, separate from the true geometric grid size. -/
def alpha (a:Nat) (width:List Bool) :SemiprimeRationalBits.RationalWord:=
  (SemiprimeD1RecoveryPowerBits.power width SemiprimeD1RecoveryGridBits.twoWord (a+1)).word
/-- Exact signed original node cache from the physically acquired a+2 template. -/
def node (a:Nat) (t:List Bool) :SemiprimeRationalBits.RationalWord:=
  ⟨⟨false,SemiprimeD1StackWordFitExecution.result t (List.replicate (a+2) false)⟩,[true]⟩
/-- Every physically retained or evolving rational register; all other actual registers are clear. -/
def cache (a:Nat) (t width:List Bool) (p:Payload) :Reg→Option SemiprimeRationalBits.RationalWord
  | .two=>some SemiprimeD1RecoveryGridBits.twoWord | .center=>some (center a width)
  | .alpha=>some (alpha a width) | .node=>some (node a t)
  | .gridNum=>some p.numerator | .gridDen=>some p.denominator | _=>none
/-- Complete physical signed/denominator register bytes. -/
def registers (a:Nat) (t width:List Bool) (p:Payload) (r:Reg×Bool) :List Bool:=
  match cache a t width p r.1 with
  | none=>[] | some word=>if r.2 then word.denominator else signed word
/-- Every original, actual current q/todo and chronological slope buffer at the row boundary. -/
def auxiliary (a M u n:Nat) (t q:List Bool) (p:Payload) :Aux→List Bool
  | .originalA=>List.replicate a true | .originalM=>List.replicate M true | .originalU=>List.replicate u true
  | .originalT=>t | .q=>q | .todo=>List.replicate n true | .indexTemplate=>List.replicate (a+2) false
  | .slopes=>slopeTape p.slopes | _=>[]
/-- All104 actual physical words at a genuine row/finish boundary. -/
def view (a M u n:Nat) (t q width:List Bool) (p:Payload) :Words:=
  {rational:=emptyRational width,
   division:=SemiprimeD1StackUnaryDivmod.contents [] [] [] [] (List.replicate (SemiprimeD1TaperedLoss.height M u) true) [],
   registers:=registers a t width p,auxiliary:=auxiliary a M u n t q p}
/-- The same actual original-input source reaches EXACTLY the literal initial loop invariant. -/
theorem front_eq (a M u:Nat) (t width:List Bool) :
    bank (SemiprimeD1StackRecoveryGridFront.result a M u t width)=
      bank (view a M u (2^(a+1)) t (SemiprimeD1StackRecoveryGridDecrement.difference
        (SemiprimeD1StackRecoveryGridFront.sizeWord a)) width one):=by
  funext k
  rcases k with k|k
  · change (SemiprimeD1StackRecoveryGridAcquisition.result a M u t width).rational k=emptyRational width k
    exact congrFun (SemiprimeD1StackRecoveryGridFront.acquired_rational a M u t width) k
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
/-- Exact physically parsed retained center cache. -/
theorem center_word (a M u n:Nat) (t q width:List Bool) (p:Payload) :getReg (view a M u n t q width p) .center=center a width:=rfl
/-- Exact physically parsed retained alpha cache. -/
theorem alpha_word (a M u n:Nat) (t q width:List Bool) (p:Payload) :getReg (view a M u n t q width p) .alpha=alpha a width:=rfl
/-- Exact physically parsed original node cache. -/
theorem node_word (a M u n:Nat) (t q width:List Bool) (p:Payload) :getReg (view a M u n t q width p) .node=node a t:=rfl
/-- Exact actual cached right-fold numerator. -/
theorem numerator_word (a M u n:Nat) (t q width:List Bool) (p:Payload) :getReg (view a M u n t q width p) .gridNum=p.numerator:=rfl
/-- Exact actual cached right-fold denominator. -/
theorem denominator_word (a M u n:Nat) (t q width:List Bool) (p:Payload) :getReg (view a M u n t q width p) .gridDen=p.denominator:=rfl
/-- Exact original node bytes when the retained physical binary input denotes an original finite grid index. -/
theorem node_original (a n:Nat) (t:List Bool) (hv:SemiprimeBitArithmetic.bitValue t=n) (hn:n<2^(a+1)) :
    node a t=(SemiprimeD1RecoveryGridBits.index a n).word:=by
  unfold node
  rw [SemiprimeD1StackRecoveryGridNode.fit_index a n t hv hn]
  rfl
end RiemannGaussian.SemiprimeD1StackRecoveryGridModel
