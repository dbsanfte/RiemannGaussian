/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalOperationCalls
/-! # Actual sign parsing and preserving magnitude acquisition from the five tapes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRationalOperationSetup
open SemiprimeD1StackRationalOperation SemiprimeD1StackRationalOperationEncoding
open SemiprimeD1StackRationalOperationCalls SemiprimeD1StackProcedureTrace
/-- Binary operations actually read the second signed word; unary operations retain it untouched. -/
def binary (op:Op) :Bool:=match op with | .add|.mul=>true | .neg|.inv=>false
/-- Complete retained original inputs with the first actual magnitude acquired. -/
def leftReady (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :Words:=
  {originals (sx::xn) xd (sy::yn) yd template with leftMagnitude:=xn}
/-- Both binary magnitudes are acquired; unary entries physically leave the second cache empty. -/
def ready (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :Words:=
  {leftReady sx xn xd sy yn yd template with rightMagnitude:=if binary op then yn else []}
/-- Exact left sign-word preserving copy and actual sign-head pop. -/
theorem left_run (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    Runs program ((5*(xn.length+1)+4)+1) (localLabel .start op false false)
      (input (sx::xn) xd (sy::yn) yd template)
      (localLabel (if binary op then .rightCopy else .dispatch) op sx false)
      (bank (leftReady sx xn xd sy yn yd template)):=by
  rw [input_bank]
  let w:=originals (sx::xn) xd (sy::yn) yd template
  have h0:=P.copy_call .signedLeft (localLabel .start op false false) (localLabel .parseLeft op false false) rfl
    (bank w) (sx::xn) [] rfl rfl rfl
  change Runs _ _ _ _ _ (Function.update (bank w) (aux .leftMagnitude) ((sx::xn)++[])) at h0
  rw [List.append_nil,update_leftMagnitude] at h0
  have h1:=P.pop_run (localLabel .parseLeft op false false) (localLabel .abort op false false)
    (localLabel (if op=.add ∨ op=.mul then .rightCopy else .dispatch) op false false)
    (localLabel (if op=.add ∨ op=.mul then .rightCopy else .dispatch) op true false)
    (aux .leftMagnitude) (bank {w with leftMagnitude:=sx::xn}) (sx::xn) rfl rfl
  rw [update_leftMagnitude] at h1
  have h:=P.join h0 h1
  cases op <;> cases sx <;> exact h
/-- Actual right sign-word preserving copy and actual sign-head pop. -/
theorem right_run (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    Runs program ((5*(yn.length+1)+4)+1) (localLabel .rightCopy op sx false)
      (bank (leftReady sx xn xd sy yn yd template)) (localLabel .dispatch op sx sy)
      (bank {leftReady sx xn xd sy yn yd template with rightMagnitude:=yn}):=by
  let w:=leftReady sx xn xd sy yn yd template
  have h0:=P.copy_call .signedRight (localLabel .rightCopy op sx false) (localLabel .parseRight op sx false) rfl
    (bank w) (sy::yn) [] rfl rfl rfl
  change Runs _ _ _ _ _ (Function.update (bank w) (aux .rightMagnitude) ((sy::yn)++[])) at h0
  rw [List.append_nil,update_rightMagnitude] at h0
  have h1:=P.pop_run (localLabel .parseRight op sx false) (localLabel .abort op sx false)
    (localLabel .dispatch op sx false) (localLabel .dispatch op sx true)
    (aux .rightMagnitude) (bank {w with rightMagnitude:=sy::yn}) (sy::yn) rfl rfl
  rw [update_rightMagnitude] at h1
  have h:=P.join h0 h1
  cases sy <;> exact h
/-- Own actual setup clock counts only actual copies/sign-head reads. -/
def setupTime (op:Op) (xn yn:List Bool) :Nat:=
  ((5*(xn.length+1)+4)+1)+(if binary op then (5*(yn.length+1)+4)+1 else 0)
/-- Whole actual five-word front door reaches the correct finite arithmetic branch with genuine parsed signs. -/
theorem setup_run (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    Runs program (setupTime op xn yn) (localLabel .start op false false)
      (input (sx::xn) xd (sy::yn) yd template)
      (localLabel .dispatch op sx (if binary op then sy else false))
      (bank (ready op sx xn xd sy yn yd template)):=by
  have h0:=left_run op sx xn xd sy yn yd template
  have h1:=right_run op sx xn xd sy yn yd template
  cases op with
  | add=>exact P.join h0 h1
  | mul=>exact P.join h0 h1
  | neg=>exact h0
  | inv=>exact h0
end RiemannGaussian.SemiprimeD1StackRationalOperationSetup
