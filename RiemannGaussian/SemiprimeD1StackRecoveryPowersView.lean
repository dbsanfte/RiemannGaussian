/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryPowersPrimitives
/-! # Complete physical47-word views and actual one-word updates
These functions describe proof invariants only; no word view is an instruction.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryPowersView
open SemiprimeD1StackRecoveryPowers
/-- Literal actual47-role type for the physical store view. -/
abbrev Stack:=SemiprimeD1StackRecoveryPowers.Stack
/-- Every allocated arithmetic and caller word is explicit. -/
structure Words where
  /-- Complete36-role helper bank. -/
  rational:R.Stack→List Bool:=fun _=>[]
  /-- All eleven retained, cache and logging words. -/
  added:Aux→List Bool:=fun _=>[]
/-- Actual full physical store. -/
def bank (w:Words):Stack→List Bool:=Sum.elim w.rational w.added
/-- A caller-word write preserves all other46 actual tapes. -/
theorem update_added (w:Words) (slot:Aux) (xs:List Bool):
    Function.update (bank w) (aux slot) xs=bank {w with added:=Function.update w.added slot xs}:=by
  funext role
  rcases role with role|role
  · rfl
  · simp only [bank,aux,Function.update_apply,Sum.elim_inr,Sum.inr.injEq]
/-- An actual arithmetic-word write preserves all caller fields. -/
theorem update_rational (w:Words) (slot:R.Stack) (xs:List Bool):
    Function.update (bank w) (rational slot) xs=bank {w with rational:=Function.update w.rational slot xs}:=by
  funext role
  rcases role with role|role
  · simp only [bank,rational,Function.update_apply,Sum.elim_inl,Sum.inl.injEq]
  · rfl
/-- Physically writing one additional word. -/
def put (w:Words) (slot:Aux) (xs:List Bool):Words:={w with added:=Function.update w.added slot xs}
/-- Original four-word source view, with every private tape empty. -/
def originals (signed den q width:List Bool):Words:=
  ⟨emptyRational width,fun k=>match k with | .argumentSigned=>signed | .argumentDen=>den | .q=>q | _=>[]⟩
/-- The proof view is precisely the literal source initialization. -/
theorem originals_bank (signed den q width:List Bool):bank (originals signed den q width)=input signed den q width:=rfl
/-- Complete original width is retained; every other arithmetic role is empty. -/
theorem emptyRational_input (width:List Bool):emptyRational width=SemiprimeD1StackRationalOperation.input [] [] [] [] width:=by
  funext role
  rcases role with role|role
  · rfl
  · rcases role with role|role
    · rfl
    · cases role <;> rfl
end RiemannGaussian.SemiprimeD1StackRecoveryPowersView
