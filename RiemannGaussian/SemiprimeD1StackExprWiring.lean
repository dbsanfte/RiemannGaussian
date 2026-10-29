/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExpr
/-! # Concrete disjoint physical wiring for the complete evaluator -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackExprWiring
open SemiprimeD1StackExpr
/-- Shared views do not identify any distinct literal-machine data roles. -/
theorem literal_injective : Function.Injective literalStack := by decide
/-- Every actual addition data role remains distinct. -/
theorem add_injective : Function.Injective addStack := by decide
/-- Every actual subtraction data role remains distinct. -/
theorem sub_injective : Function.Injective subStack := by decide
/-- Every actual multiplication data role remains distinct. -/
theorem mul_injective : Function.Injective mulStack := by decide
/-- Frame input, saved output and restoration scratch are distinct. -/
theorem frame_injective : Function.Injective frameStack := by decide
/-- Copy input, right operand and scratch are distinct. -/
theorem copy_injective : Function.Injective copyStack := by decide
/-- Saved-field input, actual left output, scratch and flag are distinct. -/
theorem field_injective : Function.Injective fieldStack := by
  intro i j h
  rcases i with i|i <;> rcases j with j|j
  · cases i <;> cases j <;> simp_all [fieldStack]
  · cases i <;> simp_all [fieldStack]
  · cases j <;> simp_all [fieldStack]
  · cases i;cases j;rfl

/-- Every common physical bank projection is literal. -/
@[simp] theorem bank_apply (code cached saved result left right flag scratch : List Bool) (k : Stack) :
    bank code cached saved result left right flag scratch k=match k with
    | .code=>code | .modulus=>cached | .saved=>saved | .result=>result
    | .left=>left | .right=>right | .flag=>flag | .scratch=>scratch | _=>[] := rfl

@[simp] theorem update_code (code cached saved result left right flag scratch word : List Bool) :
    Function.update (bank code cached saved result left right flag scratch) .code word=
      bank word cached saved result left right flag scratch := by
  funext k;cases k <;> simp [bank]
@[simp] theorem update_result (code cached saved result left right flag scratch word : List Bool) :
    Function.update (bank code cached saved result left right flag scratch) .result word=
      bank code cached saved word left right flag scratch := by
  funext k;cases k <;> simp [bank]
@[simp] theorem update_saved (code cached saved result left right flag scratch word : List Bool) :
    Function.update (bank code cached saved result left right flag scratch) .saved word=
      bank code cached word result left right flag scratch := by
  funext k;cases k <;> simp [bank]
@[simp] theorem update_flag (code cached saved result left right flag scratch word : List Bool) :
    Function.update (bank code cached saved result left right flag scratch) .flag word=
      bank code cached saved result left right word scratch := by
  funext k;cases k <;> simp [bank]
end RiemannGaussian.SemiprimeD1StackExprWiring
