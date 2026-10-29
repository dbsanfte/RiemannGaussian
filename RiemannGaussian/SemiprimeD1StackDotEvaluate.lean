/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprDotBounds
import RiemannGaussian.SemiprimeD1StackExprBounds

/-! # Actual dot-source construction joined directly to numerical execution
The acquired syntax stack IS the evaluator's code stack. Both whole programs
execute through real finite-label calls; no AST, getter, exponent or evaluator
is supplied. Inputs remain physical prepared caches and the binary modulus.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackDotEvaluate
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace D
export SemiprimeD1StackExprDot (Stack Label Cache Work program bank initial)
end D
namespace E
export SemiprimeD1StackExpr (Stack Label program bank input initial)
end E

/-- Ninety-seven fixed Boolean data roles; the unused private code role stays empty. -/
abbrev Stack := D.Stack⊕E.Stack
/-- Actual shared source-output/evaluator-input stack. -/
def code : Stack := .inl .output
/-- Retained physical binary modulus, with no conversion to a unary value. -/
def modulus : Stack := .inr .modulus
/-- Whole original numerical dot output. -/
def output : Stack := .inr .result
/-- Direct physical wiring: no code copying or native source transport. -/
def expressionStack : E.Stack→Stack
  | .code => code
  | k => .inr k
/-- Fixed component entry, real continuation and nested control locations. -/
inductive Label where
  | start | evaluate | done
  | source (pc : D.Label) | expression (pc : E.Label)
  deriving Fintype
/-- ONE actual source-and-evaluation instruction program. -/
def program : Label→C.Instruction Stack Label
  | .start => .call (.source (.control .start)) .evaluate
  | .evaluate => .call (.expression .start) .done
  | .done => .base .halt
  | .source pc => SemiprimeD1StackValidationLink.instruction Sum.inl Label.source (D.program pc)
  | .expression pc => SemiprimeD1StackValidationLink.instruction expressionStack Label.expression (E.program pc)
/-- Reached physical data view, with the actual shared code as the left output. -/
def store (c : D.Cache) (codeWord : List Bool) (expr : E.Stack→List Bool) : Stack→List Bool :=
  Sum.elim (D.bank c {output:=codeWord}) expr
/-- Input contains only prepared physical argument tapes, modulus and suffix. -/
def initial (c : D.Cache) (cached tail : List Bool) : C.State Stack Label :=
  ⟨some .start,none,none,store c tail (E.input [] cached),[]⟩
/-- Direct-code inclusion has no overlapping evaluator roles. -/
theorem expressionStack_injective : Function.Injective expressionStack := by
  intro i j h
  cases i <;> cases j <;> simp_all [expressionStack,code]
/-- Actual finite bit machine for the SAME two executed programs. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (.inl .base) output .start program
/-- Data and return-tag alphabets are fixed and finite before every input. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite (.inl .base) output Label.start program
/-- Internal control carries no input-sized integer, list, expression or closure. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite (.inl .base) output Label.start program
/-- Every Boolean register is included in subsequent prefix storage bounds. -/
theorem stack_card : Fintype.card Stack=97 := by decide

end RiemannGaussian.SemiprimeD1StackDotEvaluate
