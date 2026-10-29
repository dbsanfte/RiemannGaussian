/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprBounds
import RiemannGaussian.SemiprimeD1StackWordEqualBounds
/-! # Actual two-expression public residue-equality caller
The code evaluates the first actual prefix, physically saves/drains its result,
evaluates the next actual prefix, then calls the complete binary numeric comparator.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackExprEquality
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace E
export SemiprimeD1StackExpr (Stack Label program initial input)
end E
namespace Q
export SemiprimeD1StackAdder (Stack store)
export SemiprimeD1StackWordEqual (Label code state)
end Q
/-- Eighty fixed Boolean data roles, including the complete evaluator bank. -/
abbrev Stack := E.Stack⊕(Q.Stack⊕Unit)
/-- Original physical expression stream. -/
def inputCode : Stack := .inl .code
/-- Retained original raw binary modulus. -/
def modulus : Stack := .inl .modulus
/-- The actual numeric-equality Boolean output cell. -/
def output : Stack := .inr (.inl .output)
/-- Only the comparator right input shares the actual second expression result. -/
def equalStack : Q.Stack→Stack
  | .right=>.inl .result
  | k=>.inr (.inl k)
/-- Actual left-result copy into the comparator's left operand. -/
def copyStack (k : Fin 3) : Stack :=
  if k=0 then .inl .result else if k=1 then .inr (.inl .left) else .inr (.inr ())
/-- Fixed real-call and literal component locations. -/
inductive Label where
  | start | copyLeft | clearLeft | evaluateRight | compare | done
  | expression (pc : E.Label) | copy (pc : Fin 9) | equality (pc : Q.Label)
  deriving DecidableEq,Fintype
/-- ONE closed program: no expression, evaluator, comparison or clock supplier. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.expression .start) .copyLeft
  | .copyLeft=>.call (.copy 0) .clearLeft
  | .clearLeft=>.base (.pop (.inl .result) .evaluateRight .clearLeft .clearLeft)
  | .evaluateRight=>.call (.expression .start) .compare
  | .compare=>.call (.equality .loop) .done
  | .done=>.base .halt
  | .expression pc=>SemiprimeD1StackValidationLink.instruction Sum.inl Label.expression (E.program pc)
  | .copy pc=>SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code pc)
  | .equality pc=>SemiprimeD1StackMultiplierLink.instruction equalStack Label.equality (Q.code pc)
/-- Literal physical evaluator/comparator/copy payload view. -/
def store (expr : E.Stack→List Bool) (compared : Q.Stack→List Bool) (scratch : List Bool) : Stack→List Bool :=
  Sum.elim expr (Sum.elim compared (fun _=>scratch))
/-- Only original physical combined syntax and binary cache are supplied. -/
def input (code cached : List Bool) : Stack→List Bool := store (E.input code cached) (Q.store [] [] [] []) []
/-- Closed physical two-expression entry, with empty operand/work/return stacks. -/
def initial (code cached : List Bool) : C.State Stack Label := ⟨some .start,none,none,input code cached,[]⟩
/-- Comparator operands/output are physically distinct after shared-result wiring. -/
theorem equal_injective : Function.Injective equalStack := by
  intro i j h
  cases i <;> cases j <;> simp_all [equalStack]
/-- Actual copy source, destination and restoration scratch are distinct. -/
theorem copy_injective : Function.Injective copyStack := by decide
/-- Actual finite evaluator/equality machine; preparing syntax/cache is caller work. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine inputCode output .start program
/-- Every data and real return alphabet is finite before any original input. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite inputCode output Label.start program
/-- No decoded expression, Nat, list or function occurs in internal finite control. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite inputCode output Label.start program
/-- Fixed literal data-role inventory. -/
theorem stack_card : Fintype.card Stack=80 := by decide
end RiemannGaussian.SemiprimeD1StackExprEquality
