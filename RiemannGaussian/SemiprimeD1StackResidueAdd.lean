/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAdderExecution
import RiemannGaussian.SemiprimeD1StackDividerExecution
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
import RiemannGaussian.SemiprimeD1StackPhysicalLoops
/-! # Actual general-modulus residue addition
The binary ripple sum is the restoring divider's literal input. Modulus copying,
quotient cleanup and every real call are executed by the fixed instruction table.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackResidueAdd
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace A
export SemiprimeD1StackAdder (Stack Label code store)
end A
namespace D
export SemiprimeD1StackDivider (Stack Label code payload)
end D
/-- Seventeen fixed physical Boolean data roles. -/
abbrev Stack := A.Stack⊕(D.Stack⊕Bool)
/-- The raw binary modulus cache, retained literally. -/
def modulus : Stack := .inr (.inr false)
/-- Actual copy-restoration workspace. -/
def copyTemporary : Stack := .inr (.inr true)
/-- Direct sum-to-division input wiring; all other divider roles are distinct. -/
def divideStack : D.Stack→Stack
  | .inr .input=>.inl .output
  | k=>.inr (.inl k)
/-- Fixed cached-modulus copy wiring. -/
def copyStack (k : Fin 3) : Stack :=
  if k=0 then modulus else if k=1 then divideStack (.inr .divisor) else copyTemporary
/-- Fixed real procedure and arithmetic labels. -/
inductive Label where
  | start | copyModulus | divide | clearQuotient | done
  | addition (pc : A.Label) | copy (pc : Fin 9) | division (pc : D.Label)
  deriving DecidableEq,Fintype,Repr
/-- Closed finite code; no sum, remainder, branch or elapsed answer is supplied. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.addition (.start false)) .copyModulus
  | .copyModulus=>.call (.copy 0) .divide
  | .divide=>.call (.division (.control .start)) .clearQuotient
  | .clearQuotient=>.base (.pop (divideStack (.inr .quotient)) .done .clearQuotient .clearQuotient)
  | .done=>.base .halt
  | .addition pc=>SemiprimeD1StackMultiplierLink.instruction Sum.inl Label.addition (A.code pc)
  | .copy pc=>SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code pc)
  | .division pc=>SemiprimeD1StackValidationLink.instruction divideStack Label.division (D.code pc)
/-- Literal data-bank view; the nominal divider input is unused. -/
def store (addition : A.Stack→List Bool) (division : D.Stack→List Bool)
    (cached scratch : List Bool) : Stack→List Bool :=
  Sum.elim addition (Sum.elim division (fun b=>if b then scratch else cached))
/-- Original physical operands and raw cached modulus, with empty workspace. -/
def input (a b cached : List Bool) : Stack→List Bool :=
  store (A.store a b [] []) (D.payload [] [] [] [] [] [] [] [] [] [] []) cached []
/-- Concrete prepared-input source configuration. -/
def initial (a b cached : List Bool) : C.State Stack Label :=
  ⟨some .start,none,none,input a b cached,[]⟩
/-- Designated physically computed remainder. -/
def output : Stack := divideStack (.inr .remainder)
/-- Distinct physical division roles, including the shared acquired sum input. -/
theorem divideStack_injective : Function.Injective divideStack := by
  intro i j h
  rcases i with i|i <;> rcases j with j|j
  · simp_all [divideStack]
  · cases j <;> simp_all [divideStack]
  · cases i <;> simp_all [divideStack]
  · cases i <;> cases j <;> simp_all [divideStack]
/-- Cache, divisor destination and restoration scratch are distinct. -/
theorem copyStack_injective : Function.Injective copyStack := by decide
/-- Actual fixed finite machine with all arithmetic operands on physical stacks. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (.inl (.left : A.Stack)) output .start program
/-- Every stack alphabet, including real return labels, is finite. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite (.inl (.left : A.Stack)) output .start program
/-- No unbounded arithmetic operand occurs in control. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite (.inl (.left : A.Stack)) output .start program
/-- The literal data inventory is independent of every input size. -/
theorem stack_card : Fintype.card Stack=17 := by decide
end RiemannGaussian.SemiprimeD1StackResidueAdd
