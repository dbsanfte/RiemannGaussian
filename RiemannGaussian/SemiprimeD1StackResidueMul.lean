/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMultiplierExecution
import RiemannGaussian.SemiprimeD1StackDividerExecution
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
import RiemannGaussian.SemiprimeD1StackPhysicalLoops

/-! # Actual general-modulus multiplication for the public checker
The real multiplier's accumulator is directly the real divider's input. A real
copy preserves the cached binary modulus; the physical quotient is erased.
No power/modulo/product oracle occurs in the fixed instruction table.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackResidueMul
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace M
export SemiprimeD1StackMultiplier (Stack Label code payload input factor)
end M
namespace D
export SemiprimeD1StackDivider (Stack Label code payload)
end D

/-- Twenty-two fixed Boolean data roles, including the retained modulus. -/
abbrev Stack := M.Stack⊕(D.Stack⊕Bool)
/-- The binary modulus cache is a physical word, never a control value. -/
def modulus : Stack := .inr (.inr false)
/-- Literal real copy-restoration scratch. -/
def copyTemporary : Stack := .inr (.inr true)
/-- Direct product-to-divider data path; all other division roles are separate. -/
def divideStack : D.Stack→Stack
  | .inr .input => .inl (.inl .right)
  | k => .inr (.inl k)
/-- Actual divisor copy operands. -/
def copyStack (k : Fin 3) : Stack :=
  if k=0 then modulus else if k=1 then divideStack (.inr .divisor) else copyTemporary

/-- Fixed nested component and local pipeline labels. -/
inductive Label where
  | start | copyModulus | divide | clearQuotient | done
  | multiply (pc : M.Label) | copy (pc : Fin 9) | division (pc : D.Label)
  deriving DecidableEq,Fintype,Repr

/-- One fixed literal program, including BOTH complete arithmetic machines. -/
def program : Label→C.Instruction Stack Label
  | .start => .call (.multiply (.control .start)) .copyModulus
  | .copyModulus => .call (.copy 0) .divide
  | .divide => .call (.division (.control .start)) .clearQuotient
  | .clearQuotient => .base (.pop (divideStack (.inr .quotient)) .done .clearQuotient .clearQuotient)
  | .done => .base .halt
  | .multiply pc => SemiprimeD1StackValidationLink.instruction Sum.inl Label.multiply (M.code pc)
  | .copy pc => SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code pc)
  | .division pc => SemiprimeD1StackValidationLink.instruction divideStack Label.division (D.code pc)

/-- Exact physical payload view. The divider's unused nominal input stays empty. -/
def store (multiply : M.Stack→List Bool) (division : D.Stack→List Bool)
    (cached scratch : List Bool) : Stack→List Bool :=
  Sum.elim multiply (Sum.elim division (fun b=>if b then scratch else cached))
/-- Initial actual operands and binary cached modulus; every work cell is empty. -/
def input (a b cached : List Bool) : Stack→List Bool :=
  store (M.payload a b [] [] [] [] [] [] []) (D.payload [] [] [] [] [] [] [] [] [] [] []) cached []
/-- Concrete source state for this macro entry. Operand acquisition is the caller's task. -/
def initial (a b cached : List Bool) : C.State Stack Label :=
  ⟨some .start,none,none,input a b cached,[]⟩
/-- The computed residue output is the actual divider's remainder word. -/
def output : Stack := divideStack (.inr .remainder)
/-- All shared and separate division roles are distinct. -/
theorem divideStack_injective : Function.Injective divideStack := by
  intro i j h
  rcases i with i|i <;> rcases j with j|j
  · simp_all [divideStack]
  · cases j <;> simp_all [divideStack]
  · cases i <;> simp_all [divideStack]
  · cases i <;> cases j <;> simp_all [divideStack]
/-- Modulus, divisor destination and copy scratch are distinct physical stacks. -/
theorem copyStack_injective : Function.Injective copyStack := by decide
/-- A fixed actual finite machine, with the remainder as its output designation. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (.inl M.input) output .start program
/-- All data and return-tag alphabets are finite before the operands. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite (.inl M.input) output .start program
/-- No arithmetic value is stored in transient machine control. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite (.inl M.input) output .start program
/-- The literal stack inventory is independent of the binary operand lengths. -/
theorem stack_card : Fintype.card Stack=22 := by decide

end RiemannGaussian.SemiprimeD1StackResidueMul
