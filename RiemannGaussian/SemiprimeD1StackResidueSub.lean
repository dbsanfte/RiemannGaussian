/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAdderExecution
import RiemannGaussian.SemiprimeD1StackSubtractorExecution
import RiemannGaussian.SemiprimeD1StackDividerExecution
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
import RiemannGaussian.SemiprimeD1StackPhysicalLoops
/-! # Actual general-modulus subtraction through x+M-y
All operands remain binary. The actual adder/subtractor results feed the actual
divider directly. Both physical modulus copies and the computed borrow-header
removal are literal instructions, with no residue or branch answer supplied.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackResidueSub
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace A
export SemiprimeD1StackAdder (Stack Label code store)
end A
namespace S
export SemiprimeD1StackAdder (Stack store)
export SemiprimeD1StackSubtractor (Label code)
end S
namespace D
export SemiprimeD1StackDivider (Stack Label code payload)
end D
/-- Twenty-one fixed Boolean data roles. -/
abbrev Stack := A.Stack⊕(S.Stack⊕(D.Stack⊕Bool))
/-- Binary modulus cache, physically retained. -/
def modulus : Stack := .inr (.inr (.inr false))
/-- Shared physical copy restoration workspace. -/
def copyTemporary : Stack := .inr (.inr (.inr true))
/-- The actual acquired x+M is the subtractor's literal left input. -/
def subtractStack : S.Stack→Stack
  | .left=>.inl .output
  | k=>.inr (.inl k)
/-- The actual subtraction output is the divider's literal input. -/
def divideStack : D.Stack→Stack
  | .inr .input=>.inr (.inl .output)
  | k=>.inr (.inr (.inl k))
/-- Two real cache copies: first to the adder, then to the divider. -/
def copyStack (division : Bool) (k : Fin 3) : Stack :=
  if k=0 then modulus else if k=1 then
    (if division then divideStack (.inr .divisor) else .inl .right) else copyTemporary
/-- Fixed included arithmetic, copy and outer-control locations. -/
inductive Label where
  | start | add | subtract | dropBorrow | copyDivisor | divide | clearQuotient | done
  | addition (pc : A.Label) | subtraction (pc : S.Label) | division (pc : D.Label)
  | copyAdder (pc : Fin 9) | copyDivision (pc : Fin 9)
  deriving DecidableEq,Fintype,Repr
/-- Closed literal pipeline, including both complete arithmetic operand factories. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.copyAdder 0) .add
  | .add=>.call (.addition (.start false)) .subtract
  | .subtract=>.call (.subtraction (.start false)) .dropBorrow
  | .dropBorrow=>.base (.pop (divideStack (.inr .input)) .copyDivisor .copyDivisor .copyDivisor)
  | .copyDivisor=>.call (.copyDivision 0) .divide
  | .divide=>.call (.division (.control .start)) .clearQuotient
  | .clearQuotient=>.base (.pop (divideStack (.inr .quotient)) .done .clearQuotient .clearQuotient)
  | .done=>.base .halt
  | .addition pc=>SemiprimeD1StackMultiplierLink.instruction Sum.inl Label.addition (A.code pc)
  | .subtraction pc=>SemiprimeD1StackMultiplierLink.instruction subtractStack Label.subtraction (S.code pc)
  | .division pc=>SemiprimeD1StackValidationLink.instruction divideStack Label.division (D.code pc)
  | .copyAdder pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack false) Label.copyAdder (SemiprimeD1StackCopy.code pc)
  | .copyDivision pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack true) Label.copyDivision (SemiprimeD1StackCopy.code pc)
/-- Literal staged payload. Nominal shared-source slots are physically unused. -/
def store (addition : A.Stack→List Bool) (subtraction : S.Stack→List Bool)
    (division : D.Stack→List Bool) (cached scratch : List Bool) : Stack→List Bool :=
  Sum.elim addition (Sum.elim subtraction (Sum.elim division (fun b=>if b then scratch else cached)))
/-- Only original operand/cache bytes are supplied; every work slot is empty. -/
def input (a b cached : List Bool) : Stack→List Bool :=
  store (A.store a [] [] []) (S.store [] b [] [])
    (D.payload [] [] [] [] [] [] [] [] [] [] []) cached []
/-- Actual prepared-input configuration. -/
def initial (a b cached : List Bool) : C.State Stack Label :=
  ⟨some .start,none,none,input a b cached,[]⟩
/-- The actual divider's remainder is the only arithmetic output. -/
def output : Stack := divideStack (.inr .remainder)
/-- Acquired sum input and subtraction scratch/output are disjoint. -/
theorem subtractStack_injective : Function.Injective subtractStack := by
  intro i j h
  cases i <;> cases j <;> simp_all [subtractStack]
/-- Shared subtraction-output/division-input and remaining divisor roles are disjoint. -/
theorem divideStack_injective : Function.Injective divideStack := by
  intro i j h
  rcases i with i|i <;> rcases j with j|j
  · simp_all [divideStack]
  · cases j <;> simp_all [divideStack]
  · cases i <;> simp_all [divideStack]
  · cases i <;> cases j <;> simp_all [divideStack]
/-- Both cache copies operate on distinct physical roles. -/
theorem copyStack_injective (b : Bool) : Function.Injective (copyStack b) := by
  cases b <;> decide
/-- Actual fixed finite machine for arbitrary binary operands. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (.inl (.left : A.Stack)) output .start program
/-- All stack alphabets, including actual return tags, are finite. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite (.inl (.left : A.Stack)) output .start program
/-- No arithmetic operand is carried in internal control. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite (.inl (.left : A.Stack)) output .start program
/-- Literal fixed physical data inventory. -/
theorem stack_card : Fintype.card Stack=21 := by decide
end RiemannGaussian.SemiprimeD1StackResidueSub
