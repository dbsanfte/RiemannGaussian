/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProcedureTrace
import RiemannGaussian.SemiprimeD1StackCopy
import RiemannGaussian.SemiprimeD1StackReduceExecution

/-! # Physical radix-digit acquisition from the original binary integer
The integer always stays binary. Width and digit index are physical counters.
Each index marker triggers an actual width-counter copy and width-many input
pops. The final copied counter drives canonical low-prefix reduction. Neither
the product offset nor a power/division result is supplied to the machine.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackRadixDigit
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C

/-- Six fixed Boolean data stacks; large numeric input stays on input as binary. -/
inductive Stack where
  | input | width | index | temporary | copied | output
  deriving DecidableEq,Repr

/-- Explicit finite catalogue, fixed before all input values. -/
instance : Fintype Stack := Fintype.ofList [.input,.width,.index,.temporary,.copied,.output]
  (by intro k;cases k <;> simp)

/-- Literal control, Copy instance and canonical reducer instance. -/
inductive Label where
  | start | blockCopy | skip | dropBit | finalCopy | reduceCall | clearWidth | done
  | copy (label : Fin 9)
  | reduce (label : SemiprimeD1StackReduce.Label)
  deriving DecidableEq,Fintype,Repr

/-- Persistent width is copied by a real three-stack procedure. -/
def copyStack : Fin 3→Stack := fun k=>if k=0 then .width else if k=1 then .copied else .temporary

/-- The final reduction consumes remaining binary input and a copied width. -/
def reduceStack : SemiprimeD1StackAdder.Stack→Stack
  | .left => .input
  | .right => .copied
  | .scratch => .temporary
  | .output => .output

/-- Fixed actual program. A missing input bit is physically read as EOF. -/
def program : Label→C.Instruction Stack Label
  | .start => .base (.pop .index .finalCopy .blockCopy .blockCopy)
  | .blockCopy => .call (.copy 0) .skip
  | .skip => .base (.pop .copied .start .dropBit .dropBit)
  | .dropBit => .base (.pop .input .skip .skip .skip)
  | .finalCopy => .call (.copy 0) .reduceCall
  | .reduceCall => .call (.reduce .take) .clearWidth
  | .clearWidth => .base (.pop .width .done .clearWidth .clearWidth)
  | .done => .base .halt
  | .copy l => SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code l)
  | .reduce l => SemiprimeD1StackMultiplierLink.instruction reduceStack Label.reduce (SemiprimeD1StackReduce.code l)

/-- Every payload is a literal Boolean stack, never an unbounded control field. -/
def store (input width index temporary copied output : List Bool) : Stack→List Bool
  | .input => input
  | .width => width
  | .index => index
  | .temporary => temporary
  | .copied => copied
  | .output => output

/-- Copy inclusion maps all component stacks injectively. -/
theorem copyStack_injective : Function.Injective copyStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [copyStack]

/-- Reduction uses four separate physical stacks. -/
theorem reduceStack_injective : Function.Injective reduceStack := by
  intro i j h
  cases i <;> cases j <;> simp_all [reduceStack]

/-- One actual fixed finite machine. The caller physically supplies width and
index counters; this is not yet a whole original-input preprocessing claim. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine Stack.input Stack.output .start program

/-- Every data and return alphabet is finite before all inputs. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite Stack.input Stack.output Label.start program

/-- Native unbounded input/offset values are absent from finite control. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite Stack.input Stack.output Label.start program

end RiemannGaussian.SemiprimeD1StackRadixDigit
