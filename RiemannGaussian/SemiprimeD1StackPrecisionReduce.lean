/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProcedureTrace
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
import RiemannGaussian.SemiprimeD1StackUnaryCounterExecution
import RiemannGaussian.SemiprimeD1StackReduceExecution

/-! # One fixed parser/counter/reducer program
The input is two physically framed binary words: scalar then precision. Two
actual field parses acquire both, an actual binary-to-unary loop acquires the
precision counter, and the reducer consumes it. No prepared counter or scalar
result is supplied to the running program.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPrecisionReduce
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code initial framed_run active)
end Field
namespace Unary
export SemiprimeD1StackUnaryCounter (Label code state)
end Unary
namespace Reduce
export SemiprimeD1StackReduce (Label code state)
end Reduce
open SemiprimeD1StackProcedureTrace

/-- Eight literal Boolean stack names, independent of all input lengths. -/
inductive Stack where
  | input | word | precision | width | work | temporary | result | valid
  deriving DecidableEq,Repr

/-- Explicit constant stack catalogue. -/
instance : Fintype Stack := Fintype.ofList
  [.input,.word,.precision,.width,.work,.temporary,.result,.valid] (by intro k;cases k <;> simp)

/-- Fixed control plus four literal procedure instances. -/
inductive Label where
  | start | wordValid | precisionCall | precisionValid | counterCall | counterDone | done
  | field (precision : Bool) (label : Field.Label)
  | unary (label : Unary.Label)
  | reduce (label : Reduce.Label)
  deriving DecidableEq,Fintype,Repr

/-- Literal field instance map; the second parse targets the precision stack. -/
def fieldStack (precision : Bool) : Field.Stack→Stack
  | .inl .input => .input
  | .inl .scratch => .work
  | .inl .output => if precision then .precision else .word
  | .inr _ => .valid

/-- Actual binary precision conversion uses its own physical reversal stack. -/
def unaryStack : SemiprimeD1StackAdder.Stack→Stack
  | .left => .precision
  | .right => .temporary
  | .scratch => .work
  | .output => .width

/-- Actual scalar reduction consumes the acquired word and marker counter. -/
def reduceStack : SemiprimeD1StackAdder.Stack→Stack
  | .left => .word
  | .right => .width
  | .scratch => .work
  | .output => .result

/-- The complete finite procedure table; a component halt is a real return. -/
def program : Label→C.Instruction Stack Label
  | .start => .call (.field false (Field.active .tagPop (none,false))) .wordValid
  | .wordValid => .base (.pop .valid .done .done .precisionCall)
  | .precisionCall => .call (.field true (Field.active .tagPop (none,false))) .precisionValid
  | .precisionValid => .base (.pop .valid .done .done .counterCall)
  | .counterCall => .call (.unary .reverse) .counterDone
  | .counterDone => .call (.reduce .take) .done
  | .done => .base .halt
  | .field p l => SemiprimeD1StackMultiplierLink.instruction (fieldStack p) (Label.field p) (Field.code l)
  | .unary l => SemiprimeD1StackMultiplierLink.instruction unaryStack Label.unary (Unary.code l)
  | .reduce l => SemiprimeD1StackMultiplierLink.instruction reduceStack Label.reduce (Reduce.code l)

/-- Literal eight-stack data bank. -/
def store (input word precision width work temporary result valid : List Bool) : Stack→List Bool
  | .input => input
  | .word => word
  | .precision => precision
  | .width => width
  | .work => work
  | .temporary => temporary
  | .result => result
  | .valid => valid

/-- Every source field cell has a distinct actual destination. -/
theorem fieldStack_injective (p : Bool) : Function.Injective (fieldStack p) := by
  intro i j h
  cases p <;> rcases i with i|i <;> rcases j with j|j <;>
    cases i <;> cases j <;> simp_all [fieldStack]

/-- Unary conversion uses four distinct physical stacks. -/
theorem unaryStack_injective : Function.Injective unaryStack := by
  intro i j h
  cases i <;> cases j <;> simp_all [unaryStack]

/-- Reduction uses four distinct physical stacks. -/
theorem reduceStack_injective : Function.Injective reduceStack := by
  intro i j h
  cases i <;> cases j <;> simp_all [reduceStack]

/-- One actual fixed finite procedure machine, with only the framed input loaded. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine Stack.input Stack.result Label.start program

/-- All eight Boolean data alphabets and the finite return-label alphabet are finite. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite Stack.input Stack.result Label.start program

/-- No unbounded data inhabit finite internal control. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite Stack.input Stack.result Label.start program

end RiemannGaussian.SemiprimeD1StackPrecisionReduce
