/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProcedureTrace
import RiemannGaussian.SemiprimeD1StackCopy
import RiemannGaussian.SemiprimeD1StackReduceExecution

/-! # Physical streaming digit block
This program acquires one canonical low block while RETAINING the high input
tail. A real Copy supplies the disposable width markers. A real included trim
procedure canonicalizes the collected bits; the retained input and cached width
are unmapped auxiliary payload and cannot be silently cleared by that call.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackDigitBlock
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C

/-- Fixed data stacks; the two dummy stacks isolate the trim-only procedure entry. -/
inductive Stack where
  | input | width | counter | scratch | temporary | dummyLeft | dummyRight | output
  deriving DecidableEq,Repr

/-- Explicit finite stack catalogue, fixed before all inputs. -/
instance : Fintype Stack := Fintype.ofList
  [.input,.width,.counter,.scratch,.temporary,.dummyLeft,.dummyRight,.output]
  (by intro k;cases k <;> simp)

/-- Actual local control and literal Copy/trim procedure labels. -/
inductive Label where
  | start | take | read | save (bit : Bool) | clearCounter | trimCall | done
  | copy (label : Fin 9)
  | trim (label : SemiprimeD1StackReduce.Label)
  deriving DecidableEq,Fintype,Repr

/-- Real persistent-width copying. -/
def copyStack : Fin 3→Stack := fun k=>if k=0 then .width else if k=1 then .counter else .temporary

/-- The included trim call cannot touch the retained high input or cached width. -/
def trimStack : SemiprimeD1StackAdder.Stack→Stack
  | .left => .dummyLeft
  | .right => .dummyRight
  | .scratch => .scratch
  | .output => .output

/-- The complete fixed table, with no natural-value or arbitrary-function opcode. -/
def program : Label→C.Instruction Stack Label
  | .start => .call (.copy 0) .take
  | .take => .base (.pop .counter .trimCall .read .read)
  | .read => .base (.pop .input .clearCounter (.save false) (.save true))
  | .save b => .base (.push .scratch b .take)
  | .clearCounter => .base (.pop .counter .trimCall .clearCounter .clearCounter)
  | .trimCall => .call (.trim .trim) .done
  | .done => .base .halt
  | .copy l => SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code l)
  | .trim l => SemiprimeD1StackMultiplierLink.instruction trimStack Label.trim (SemiprimeD1StackReduce.code l)

/-- Literal physical payload, including retained input and cached precision width. -/
def store (input width counter scratch temporary dummyLeft dummyRight output : List Bool) : Stack→List Bool
  | .input => input
  | .width => width
  | .counter => counter
  | .scratch => scratch
  | .temporary => temporary
  | .dummyLeft => dummyLeft
  | .dummyRight => dummyRight
  | .output => output

/-- Copy has no alias among its source/restoration/output stacks. -/
theorem copyStack_injective : Function.Injective copyStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [copyStack]

/-- The trim source is included without any aliased data stacks. -/
theorem trimStack_injective : Function.Injective trimStack := by
  intro i j h
  cases i <;> cases j <;> simp_all [trimStack]

/-- Fixed actual finite procedure machine. Width is an explicit physical caller input. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine Stack.input Stack.output .start program

/-- Every physical alphabet, including return continuations, is finite. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite Stack.input Stack.output Label.start program

/-- All internal control is finite; raw input/counters are physical stack data. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite Stack.input Stack.output Label.start program

end RiemannGaussian.SemiprimeD1StackDigitBlock
