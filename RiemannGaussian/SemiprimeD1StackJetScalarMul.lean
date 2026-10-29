/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackValidationLink
import RiemannGaussian.SemiprimeD1StackMultiplierExecution
import RiemannGaussian.SemiprimeD1StackProcedureTrace
import RiemannGaussian.SemiprimeD1StackReduceExecution

/-! # Actual canonical modular scalar multiplication
The real fixed multiplier is included as a nested-call procedure. Its binary
product is directly consumed by the real reducer using a copied precision cache.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackJetScalarMul
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace M
export SemiprimeD1StackMultiplier (Stack Label code payload input factor)
end M

/-- Eleven fixed Boolean data stacks, including cached precision and copy work. -/
abbrev Stack := M.Stack ⊕ Bool

/-- Actual reducer inclusion consumes the product accumulator directly. -/
def reduceStack : SemiprimeD1StackAdder.Stack → Stack
  | .left => .inl (.inl .right)
  | .right => .inl (.inl .left)
  | .scratch => .inl (.inl .scratch)
  | .output => .inl (.inl .output)

/-- Precision is physically copied into the reducer counter input. -/
def copyStack (k : Fin 3) : Stack :=
  if k=0 then .inr false else if k=1 then reduceStack .right else .inr true

/-- Distinct literal reducer operands. -/
theorem reduceStack_injective : Function.Injective reduceStack := by decide

/-- Distinct literal precision-copy operands. -/
theorem copyStack_injective : Function.Injective copyStack := by decide

/-- Fixed calls and finite component labels, independent of all input lengths/values. -/
inductive Label where
  | start | copyPrecision | callReduce | done
  | multiply (pc : M.Label)
  | copy (pc : Fin 9)
  | reduce (pc : SemiprimeD1StackReduce.Label)
  deriving DecidableEq,Fintype,Repr

/-- Actual fixed multiplier/copy/reducer caller with real nested return frames. -/
def program : Label → C.Instruction Stack Label
  | .start => .call (.multiply (.control .start)) .copyPrecision
  | .copyPrecision => .call (.copy 0) .callReduce
  | .callReduce => .call (.reduce .take) .done
  | .done => .base .halt
  | .multiply pc => SemiprimeD1StackValidationLink.instruction Sum.inl Label.multiply (M.code pc)
  | .copy pc => SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code pc)
  | .reduce pc => SemiprimeD1StackMultiplierLink.instruction reduceStack Label.reduce (SemiprimeD1StackReduce.code pc)

/-- Literal multiplier input/work/result bank and retained physical precision cache. -/
def store (xs ys ds left acc scratch output cp cs width work : List Bool) : Stack → List Bool
  | .inl k => M.payload xs ys ds left acc scratch output cp cs k
  | .inr false => width
  | .inr true => work

/-- Actual concrete source configuration, without preloaded return-frame advice. -/
def state (pc : Option Label) (flag : Option Bool) (returned : Option Label)
    (xs ys ds left acc scratch output cp cs width work : List Bool) : C.State Stack Label :=
  ⟨pc,flag,returned,store xs ys ds left acc scratch output cp cs width work,[]⟩

/-- Actual fixed finite-stack machine; original coefficients and precision are physical payload. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine
  (Sum.inl M.input) (reduceStack .output) Label.start program

end RiemannGaussian.SemiprimeD1StackJetScalarMul
