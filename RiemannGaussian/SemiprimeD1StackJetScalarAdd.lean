/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProcedureTrace
import RiemannGaussian.SemiprimeD1StackAdderExecution
import RiemannGaussian.SemiprimeD1StackReduceExecution

/-! # Actual modular jet scalar addition
Two binary words and one cached physical precision counter occupy fixed stacks.
Real adder/copy/reducer calls compute the exact canonical old scalar bytes.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackJetScalarAdd
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C

/-- Six fixed Boolean data stacks; the Boolean auxiliary tags are precision/work. -/
abbrev Stack := SemiprimeD1StackAdder.Stack ⊕ Bool

/-- Constant controller, actual adder/copy/reducer procedures, and finite bit flags. -/
inductive Label where
  | start | move | movePush (bit : Bool) | restore | restorePush (bit : Bool)
  | copyPrecision | callReduce | done
  | adder (pc : SemiprimeD1StackAdder.Label)
  | copy (pc : Fin 9)
  | reduce (pc : SemiprimeD1StackReduce.Label)
  deriving DecidableEq,Fintype,Repr

/-- Literal precision-copy inclusion; precision cache is retained, not reconstructed. -/
def copyStack (k : Fin 3) : Stack :=
  if k=0 then .inr false else if k=1 then .inl .right else .inr true

/-- The included copy really has three distinct operand stacks. -/
theorem copyStack_injective : Function.Injective copyStack := by decide

/-- Fixed program, with every procedure invocation represented by real calls/returns. -/
def program : Label → C.Instruction Stack Label
  | .start => .call (.adder (.start false)) .move
  | .move => .base (.pop (.inl .output) .restore (.movePush false) (.movePush true))
  | .movePush bit => .base (.push (.inl .scratch) bit .move)
  | .restore => .base (.pop (.inl .scratch) .copyPrecision (.restorePush false) (.restorePush true))
  | .restorePush bit => .base (.push (.inl .left) bit .restore)
  | .copyPrecision => .call (.copy 0) .callReduce
  | .callReduce => .call (.reduce .take) .done
  | .done => .base .halt
  | .adder pc => SemiprimeD1StackMultiplierLink.instruction Sum.inl Label.adder (SemiprimeD1StackAdder.code pc)
  | .copy pc => SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code pc)
  | .reduce pc => SemiprimeD1StackMultiplierLink.instruction Sum.inl Label.reduce (SemiprimeD1StackReduce.code pc)

/-- Literal binary operands/work/result and physical precision-cache payload. -/
def store (left right scratch output precision work : List Bool) : Stack → List Bool
  | .inl .left => left
  | .inl .right => right
  | .inl .scratch => scratch
  | .inl .output => output
  | .inr false => precision
  | .inr true => work

/-- Concrete data-only source configuration with empty actual return frames. -/
def state (pc : Option Label) (flag : Option Bool) (returned : Option Label)
    (left right scratch output precision work : List Bool) : C.State Stack Label :=
  ⟨pc,flag,returned,store left right scratch output precision work,[]⟩

/-- Actual fixed finite-stack scalar-adder machine; precision remains a declared cache. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine
  (Sum.inl .left) (Sum.inl .output) Label.start program

end RiemannGaussian.SemiprimeD1StackJetScalarAdd
