/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDigitCount
import RiemannGaussian.SemiprimeD1StackUnaryCounterExecution
import RiemannGaussian.SemiprimeD1StackAssignmentBody

/-! # Actual binary occurrence-ID vector to unary port tape
Every vector record is parsed, including the empty binary word. The actual
binary-to-unary procedure runs once per record; a physical reverse log restores
record order. Only bounded ordinal metadata becomes unary.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortOrdinalStream
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active initial)
end Field
namespace Unary
export SemiprimeD1StackUnaryCounter (Label code)
end Unary
namespace Body
export SemiprimeD1StackAssignmentBody (Stack Label code entry)
end Body
/-- Twelve fixed Boolean data roles; no decoded ordinal is in control. -/
inductive Stack where
  | bank | reader | word | fieldScratch | valid | copyScratch
  | digits | unaryScratch | unary | logScratch | history | output
  deriving DecidableEq,Repr
instance : Fintype Stack where
  elems := {.bank,.reader,.word,.fieldScratch,.valid,.copyScratch,.digits,.unaryScratch,.unary,.logScratch,.history,.output}
  complete := by intro k;cases k <;> simp
/-- Finite physical loop and reversal phases. -/
inductive Control where
  | start | next | parse | clearValid | convert | log | clearUnary
  | finish | reverse | emit (b:Bool) | done
  deriving DecidableEq,Fintype,Repr
/-- Literal component program locations, all fixed before input. -/
inductive Label where
  | control (pc:Control) | copy (pc:Fin 9) | field (pc:Field.Label)
  | unary (pc:Unary.Label) | body (pc:Body.Label)
  deriving Fintype
/-- Preserving original vector copy. -/
def copyStack (k:Fin 3) : Stack := if k=0 then .bank else if k=1 then .reader else .copyScratch
/-- Physical field parser roles. -/
def fieldStack : Field.Stack→Stack
  | .inl .input => .reader | .inl .scratch => .fieldScratch
  | .inl .output => .word | .inr _ => .valid
/-- The four real unary-counter operands. -/
def unaryStack : SemiprimeD1StackAdder.Stack→Stack
  | .left => .word | .right => .digits | .scratch => .unaryScratch | .output => .unary
/-- Actual reverse-frame logger operands. -/
def bodyStack : Body.Stack→Stack
  | .word => .unary | .scratch => .logScratch | .history => .history
local notation "ctl" => Label.control
/-- Closed source program: no count, route, decoded-ID or unary-answer supplier. -/
def program : Label→C.Instruction Stack Label
  | .control .start => .call (.copy 0) (ctl .next)
  | .control .next => .base (.pop .reader (ctl .finish) (ctl .finish) (ctl .parse))
  | .control .parse => .call (.field (Field.active .tagPop (none,false))) (ctl .clearValid)
  | .control .clearValid => .base (.pop .valid (ctl .convert) (ctl .convert) (ctl .convert))
  | .control .convert => .call (.unary .reverse) (ctl .log)
  | .control .log => .call (.body Body.entry) (ctl .clearUnary)
  | .control .clearUnary => .base (.pop .unary (ctl .next) (ctl .clearUnary) (ctl .clearUnary))
  | .control .finish => .base (.push .output false (ctl .reverse))
  | .control .reverse => .base (.pop .history (ctl .done) (ctl (.emit false)) (ctl (.emit true)))
  | .control (.emit b) => .base (.push .output b (ctl .reverse))
  | .control .done => .base .halt
  | .copy pc => SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy
      (SemiprimeD1StackCopy.code pc)
  | .field pc => SemiprimeD1StackMultiplierLink.instruction fieldStack Label.field (Field.code pc)
  | .unary pc => SemiprimeD1StackMultiplierLink.instruction unaryStack Label.unary (Unary.code pc)
  | .body pc => SemiprimeD1StackMultiplierLink.instruction bodyStack Label.body (Body.code pc)
/-- Exact intended port tape; this is a specification, never an instruction. -/
def result (words:List (List Bool)) : List Bool :=
  SemiprimeD1TensorTapeCodec.vectorBits
    (words.map fun w=>List.replicate (SemiprimeBitArithmetic.bitValue w) true)
/-- Data-only initial cache; no cardinality header enters. -/
def initial (bank:List Bool) : C.State Stack Label :=
  ⟨some (ctl .start),none,none,(fun k=>if k=.bank then bank else []),[]⟩
/-- Genuine finite Boolean-stack machine. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine Stack.bank Stack.output (ctl .start) program
/-- Twelve physical data roles are all included in prefix accounting. -/
theorem stack_card : Fintype.card Stack=12 := by decide
/-- Original cache copy has no aliased operand. -/
theorem copyStack_injective : Function.Injective copyStack := by decide
/-- Actual parser operands are distinct. -/
theorem fieldStack_injective : Function.Injective fieldStack := by decide
/-- Actual unary conversion operands are distinct. -/
theorem unaryStack_injective : Function.Injective unaryStack := by decide
/-- Actual logger operands are distinct. -/
theorem bodyStack_injective : Function.Injective bodyStack := by decide
end RiemannGaussian.SemiprimeD1StackPortOrdinalStream
