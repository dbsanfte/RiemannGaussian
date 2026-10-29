/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetScalarAddExecution
import RiemannGaussian.SemiprimeD1StackValidationLink
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
import RiemannGaussian.SemiprimeD1TensorTapeCodec
import RiemannGaussian.SemiprimeD1JetRingBits

/-! # Actual dense jet-vector addition
Two tagged coefficient tapes are read by actual field calls. A physical rank
counter drives the loop; every binary modular sum and output frame is executed.
Context precision/rank acquisition is an explicit outer interface.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackJetAdd
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace S
export SemiprimeD1StackJetScalarAdd (Stack Label program store)
end S
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active initial framed_run)
end Field

/-- Nine fixed vector/control stacks outside the six scalar arithmetic stacks. -/
inductive Aux where
  | leftTape | rightTape | rank | active | reverseOut | output | valid | parser | copy
  deriving DecidableEq,Repr

/-- Literal constant vector-stack catalogue. -/
instance : Fintype Aux := Fintype.ofList [.leftTape,.rightTape,.rank,.active,.reverseOut,.output,.valid,.parser,.copy]
  (by intro k; cases k <;> simp)

/-- Fifteen fixed Boolean data stacks. -/
abbrev Stack := S.Stack ⊕ Aux

/-- Literal field input/work/output/valid inclusion for each input stream. -/
def fieldStack (right : Bool) : Field.Stack → Stack
  | .inl .input => .inr (if right then .rightTape else .leftTape)
  | .inl .scratch => .inr .parser
  | .inl .output => .inl (.inl (if right then .right else .left))
  | .inr _ => .inr .valid

/-- Rank acquisition is a real copy from its cached physical counter. -/
def copyStack (k : Fin 3) : Stack :=
  if k=0 then .inr .rank else if k=1 then .inr .active else .inr .copy

/-- All parser destinations are actual distinct stack cells. -/
theorem fieldStack_injective (right : Bool) : Function.Injective (fieldStack right) := by
  intro i j h
  cases right <;> rcases i with i|i <;> rcases j with j|j <;>
    cases i <;> cases j <;> simp_all [fieldStack]

/-- The rank copy uses distinct physical input, result and work stacks. -/
theorem copyStack_injective : Function.Injective copyStack := by decide

/-- Fixed labels contain only individual binary flags, never rank or coefficient lists. -/
inductive Label where
  | start | loop | readLeft | leftTag | callLeft | leftParsed
  | readRight | rightTag | callRight | rightParsed | callScalar
  | emitTag | emitWord | emitPrefix (bit : Bool) | emitData (bit : Bool) | endWord
  | endVector | clearLeft | clearRight | reverse | pushOutput (bit : Bool) | done | abort
  | copy (pc : Fin 9)
  | field (right : Bool) (pc : Field.Label)
  | scalar (pc : S.Label)
  deriving DecidableEq,Fintype,Repr

/-- Actual constant vector-addition program, with literal nested component inclusion. -/
def program : Label → C.Instruction Stack Label
  | .start => .call (.copy 0) .loop
  | .loop => .base (.pop (.inr .active) .endVector .readLeft .readLeft)
  | .readLeft => .base (.peek (.inr .leftTape) .readRight .readRight .leftTag)
  | .leftTag => .base (.pop (.inr .leftTape) .callLeft .callLeft .callLeft)
  | .callLeft => .call (.field false (Field.active .tagPop (none,false))) .leftParsed
  | .leftParsed => .base (.pop (.inr .valid) .abort .abort .readRight)
  | .readRight => .base (.peek (.inr .rightTape) .callScalar .callScalar .rightTag)
  | .rightTag => .base (.pop (.inr .rightTape) .callRight .callRight .callRight)
  | .callRight => .call (.field true (Field.active .tagPop (none,false))) .rightParsed
  | .rightParsed => .base (.pop (.inr .valid) .abort .abort .callScalar)
  | .callScalar => .call (.scalar .start) .emitTag
  | .emitTag => .base (.push (.inr .reverseOut) true .emitWord)
  | .emitWord => .base (.pop (.inl (.inl .output)) .endWord (.emitPrefix false) (.emitPrefix true))
  | .emitPrefix bit => .base (.push (.inr .reverseOut) true (.emitData bit))
  | .emitData bit => .base (.push (.inr .reverseOut) bit .emitWord)
  | .endWord => .base (.push (.inr .reverseOut) false .loop)
  | .endVector => .base (.push (.inr .reverseOut) false .clearLeft)
  | .clearLeft => .base (.pop (.inr .leftTape) .clearRight .clearLeft .clearLeft)
  | .clearRight => .base (.pop (.inr .rightTape) .reverse .clearRight .clearRight)
  | .reverse => .base (.pop (.inr .reverseOut) .done (.pushOutput false) (.pushOutput true))
  | .pushOutput bit => .base (.push (.inr .output) bit .reverse)
  | .done | .abort => .base .halt
  | .copy pc => SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code pc)
  | .field right pc => SemiprimeD1StackMultiplierLink.instruction (fieldStack right) (Label.field right) (Field.code pc)
  | .scalar pc => SemiprimeD1StackValidationLink.instruction Sum.inl Label.scalar (S.program pc)

/-- Literal scalar cells, coefficient streams, metadata caches, and real output/workspace. -/
def store (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy : List Bool) : Stack → List Bool
  | .inl k => S.store left right scratch scalar precision scalarWork k
  | .inr .leftTape => a
  | .inr .rightTape => b
  | .inr .rank => rank
  | .inr .active => active
  | .inr .reverseOut => rev
  | .inr .output => output
  | .inr .valid => valid
  | .inr .parser => parser
  | .inr .copy => copy

/-- Concrete actual source state; no hidden continuation frames are supplied. -/
def state (pc : Option Label) (flag : Option Bool) (returned : Option Label)
    (left right scratch scalar precision scalarWork a b rank active rev output valid parser copy : List Bool) : C.State Stack Label :=
  ⟨pc,flag,returned,store left right scratch scalar precision scalarWork a b rank active rev output valid parser copy,[]⟩

/-- Actual fixed dense-vector machine, with preserved context caches as declared data. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (.inr .leftTape) (.inr .output) Label.start program

end RiemannGaussian.SemiprimeD1StackJetAdd
