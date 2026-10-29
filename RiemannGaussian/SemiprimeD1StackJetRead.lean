/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProcedureTrace
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
import RiemannGaussian.SemiprimeD1TensorTapeCodec
import RiemannGaussian.SemiprimeD1JetRingBits

/-! # Physical cached coefficient-vector lookup
A real copy preserves the encoded cache. A physical unary index drives actual
field parses and clears. Coefficient payload is always binary; no getter opcode
or selected-word supplier occurs in the fixed program.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackJetRead
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active initial framed_run)
end Field

/-- Eight literal Boolean stacks; the index word's physical length is its index. -/
inductive Stack where
  | cache | reader | index | parser | skipped | output | valid | copy
  deriving DecidableEq,Repr

/-- Constant stack enumeration before every vector and index input. -/
instance : Fintype Stack := Fintype.ofList [.cache,.reader,.index,.parser,.skipped,.output,.valid,.copy]
  (by intro k; cases k <;> simp)

/-- Literal cache-copy mapping. -/
def copyStack (k : Fin 3) : Stack := if k=0 then .cache else if k=1 then .reader else .copy

/-- Literal field-parser instance; skipped words are actually materialized then cleared. -/
def fieldStack (skip : Bool) : Field.Stack → Stack
  | .inl .input => .reader
  | .inl .scratch => .parser
  | .inl .output => if skip then .skipped else .output
  | .inr _ => .valid

/-- Distinct actual copy stacks. -/
theorem copyStack_injective : Function.Injective copyStack := by decide

/-- Distinct actual parser stacks. -/
theorem fieldStack_injective (skip : Bool) : Function.Injective (fieldStack skip) := by
  intro i j h
  cases skip <;> rcases i with i|i <;> rcases j with j|j <;>
    cases i <;> cases j <;> simp_all [fieldStack]

/-- Fixed physical index/control and literal procedure labels. -/
inductive Label where
  | start | loop | skipTag | selectTag | callSkip | skipParsed | clearSkipped
  | callTake | takeParsed | clearInput | clearIndex | done | abort
  | copy (pc : Fin 9)
  | field (skip : Bool) (pc : Field.Label)
  deriving DecidableEq,Fintype,Repr

/-- Complete fixed lookup code; only actual stack cells decide the branches. -/
def program : Label → C.Instruction Stack Label
  | .start => .call (.copy 0) .loop
  | .loop => .base (.pop .index .selectTag .skipTag .skipTag)
  | .skipTag => .base (.pop .reader .clearIndex .clearInput .callSkip)
  | .selectTag => .base (.pop .reader .clearIndex .clearInput .callTake)
  | .callSkip => .call (.field true (Field.active .tagPop (none,false))) .skipParsed
  | .skipParsed => .base (.pop .valid .abort .abort .clearSkipped)
  | .clearSkipped => .base (.pop .skipped .loop .clearSkipped .clearSkipped)
  | .callTake => .call (.field false (Field.active .tagPop (none,false))) .takeParsed
  | .takeParsed => .base (.pop .valid .abort .abort .clearInput)
  | .clearInput => .base (.pop .reader .clearIndex .clearInput .clearInput)
  | .clearIndex => .base (.pop .index .done .clearIndex .clearIndex)
  | .done | .abort => .base .halt
  | .copy pc => SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code pc)
  | .field skip pc => SemiprimeD1StackMultiplierLink.instruction (fieldStack skip) (Label.field skip) (Field.code pc)

/-- Actual cache, query, binary payload and workspace. -/
def store (cache reader index parser skipped output valid copy : List Bool) : Stack → List Bool
  | .cache => cache
  | .reader => reader
  | .index => index
  | .parser => parser
  | .skipped => skipped
  | .output => output
  | .valid => valid
  | .copy => copy

/-- Actual source configuration with empty real return frames. -/
def state (pc : Option Label) (flag : Option Bool) (returned : Option Label)
    (cache reader index parser skipped output valid copy : List Bool) : C.State Stack Label :=
  ⟨pc,flag,returned,store cache reader index parser skipped output valid copy,[]⟩

/-- Actual finite-stack machine; a caller provides the physical unary query index. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine Stack.cache Stack.output Label.start program

end RiemannGaussian.SemiprimeD1StackJetRead
