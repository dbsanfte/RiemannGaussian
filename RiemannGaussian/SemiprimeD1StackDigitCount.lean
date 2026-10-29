/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
import RiemannGaussian.SemiprimeD1StackProcedureFragments

/-! # Actual cached digit-vector record counting
The actual vector is physically copied, every field is parsed by the real
finite parser, and one unary marker is pushed per record. Empty zero-valued
digit fields are counted, not skipped. This is an internal cache primitive;
the original-input graph caller must acquire the cache, not supply a count.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackDigitCount
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active initial)
end Field
namespace Link
export SemiprimeD1StackMultiplierLink (instruction DataRel data_unique Rel run_rel)
end Link
/-- Seven fixed Boolean roles for immutable cache, parsing, and actual count. -/
inductive Stack where
  | bank | reader | count | word | fieldScratch | valid | copyScratch
  deriving DecidableEq,Repr
instance : Fintype Stack where
  elems:={.bank,.reader,.count,.word,.fieldScratch,.valid,.copyScratch}
  complete:=by intro k;cases k <;> simp
/-- Static finite count-loop labels. -/
inductive Local where
  | main | popVector | fieldCall | clearWord | popValid | pushCount | halt
  deriving DecidableEq,Repr
instance : Fintype Local where
  elems:={.main,.popVector,.fieldCall,.clearWord,.popValid,.pushCount,.halt}
  complete:=by intro pc;cases pc <;> simp
/-- All literal count, Copy and parser labels are fixed before the cache. -/
abbrev Label := Local⊕(Fin 9⊕Field.Label)
/-- Actual Copy operands preserve the cached vector and acquire a real reader. -/
def copyStack (k:Fin 3) : Stack := if k=0 then .bank else if k=1 then .reader else .copyScratch
/-- Static included Copy labels. -/
def copyLabel (pc:Fin 9) : Label := .inr (.inl pc)
/-- Literal parser operands, including the actual written validity bit. -/
def fieldStack : Field.Stack→Stack
  | .inl .input => .reader
  | .inl .scratch => .fieldScratch
  | .inl .output => .word
  | .inr _ => .valid
/-- Static included parser labels. -/
def fieldLabel (pc:Field.Label) : Label := .inr (.inr pc)
/-- One fixed concrete reader/counting instruction table. -/
def program : Label→C.Instruction Stack Label
  | .inr (.inl pc) => Link.instruction copyStack copyLabel (SemiprimeD1StackCopy.code pc)
  | .inr (.inr pc) => Link.instruction fieldStack fieldLabel (Field.code pc)
  | .inl .main => .call (copyLabel 0) (.inl .popVector)
  | .inl .popVector => .base (.pop .reader (.inl .halt) (.inl .halt) (.inl .fieldCall))
  | .inl .fieldCall => .call (fieldLabel (Field.active .tagPop (none,false))) (.inl .clearWord)
  | .inl .clearWord => .base (.pop .word (.inl .popValid) (.inl .clearWord) (.inl .clearWord))
  | .inl .popValid => .base (.pop .valid (.inl .pushCount) (.inl .pushCount) (.inl .pushCount))
  | .inl .pushCount => .base (.push .count true (.inl .popVector))
  | .inl .halt => .base .halt
/-- Fixed finite internal vector-counting machine. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine Stack.bank Stack.count (.inl .main) program
/-- Literal seven-word physical payload. -/
def data (bank reader count word fieldScratch valid copyScratch:List Bool) : Stack→List Bool
  | .bank => bank
  | .reader => reader
  | .count => count
  | .word => word
  | .fieldScratch => fieldScratch
  | .valid => valid
  | .copyScratch => copyScratch
/-- Component stack maps never alias distinct operands. -/
theorem copyStack_injective : Function.Injective copyStack := by decide
/-- Parser input/output/scratch/valid words are distinct actual stacks. -/
theorem fieldStack_injective : Function.Injective fieldStack := by decide
/-- Every actual alphabet, including the return-tag alphabet, is finite. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite Stack.bank Stack.count (.inl .main) program
/-- Seven fixed Boolean data stacks. -/
theorem stack_card : Fintype.card Stack=7 := by decide
/-- Seventy-one fixed program labels. -/
theorem label_card : Fintype.card Label=71 := by decide
end RiemannGaussian.SemiprimeD1StackDigitCount
