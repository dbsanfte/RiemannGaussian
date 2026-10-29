/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackZeroBoundaryTableBounds
import RiemannGaussian.SemiprimeD1StackPortOrdinalStreamOriginal
import RiemannGaussian.SemiprimeD1StackVertexRecordStream
/-! # Actual boundary table, acquired scope conversion and original record logging
The original binary N and an acquired binary occurrence-ID vector are the only
source fields. The two acquired outputs are the logger's actual operands.
Scope routing remains the caller's acquisition work.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackBoundaryRecord
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace Z
export SemiprimeD1StackZeroBoundaryTable (Stack Label program initial done original output)
end Z
namespace S
export SemiprimeD1StackPortOrdinalStream (Stack Label program initial result)
end S
namespace R
export SemiprimeD1StackVertexRecordStream (Stack Label code data row recordTime)
end R
/-- All forty-eight physical roles, including the two unused alias shadows. -/
abbrev Stack := Z.Stack ⊕ (S.Stack ⊕ R.Stack)
/-- Actual N-only source's private registers and public metadata. -/
def boundaryStack (k : Z.Stack) : Stack := .inl k
/-- Actual preserving binary-ID serializer's private registers and bank. -/
def scopeStack (k : S.Stack) : Stack := .inr (.inl k)
/-- Direct operands: neither acquired answer is copied or recoded. -/
def recordStack : R.Stack → Stack
  | .ports => scopeStack .output
  | .table => boundaryStack Z.output
  | k => .inr (.inr k)
/-- Original binary N's physical input role. -/
def original : Stack := boundaryStack Z.original
/-- The actual caller's accumulated reverse row log. -/
def history : Stack := recordStack .history
/-- The actual caller's retained final output accumulator. -/
def output : Stack := recordStack .output
/-- Four finite local controls, independent of every input value. -/
inductive Control where | start | scope | record | done
  deriving DecidableEq
instance : Fintype Control := Fintype.ofList [.start,.scope,.record,.done] (by intro k;cases k <;> simp)
/-- All real component labels, with no decoded identifier in control. -/
abbrev Label := Control ⊕ (Z.Label ⊕ (S.Label ⊕ R.Label))
/-- Literal whole-table acquisition procedure inclusion. -/
def boundaryLabel (pc : Z.Label) : Label := .inr (.inl pc)
/-- Literal binary ordinal serialization procedure inclusion. -/
def scopeLabel (pc : S.Label) : Label := .inr (.inr (.inl pc))
/-- Literal physical frame logger inclusion. -/
def recordLabel (pc : R.Label) : Label := .inr (.inr (.inr pc))
/-- The actual three calls; the logger consumes both acquired outputs directly. -/
def program : Label → C.Instruction Stack Label
  | .inl .start => .call (boundaryLabel (.inl .start)) (.inl .scope)
  | .inl .scope => .call (scopeLabel (.control .start)) (.inl .record)
  | .inl .record => .call (recordLabel .record) (.inl .done)
  | .inl .done => .base .halt
  | .inr (.inl pc) => SemiprimeD1StackValidationLink.instruction boundaryStack boundaryLabel (Z.program pc)
  | .inr (.inr (.inl pc)) => SemiprimeD1StackValidationLink.instruction scopeStack scopeLabel (S.program pc)
  | .inr (.inr (.inr pc)) => SemiprimeD1StackMultiplierLink.instruction recordStack recordLabel (R.code pc)
/-- Entire physical inventory; both unused alias shadows stay empty. -/
def data (z : Z.Stack → List Bool) (s : S.Stack → List Bool) (hist out : List Bool) : Stack → List Bool :=
  Sum.elim z (Sum.elim s (R.data [] [] hist out))
/-- Only original binary N, acquired binary scope bytes and caller accumulators. -/
def initial (bits bank hist out : List Bool) : C.State Stack Label :=
  ⟨some (.inl .start),none,none,data (Z.initial bits).data (S.initial bank).data hist out,[]⟩
/-- Proof-side exact acquired boundary bytes, never a runtime input. -/
def table (bits : List Bool) : List Bool := (Z.done bits).data Z.output
/-- Both acquired fields are consumed; the public caches and original bank remain. -/
def done (bits : List Bool) (words : List (List Bool)) (hist out : List Bool) : C.State Stack Label :=
  ⟨none,none,none,data (Function.update (Z.done bits).data Z.output [])
    (Function.update (SemiprimeD1StackPortOrdinalStreamExecution.done words).data (SemiprimeD1StackPortOrdinalStream.Stack.output) [])
    ((R.row (S.result words) (table bits)).reverse++hist) out,[]⟩
/-- Genuine fixed finite procedure machine, including the actual return alphabet. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine original output (.inl .start) program
/-- Every original metadata, private scratch and unused alias role is counted. -/
theorem stack_card : Fintype.card Stack=48 := by decide
/-- The logger's two shared operands and its own accumulators are distinct. -/
theorem recordStack_injective : Function.Injective recordStack := by decide
/-- The actual public acquisition's complete metadata cache survives record logging. -/
theorem retained_public (bits : List Bool) (words : List (List Bool)) (hist out : List Bool)
    (k : SemiprimeD1StackZeroBoundaryTable.P.Stack) :
    (done bits words hist out).data (boundaryStack (.inl k))=
      SemiprimeD1StackZeroBoundaryTable.context bits k := rfl
/-- The original binary occurrence-ID bank is preserved byte for byte. -/
theorem retained_bank (bits : List Bool) (words : List (List Bool)) (hist out : List Bool) :
    (done bits words hist out).data (scopeStack .bank)=SemiprimeD1TensorTapeCodec.vectorBits words := rfl
/-- Appending a row leaves the caller's final output accumulator intact. -/
theorem retained_output (bits : List Bool) (words : List (List Bool)) (hist out : List Bool) :
    (done bits words hist out).data output=out := rfl
end RiemannGaussian.SemiprimeD1StackBoundaryRecord
