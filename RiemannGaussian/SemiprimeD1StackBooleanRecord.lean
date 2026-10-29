/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanTableSource
import RiemannGaussian.SemiprimeD1StackPortOrdinalStreamOriginal
import RiemannGaussian.SemiprimeD1StackVertexRecordStream
/-! # Actual fixed Boolean table, acquired ordered scope and original row logging
The only unbounded inputs are the acquired binary occurrence-ID bank and caller
accumulators. The mode is one of three finite original vertex tags.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackBooleanRecord
open SemiprimeD1StackBooleanEntry (Mode)
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace T
export SemiprimeD1StackBooleanTableSource (Stack Label code initial done)
end T
namespace S
export SemiprimeD1StackPortOrdinalStream (Stack Label program initial result)
end S
namespace R
export SemiprimeD1StackVertexRecordStream (Stack Label code data row recordTime)
end R
/-- All seventeen roles, including two unused alias shadows. -/
abbrev Stack := T.Stack ⊕ (S.Stack ⊕ R.Stack)
/-- The literal table writer's one physical output. -/
def tableStack (k : T.Stack) : Stack := .inl k
/-- The preserving binary-ID serializer's complete physical inventory. -/
def scopeStack (k : S.Stack) : Stack := .inr (.inl k)
/-- Direct acquired operands: no encoded-answer copy or recoding. -/
def recordStack : R.Stack → Stack
  | .ports => scopeStack .output
  | .table => tableStack ()
  | k => .inr (.inr k)
/-- Original binary occurrence-ID bank input. -/
def original : Stack := scopeStack .bank
/-- Actual caller's accumulated reverse row log. -/
def history : Stack := recordStack .history
/-- Actual caller's retained final output accumulator. -/
def output : Stack := recordStack .output
/-- One finite original vertex tag chooses a literal source entry. -/
inductive Control where
  | start (mode : Mode) | scope | record | done
  deriving DecidableEq, Fintype
/-- All component and caller labels are fixed before the original binary input. -/
abbrev Label := Control ⊕ (T.Label ⊕ (S.Label ⊕ R.Label))
/-- Included literal whole-table labels. -/
def tableLabel (pc : T.Label) : Label := .inr (.inl pc)
/-- Included binary ordinal serialization labels. -/
def scopeLabel (pc : S.Label) : Label := .inr (.inr (.inl pc))
/-- Included physical row logger labels. -/
def recordLabel (pc : R.Label) : Label := .inr (.inr (.inr pc))
/-- Actual table, scope and consuming logger calls, then literal halt. -/
def program : Label → C.Instruction Stack Label
  | .inl (.start mode) => .call (tableLabel (mode,0)) (.inl .scope)
  | .inl .scope => .call (scopeLabel (.control .start)) (.inl .record)
  | .inl .record => .call (recordLabel .record) (.inl .done)
  | .inl .done => .base .halt
  | .inr (.inl pc) => SemiprimeD1StackMultiplierLink.instruction tableStack tableLabel (T.code pc)
  | .inr (.inr (.inl pc)) => SemiprimeD1StackValidationLink.instruction scopeStack scopeLabel (S.program pc)
  | .inr (.inr (.inr pc)) => SemiprimeD1StackMultiplierLink.instruction recordStack recordLabel (R.code pc)
/-- Entire physical inventory, including both empty unused alias shadows. -/
def data (t : T.Stack → List Bool) (s : S.Stack → List Bool) (hist out : List Bool) : Stack → List Bool :=
  Sum.elim t (Sum.elim s (R.data [] [] hist out))
/-- Empty table source; only acquired binary scope bytes and caller accumulators. -/
def initial (mode : Mode) (bank hist out : List Bool) : C.State Stack Label :=
  ⟨some (.inl (.start mode)),none,none,data (fun _=>[]) (S.initial bank).data hist out,[]⟩
/-- Proof-side table byte notation, never an input answer. -/
def table (mode : Mode) : List Bool := SemiprimeD1BooleanRootTables.bytes mode
/-- Both acquired fields consumed, binary bank and caller output preserved. -/
def done (mode : Mode) (words : List (List Bool)) (hist out : List Bool) : C.State Stack Label :=
  ⟨none,none,none,data (fun _=>[])
    (Function.update (SemiprimeD1StackPortOrdinalStreamExecution.done words).data
      SemiprimeD1StackPortOrdinalStream.Stack.output [])
    ((R.row (S.result words) (table mode)).reverse++hist) out,[]⟩
/-- Genuine fixed program and real return alphabet; mode is a finite entry label. -/
def machine (mode : Mode) : Turing.FinTM2 :=
  SemiprimeD1StackCalls.machine original output (.inl (.start mode)) program
/-- Every physical register, including both unused aliases, is counted. -/
theorem stack_card : Fintype.card Stack=17 := by decide
/-- The two shared operands and caller accumulators are distinct. -/
theorem recordStack_injective : Function.Injective recordStack := by decide
/-- The acquired ordered binary occurrence bank survives byte for byte. -/
theorem retained_bank (mode : Mode) (words : List (List Bool)) (hist out : List Bool) :
    (done mode words hist out).data original=SemiprimeD1TensorTapeCodec.vectorBits words := rfl
/-- The final output accumulator is untouched by a new record. -/
theorem retained_output (mode : Mode) (words : List (List Bool)) (hist out : List Bool) :
    (done mode words hist out).data output=out := rfl
end RiemannGaussian.SemiprimeD1StackBooleanRecord
