/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerTableOriginal
import RiemannGaussian.SemiprimeD1StackPortOrdinalStreamOriginal
import RiemannGaussian.SemiprimeD1StackVertexRecordStreamExecution
/-! # Actual owner table, numeric scope conversion and consuming record source
The table counter and serializer share ONE physically acquired scope bank.
Only actual owner-key, prefix and scope bytes enter; degree and compatibility
are computed by the included sources. All alias shadows remain allocated.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 32768
namespace RiemannGaussian.SemiprimeD1StackOwnerRecord
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace T
export SemiprimeD1StackOwnerTable (Stack Label program initial data scope query reader output)
end T
namespace S
export SemiprimeD1StackPortOrdinalStream (Stack Label program initial result)
end S
namespace R
export SemiprimeD1StackVertexRecordStream (Stack Label code data row recordTime)
end R
/-- All34 roles, including three physically empty alias shadows. -/
abbrev Stack := T.Stack ⊕ (S.Stack ⊕ R.Stack)
/-- Included complete physical ordinal-conversion role. -/
def scopeStack (k : S.Stack) : Stack := .inr (.inl k)
/-- The real table scope counter and ordinal serializer use the SAME bank. -/
def tableStack : T.Stack → Stack
  | .inr (.inl .bank) => scopeStack .bank
  | k => .inl k
/-- Actual source outputs are the two consuming logger operands. -/
def recordStack : R.Stack → Stack
  | .ports => scopeStack .output
  | .table => tableStack T.output
  | k => .inr (.inr k)
/-- Shared physically acquired binary occurrence-ID bank. -/
def original : Stack := scopeStack .bank
/-- Actual accumulated reverse row log. -/
def history : Stack := recordStack .history
/-- Actual final forward record stream output. -/
def output : Stack := recordStack .output
/-- Fixed finite outer source phases, with no unbounded control data. -/
inductive Control where
  | start | scope | record | done
  deriving DecidableEq
instance : Fintype Control := Fintype.ofList [.start,.scope,.record,.done]
  (by intro k;cases k <;> simp)
/-- All included source and literal bytecode labels, fixed before original N. -/
abbrev Label := Control ⊕ (T.Label ⊕ (S.Label ⊕ R.Label))
/-- Included actual owner-table source location. -/
def tableLabel (pc : T.Label) : Label := .inr (.inl pc)
/-- Included actual ordinal-conversion source location. -/
def scopeLabel (pc : S.Label) : Label := .inr (.inr (.inl pc))
/-- Included actual consuming logger location. -/
def recordLabel (pc : R.Label) : Label := .inr (.inr (.inr pc))
/-- One fixed actual owner-table, scope-conversion and record-logging program. -/
def program : Label → C.Instruction Stack Label
  | .inl .start => .call (tableLabel .start) (.inl .scope)
  | .inl .scope => .call (scopeLabel (.control .start)) (.inl .record)
  | .inl .record => .call (recordLabel .record) (.inl .done)
  | .inl .done => .base .halt
  | .inr (.inl pc) => SemiprimeD1StackValidationLink.instruction tableStack tableLabel (T.program pc)
  | .inr (.inr (.inl pc)) => SemiprimeD1StackValidationLink.instruction scopeStack scopeLabel (S.program pc)
  | .inr (.inr (.inr pc)) => SemiprimeD1StackMultiplierLink.instruction recordStack recordLabel (R.code pc)
/-- Proof-side complete physical store, with the unused table-bank shadow empty. -/
def data (t : T.Stack → List Bool) (s : S.Stack → List Bool) (hist out : List Bool) : Stack → List Bool
  | .inl (.inr (.inl .bank)) => []
  | .inl k => t k
  | .inr (.inl k) => s k
  | .inr (.inr k) => R.data [] [] hist out k
/-- Only acquired key, actual prefix/scope bytes and caller accumulators initialize this source. -/
def initial (key prefixBytes bank hist out : List Bool) : C.State Stack Label :=
  ⟨some (.inl .start),none,none,
    data (T.initial key prefixBytes bank).data (S.initial bank).data hist out,[]⟩
/-- Specification of the table ALREADY computed from actual bytes. -/
def table (key : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (words : List (List Bool)) (hs : words.length≤2) : List Bool :=
  (SemiprimeD1StackOwnerTableExecution.done key rows tail words hs).data T.output
/-- Exact complete physical halt store with original source data and prefix retained. -/
def done (key : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (words : List (List Bool)) (hs : words.length≤2) (hist out : List Bool) : C.State Stack Label :=
  ⟨none,none,none,
    data (Function.update (SemiprimeD1StackOwnerTableExecution.done key rows tail words hs).data T.output [])
      (Function.update (SemiprimeD1StackPortOrdinalStreamExecution.done words).data
        SemiprimeD1StackPortOrdinalStream.Stack.output [])
      ((R.row (S.result words) (table key rows tail words hs)).reverse++hist) out,[]⟩
/-- Genuine fixed finite machine compiling the actual source and real return alphabet. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine original output (.inl .start) program
theorem stack_card : Fintype.card Stack=34 := by decide
theorem scopeStack_injective : Function.Injective scopeStack := by
  intro a b h;exact Sum.inl_injective (Sum.inr_injective h)
theorem tableStack_injective : Function.Injective tableStack := by decide
theorem recordStack_injective : Function.Injective recordStack := by decide
/-- The actual common binary bank survives both scans and row logging. -/
theorem retained_bank (key : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (words : List (List Bool)) (hs : words.length≤2) (hist out : List Bool) :
    (done key rows tail words hs hist out).data original=SemiprimeD1TensorTapeCodec.vectorBits words := rfl
end RiemannGaussian.SemiprimeD1StackOwnerRecord
