/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticTableExecution
import RiemannGaussian.SemiprimeD1StackPortOrdinalStreamOriginal
import RiemannGaussian.SemiprimeD1StackVertexRecordStream
/-! # Fixed static checker, acquired scope serializer and consuming row logger
The program depends only on one compile-time finite checker. Actual runtime
inputs are its original template, binary scope bytes and caller accumulators.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackStaticRecord
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace T
export SemiprimeD1StackStaticTable (Static Stack Label program initial counter aux)
end T
namespace S
export SemiprimeD1StackPortOrdinalStream (Stack Label program initial result)
end S
namespace R
export SemiprimeD1StackVertexRecordStream (Stack Label code data row recordTime)
end R
/-- Entire physical inventory, including all three dormant alias shadows. -/
abbrev Stack (K : Type) := T.Stack K ⊕ (S.Stack ⊕ R.Stack)
/-- Complete actual table compiler bank. -/
def tableStack {K : Type} (k : T.Stack K) : Stack K := .inl k
/-- The serializer reads the actual retained table scope bank directly. -/
def scopeStack {K : Type} : S.Stack → Stack K
  | .bank=>tableStack (T.counter .bank)
  | k=>.inr (.inl k)
/-- The logger consumes both actual component outputs without a copy. -/
def recordStack {K : Type} : R.Stack → Stack K
  | .ports=>scopeStack .output
  | .table=>tableStack (T.aux .output)
  | k=>.inr (.inr k)
/-- Actual binary scope input. -/
def original {K : Type} : Stack K :=scopeStack .bank
/-- Caller reverse chronological row history. -/
def history {K : Type} : Stack K :=recordStack .history
/-- Caller final output accumulator. -/
def output {K : Type} : Stack K :=recordStack .output
/-- Four literal caller stages, fixed before all original inputs. -/
inductive Control where | start | scope | record | done
  deriving DecidableEq
instance : Fintype Control := Fintype.ofList [.start,.scope,.record,.done]
  (by intro k;cases k <;> simp)
/-- Every static checker label and actual subroutine return label is finite. -/
abbrev Label (L : Type) (size : Nat) := Control ⊕ (T.Label L size ⊕ (S.Label ⊕ R.Label))
/-- Included table label. -/
def tableLabel {L : Type} {n : Nat} (pc : T.Label L n) : Label L n :=.inr (.inl pc)
/-- Included serializer label. -/
def scopeLabel {L : Type} {n : Nat} (pc : S.Label) : Label L n :=.inr (.inr (.inl pc))
/-- Included logger label. -/
def recordLabel {L : Type} {n : Nat} (pc : R.Label) : Label L n :=.inr (.inr (.inr pc))
variable {K L : Type} [DecidableEq K] (s : T.Static K L)
/-- Complete static table acquisition, paid ordinal conversion, consuming log
and halt. No number, table, arity, predicate or budget enters this definition. -/
def program : Label L s.roles.length→C.Instruction (Stack K) (Label L s.roles.length)
  | .inl .start=>.call (tableLabel .start) (.inl .scope)
  | .inl .scope=>.call (scopeLabel (.control .start)) (.inl .record)
  | .inl .record=>.call (recordLabel .record) (.inl .done)
  | .inl .done=>.base .halt
  | .inr (.inl pc)=>SemiprimeD1StackValidationLink.instruction tableStack tableLabel (T.program s pc)
  | .inr (.inr (.inl pc))=>SemiprimeD1StackValidationLink.instruction scopeStack scopeLabel (S.program pc)
  | .inr (.inr (.inr pc))=>SemiprimeD1StackMultiplierLink.instruction recordStack recordLabel (R.code pc)
/-- Full physical store; unused serializer bank and logger aliases stay empty. -/
def data (t : T.Stack K→List Bool) (u : S.Stack→List Bool) (hist out : List Bool) : Stack K→List Bool :=
  Sum.elim t (Sum.elim u (R.data [] [] hist out))
/-- Empty checker and private banks, only original template/scope and accumulators. -/
def initial (template : K→List Bool) (bank hist out : List Bool) : C.State (Stack K) (Label L s.roles.length) :=
  ⟨some (.inl .start),none,none,data (T.initial s template bank).data (fun _=>[]) hist out,[]⟩
/-- Serializer private result with the unused bank shadow physically empty. -/
def scopeData (words : List (List Bool)) : S.Stack→List Bool :=
  Function.update (SemiprimeD1StackPortOrdinalStreamExecution.done words).data .bank []
/-- Actual table acquisition state before serializer call. -/
def afterTable (template : K→List Bool) (words : List (List Bool)) (answer : List Bool→Bool)
    (hist out : List Bool) : Stack K→List Bool :=
  data (SemiprimeD1StackStaticTableExecution.result template words answer) (fun _=>[]) hist out
/-- Actual directly aliased serializer output ready for consuming logging. -/
def afterScope (template : K→List Bool) (words : List (List Bool)) (answer : List Bool→Bool)
    (hist out : List Bool) : Stack K→List Bool :=
  data (SemiprimeD1StackStaticTableExecution.result template words answer) (scopeData words) hist out
/-- Complete final state consumes both component outputs and retains original
scope/template/acquired count, all dormant shadows and caller final output. -/
def done (template : K→List Bool) (words : List (List Bool)) (answer : List Bool→Bool)
    (hist out : List Bool) : C.State (Stack K) (Label L s.roles.length) :=
  ⟨none,none,none,data
    (Function.update (SemiprimeD1StackStaticTableExecution.result template words answer) (T.aux .output) [])
    (Function.update (scopeData words) .output [])
    ((R.row (S.result words) (SemiprimeD1StackStaticTableExecution.outputTape answer words)).reverse++hist) out,[]⟩
/-- Same fixed finite machine for every original template and binary scope. -/
def machine [Fintype K] [Fintype L] : Turing.FinTM2 :=
  SemiprimeD1StackCalls.machine original output (.inl .start) (program s)
omit [DecidableEq K] in
/-- Complete physical cardinality includes all three alias shadows. -/
theorem stack_card [Fintype K] : Fintype.card (Stack K)=2*Fintype.card K+28 := by
  simp only [Stack,Fintype.card_sum]
  have hd:Fintype.card SemiprimeD1StackDigitCount.Stack=7:=by decide
  have ha:Fintype.card SemiprimeD1StackStaticTable.Aux=5:=by decide
  have hs:Fintype.card S.Stack=12:=by decide
  have hr:Fintype.card R.Stack=4:=by decide
  omega

omit [DecidableEq K] in
/-- Shared bank wiring is injective on all twelve serializer roles. -/
theorem scopeStack_injective : Function.Injective (@scopeStack K) := by
  intro a b h;cases a <;> cases b <;> simp_all [scopeStack,tableStack]
omit [DecidableEq K] in
/-- Both consumed inputs and caller accumulators remain distinct. -/
theorem recordStack_injective : Function.Injective (@recordStack K) := by
  intro a b h;cases a <;> cases b <;> simp_all [recordStack,scopeStack,tableStack]
end RiemannGaussian.SemiprimeD1StackStaticRecord
