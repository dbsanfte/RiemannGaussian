/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueResources
import RiemannGaussian.SemiprimeD1StackOwnerRecordBounds
/-! # Actual original-N all-owner record source
The retained N-only catalogue is physically copied and parsed. Every owner
gets a fresh physical copy of the caller prefix, the real table/ordinal/logger
source runs, and retained key/tail/bank words are physically drained. Empty
prefix initialization is a literal push. No owner/key/fibre/table is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerRecords
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace S
export SemiprimeD1StackOwnerFibreCatalogue (Stack Label program originalInput input)
end S
namespace R
export SemiprimeD1StackOwnerRecord (Stack Label program original history output initial done)
end R
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F
namespace L
export SemiprimeD1StackVertexRecordStream (Stack Label code data row)
end L
/-- Five physically allocated outer reader, prefix, copy and parser work roles. -/
inductive Aux where
  | reader | prefixBytes | copyScratch | fieldScratch | valid
  deriving DecidableEq
instance : Fintype Aux :=Fintype.ofList [.reader,.prefixBytes,.copyScratch,.fieldScratch,.valid]
  (by intro k;cases k <;> simp)
/-- All344 physical roles, including every retained source cache and unused alias shadow. -/
abbrev Stack := S.Stack ⊕ (R.Stack ⊕ Aux)
/-- Complete actual N-only all-owner fibre source role inclusion. -/
def source (k : S.Stack) : Stack := .inl k
/-- Complete actual34-role table, ordinal and consuming logger inclusion. -/
def record (k : R.Stack) : Stack := .inr (.inl k)
/-- Literal outer reader, retained-prefix or parser work role. -/
def aux (k : Aux) : Stack := .inr (.inr k)
/-- Only original binary N is present at standard machine initialization. -/
def originalInput : Stack := source S.originalInput
/-- Actual accumulated reverse row log. -/
def history : Stack := record R.history
/-- Actual final forward record stream output. -/
def output : Stack := record R.output
/-- Actual parsed original binary E-owner key operand. -/
def key : Stack := record (SemiprimeD1StackOwnerRecord.tableStack SemiprimeD1StackOwnerTable.query)
/-- Actual fresh copy of the retained caller prefix for this owner. -/
def prefixReader : Stack := record (SemiprimeD1StackOwnerRecord.tableStack SemiprimeD1StackOwnerTable.reader)
/-- Actual parsed ordered binary scope-ID vector, shared by table counter and serializer. -/
def bank : Stack := record R.original
/-- Logger role inclusion with its actual source operands directly aliased. -/
def logStack (k : L.Stack) : Stack :=record (SemiprimeD1StackOwnerRecord.recordStack k)
/-- Two actual copies: complete source catalogue and caller prefix bytes per owner. -/
def copyStack (part : Bool) (k : Fin 3) : Stack :=
  if k=0 then (if part then aux .prefixBytes else source (SemiprimeD1StackOwnerFibreCatalogue.aux .output))
  else if k=1 then (if part then prefixReader else aux .reader) else aux .copyScratch
/-- Actual source-catalogue parser roles; the finite phase chooses key or bank output. -/
def fieldStack (scopes : Bool) : F.Stack → Stack
  | .inl .input => aux .reader
  | .inl .scratch => aux .fieldScratch
  | .inl .output => if scopes then bank else key
  | .inr _ => aux .valid
/-- Fixed finite outer source phases, with no unbounded control data. -/
inductive Control where
  | empty | main | copyCatalogue | initialize | loop | field (scopes : Bool) | valid (scopes : Bool)
  | copyPrefix | emit | clearKey | clearTail | clearBank | reverse | halt | abort
  deriving Fintype
/-- All included source and literal bytecode labels, fixed before original N. -/
inductive Label where
  | local (pc : Control) | source (pc : S.Label) | record (pc : R.Label)
  | copy (part : Bool) (pc : Fin 9) | field (scopes : Bool) (pc : F.Label) | log (pc : L.Label)
  deriving Fintype
/-- ONE fixed original-input source; original E/M counts and tables never enter control. -/
def program : Label → C.Instruction Stack Label
  | .source pc => SemiprimeD1StackValidationLink.instruction source Label.source (S.program pc)
  | .record pc => SemiprimeD1StackValidationLink.instruction record Label.record (R.program pc)
  | .copy part pc => SemiprimeD1StackMultiplierLink.instruction (copyStack part) (Label.copy part) (SemiprimeD1StackCopy.code pc)
  | .field scopes pc => SemiprimeD1StackMultiplierLink.instruction (fieldStack scopes) (Label.field scopes) (F.code pc)
  | .log pc => SemiprimeD1StackMultiplierLink.instruction logStack Label.log (L.code pc)
  | .local .empty => .base (.push (aux .prefixBytes) false (.local .main))
  | .local .main => .call (.source (.local .main)) (.local .copyCatalogue)
  | .local .copyCatalogue => .call (.copy false 0) (.local .initialize)
  | .local .initialize => .call (.log .initialize) (.local .loop)
  | .local .loop => .base (.pop (aux .reader) (.local .reverse) (.local .reverse) (.local (.field false)))
  | .local (.field scopes) => .call (.field scopes (F.active .tagPop (none,false))) (.local (.valid scopes))
  | .local (.valid scopes) => .base (.pop (aux .valid) (.local .abort) (.local .abort)
      (if scopes then .local .copyPrefix else .local (.field true)))
  | .local .copyPrefix => .call (.copy true 0) (.local .emit)
  | .local .emit => .call (.record (.inl .start)) (.local .clearKey)
  | .local .clearKey => .base (.pop key (.local .clearTail) (.local .clearKey) (.local .clearKey))
  | .local .clearTail => .base (.pop prefixReader (.local .clearBank) (.local .clearTail) (.local .clearTail))
  | .local .clearBank => .base (.pop bank (.local .loop) (.local .clearBank) (.local .clearBank))
  | .local .reverse => .call (.log .reverse) (.local .halt)
  | .local .halt | .local .abort => .base .halt
/-- Complete physical source, owner-record and outer-role store description. -/
def data (s : S.Stack → List Bool) (r : R.Stack → List Bool) (a : Aux → List Bool) : Stack → List Bool :=
  Sum.elim s (Sum.elim r a)
/-- Actual remaining catalogue reader and retained caller prefix, with work roles empty. -/
def rowAux (reader prefixBytes : List Bool) : Aux → List Bool
  | .reader => reader | .prefixBytes => prefixBytes | _ => []
/-- Arbitrary actual caller prefix is retained separately and copied before every owner. -/
def initialPrefix (bits prefixBytes : List Bool) : C.State Stack Label :=
  ⟨some (.local .main),none,none,data (S.input bits) (fun _=>[]) (rowAux [] prefixBytes),[]⟩
/-- Empty-prefix specialization initially contains ONLY binary original N. -/
def initial (bits : List Bool) : C.State Stack Label :=
  ⟨some (.local .empty),none,none,data (S.input bits) (fun _=>[]) (rowAux [] []),[]⟩
/-- Genuine fixed finite machine compiling the actual source and real return alphabet. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackCalls.machine originalInput output (.local .empty) program
theorem stack_card :Fintype.card Stack=344:=by decide
end RiemannGaussian.SemiprimeD1StackOwnerRecords
