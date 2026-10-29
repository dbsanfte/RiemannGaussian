/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanRecordOriginal
import RiemannGaussian.SemiprimeD1EdgeCatalogueEncoding
/-! # Literal original descriptor parsing and Boolean record dispatch
The five physical catalogue fields determine the finite original Boolean
family by real unary-tag pops. The actual table/scope/logger program then runs.
No decoded mode, vertex, arity, output row or clock is a runtime input.
Scope acquisition and the original descriptor producer remain caller work.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecord
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace R
export SemiprimeD1StackBooleanRecord (Stack Label program initial done history output)
end R
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F
/-- Five physical parser and tag-copy work roles. -/
inductive Aux where | reader | fieldScratch | valid | tagReader | copyScratch
  deriving DecidableEq, Repr
instance : Fintype Aux := Fintype.ofList [.reader,.fieldScratch,.valid,.tagReader,.copyScratch]
  (by intro k;cases k <;> simp)
/-- All27 roles: the actual17-role record program, five cached fields, five work roles. -/
abbrev Stack := R.Stack ⊕ (Fin 5 ⊕ Aux)
/-- One of the five actually parsed original catalogue fields. -/
def cache (part : Fin 5) : Stack := .inr (.inl part)
/-- A private Boolean work stack. -/
def aux (role : Aux) : Stack := .inr (.inr role)
/-- Literal parser operands; no field is decoded by host control. -/
def fieldStack (part : Fin 5) : F.Stack → Stack
  | .inl .input => aux .reader
  | .inl .scratch => aux .fieldScratch
  | .inl .output => cache part
  | .inr _ => aux .valid
/-- Preserving copy of the actual unary constructor tag. -/
def copyStack (k : Fin 3) : Stack :=
  if k=0 then cache 0 else if k=1 then aux .tagReader else aux .copyScratch
/-- Fixed five-field parsing and eighteen-position tag control. -/
inductive Control where
  | field (part : Fin 5) | valid (part : Fin 5) | copyTag | decode (count : Fin 18)
  | record (mode : SemiprimeD1StackBooleanEntry.Mode) | invalidClear | done | abort
  deriving DecidableEq, Fintype
/-- Every label and return alphabet is fixed before original N and all descriptors. -/
inductive Label where
  | local (pc : Control) | field (part : Fin 5) (pc : F.Label) | copy (pc : Fin 9)
  | record (pc : R.Label)
  deriving Fintype
/-- Exact original Boolean-family mapping, a finite instruction-table constant. -/
def dispatch (count : Fin 18) : Label :=
  if count.val=8 then .local (.record .orGate)
  else if count.val=9 then .local (.record .inputCheck)
  else if 10≤count.val then .local (.record .equality) else .local .abort
/-- The next real tag pop is one fixed bounded label, never a native unary decoder. -/
def nextDecode (count : Fin 18) : Label :=
  if h : count.val<17 then .local (.decode ⟨count.val+1,by omega⟩) else .local .invalidClear
/-- The fifth actual field is followed by copying the acquired constructor tag. -/
def nextField (part : Fin 5) : Label :=
  if h : part.val<4 then .local (.field ⟨part.val+1,by omega⟩) else .local .copyTag
/-- One literal parser, finite dispatch and actual whole-record instruction table. -/
def program : Label → C.Instruction Stack Label
  | .local (.field part) => .call (.field part (F.active .tagPop (none,false))) (.local (.valid part))
  | .local (.valid part) => .base (.pop (aux .valid) (.local .abort) (.local .abort) (nextField part))
  | .local .copyTag => .call (.copy 0) (.local (.decode 0))
  | .local (.decode count) => .base (.pop (aux .tagReader) (dispatch count) (nextDecode count) (nextDecode count))
  | .local (.record mode) => .call (.record (.inl (.start mode))) (.local .done)
  | .local .invalidClear => .base (.pop (aux .tagReader) (.local .abort) (.local .invalidClear) (.local .invalidClear))
  | .local .done | .local .abort => .base .halt
  | .field part pc => SemiprimeD1StackMultiplierLink.instruction (fieldStack part) (Label.field part) (F.code pc)
  | .copy pc => SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code pc)
  | .record pc => SemiprimeD1StackValidationLink.instruction Sum.inl Label.record (R.program pc)
/-- Proof-side complete physical store, including every retained cache. -/
def data (base : R.Stack → List Bool) (words : Fin 5 → List Bool)
    (reader valid tagReader : List Bool) : Stack → List Bool
  | .inl k => base k
  | .inr (.inl k) => words k
  | .inr (.inr .reader) => reader
  | .inr (.inr .valid) => valid
  | .inr (.inr .tagReader) => tagReader
  | _ => []
/-- Empty parser and tag-copy work, retaining the physical record substore. -/
def clean (base : R.Stack → List Bool) (words : Fin 5 → List Bool) (reader : List Bool) : Stack → List Bool :=
  data base words reader [] []
/-- The record bank and accumulators are actual bytes, independent of any selected mode. -/
def recordInput (bank hist out : List Bool) : R.Stack → List Bool :=
  (R.initial .equality bank hist out).data
/-- Only actual descriptor bytes, an acquired binary scope and caller accumulators are loaded. -/
def initial (descriptor bank hist out : List Bool) : C.State Stack Label :=
  ⟨some (.local (.field 0)),none,none,clean (recordInput bank hist out) (fun _=>[]) descriptor,[]⟩
/-- Fixed prepared-caller machine; the scope and descriptor producers are explicit caller work. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine
  (aux .reader) (.inl R.history) (.local (.field 0)) program
/-- All physical aliases and retained source fields are counted. -/
theorem stack_card : Fintype.card Stack=27 := by
  decide
/-- The actual parser has four distinct physical operands. -/
theorem field_injective (part : Fin 5) : Function.Injective (fieldStack part) := by fin_cases part <;> decide
/-- The tag copy has three distinct physical operands. -/
theorem copy_injective : Function.Injective copyStack := by decide
/-- Runtime flags contain only finite Boolean and literal-label data. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite (aux .reader) (.inl R.history) (.local (.field 0)) program
/-- All27 data alphabets and the real return-tag alphabet are finite. -/
theorem all_alphabets_finite (k : machine.K) : Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite (aux .reader) (.inl R.history) (.local (.field 0)) program k
end RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecord
