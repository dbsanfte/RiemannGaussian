/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackTransformBounds
import RiemannGaussian.SemiprimeD1StackDigitBankBounds

/-! # Original-input transform and full digit-bank acquisition
One fixed finite program starts with ONLY binary N. It executes the complete
transform supplier, physically copies its retained N and acquired radix tally,
then executes the complete EOF-driven digit bank. No prepared metadata, width,
digit count, digit value or evaluator is a caller input.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1BinaryDigitAcquisition
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace Meta
export SemiprimeD1StackTransform (Stack Label Local program input initial)
end Meta
namespace Bank
export SemiprimeD1StackDigitBank (Stack Label program original output)
end Bank

/-- All metadata/bank data and one real copy-restoration stack are fixed before input. -/
abbrev Stack := Meta.Stack⊕(Bank.Stack⊕Unit)

/-- Fixed literal pipeline control. -/
inductive Control where
  | start | copyInput | copyRadix | bankCall | done
  deriving DecidableEq,Repr

/-- Explicit fixed control catalogue, independent of all input sizes. -/
instance : Fintype Control := Fintype.ofList [.start,.copyInput,.copyRadix,.bankCall,.done]
  (by intro k;cases k <;> simp)

/-- Fixed nested component labels, not input-sized bytecode. -/
abbrev Label := Control⊕(Meta.Label⊕((Bool×Fin 9)⊕Bank.Label))

/-- Static metadata-stack inclusion. -/
def metaStack : Meta.Stack→Stack := Sum.inl
/-- Static bank-stack inclusion. -/
def bankStack (k : Bank.Stack) : Stack := .inr (.inl k)
/-- One literal restoration stack for both inter-stage copy calls. -/
def copyTemporary : Stack := .inr (.inr ())

/-- Literal control label. -/
def mainLabel : Control→Label := Sum.inl
/-- Literal metadata code inclusion. -/
def metaLabel (l : Meta.Label) : Label := .inr (.inl l)
/-- Literal inter-stage copy code inclusion. -/
def copyLabel (radix : Bool) (l : Fin 9) : Label := .inr (.inr (.inl (radix,l)))
/-- Literal full bank code inclusion. -/
def bankLabel (l : Bank.Label) : Label := .inr (.inr (.inr l))

/-- Actual retained source is original binary input or physically acquired radix. -/
def copySource (radix : Bool) : Stack := metaStack (if radix then .radix else .input)
/-- Actual bank destination is original binary word or cached physical width. -/
def copyTarget (radix : Bool) : Stack := bankStack (if radix then .inl .width else Bank.original)

/-- Real three-stack copy operand map; nothing is preloaded by the caller. -/
def copyStack (radix : Bool) : Fin 3→Stack :=
  fun k=>if k=0 then copySource radix else if k=1 then copyTarget radix else copyTemporary

/-- Complete finite instruction table, preserving both components' nested calls. -/
def program : Label→C.Instruction Stack Label
  | .inl .start => .call (metaLabel (.inl .start)) (mainLabel .copyInput)
  | .inl .copyInput => .call (copyLabel false 0) (mainLabel .copyRadix)
  | .inl .copyRadix => .call (copyLabel true 0) (mainLabel .bankCall)
  | .inl .bankCall => .call (bankLabel (SemiprimeD1StackDigitBank.control .start)) (mainLabel .done)
  | .inl .done => .base .halt
  | .inr (.inl l) => SemiprimeD1StackValidationLink.instruction metaStack metaLabel (Meta.program l)
  | .inr (.inr (.inl (r,l))) =>
      SemiprimeD1StackMultiplierLink.instruction (copyStack r) (copyLabel r) (SemiprimeD1StackCopy.code l)
  | .inr (.inr (.inr l)) => SemiprimeD1StackValidationLink.instruction bankStack bankLabel (Bank.program l)

/-- Literal combined physical store; no runtime answer is synthesized by this proof view. -/
def store (metadata : Meta.Stack→List Bool) (bank : Bank.Stack→List Bool) (temporary : List Bool) : Stack→List Bool :=
  Sum.elim metadata (Sum.elim bank (fun _=>temporary))

/-- True original-input initial data, every bank/copy/derived metadata stack empty. -/
def input (bits : List Bool) : Stack→List Bool := store (Meta.input bits) (fun _=>[]) []

/-- Original-input source state before any metadata call. -/
def initial (bits : List Bool) : C.State Stack Label := ⟨some (mainLabel .start),none,none,input bits,[]⟩

/-- All real inter-stage copy stacks are distinct. -/
theorem copyStack_injective (radix : Bool) : Function.Injective (copyStack radix) := by
  intro i j h
  cases radix <;> fin_cases i <;> fin_cases j <;>
    simp_all [copyStack,copySource,copyTarget,copyTemporary,metaStack,bankStack,SemiprimeD1StackDigitBank.original]

/-- One fixed actual machine whose sole initial input is the original binary integer. -/
def machine : Turing.FinTM2 :=
  SemiprimeD1StackCalls.machine (metaStack .input) (bankStack Bank.output) (mainLabel .start) program

/-- Every data/return alphabet is finite and fixed before N. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite (metaStack .input) (bankStack Bank.output) (mainLabel .start) program

/-- Internal control is finite, containing no native N/digit/cache answer. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite (metaStack .input) (bankStack Bank.output) (mainLabel .start) program

end RiemannGaussian.SemiprimeD1BinaryDigitAcquisition
