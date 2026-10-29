/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDigitBlockBounds
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
import RiemannGaussian.SemiprimeD1StackAssignmentBody

/-! # Actual streaming original digit-bank program
The original binary integer is physically copied once and retained. A positive
cached radix width drives repeated real block calls until the reader reaches
EOF. Each canonical block is physically framed into a reverse log, then the
whole bank is reversed once. No digit count, digit result or offset is supplied.
Width acquisition remains the original metadata caller's responsibility.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackDigitBank
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace Block
export SemiprimeD1StackDigitBlock (Stack Label program)
end Block
namespace Body
export SemiprimeD1StackAssignmentBody (Stack Label code entry)
end Body

/-- Eight block work/cache stacks plus original input, reverse history and final output. -/
abbrev Stack := Block.Stack⊕Fin 3

/-- Fixed physical original binary input stack. -/
def original : Stack := .inr 0
/-- Fixed reverse digit-vector log. -/
def history : Stack := .inr 1
/-- Fixed final encoded digit-bank output. -/
def output : Stack := .inr 2

/-- Fixed local finite-state control. -/
inductive Control where
  | start | copyInput | loop | blockCall | logCall | clearBlock
  | finish | reverse | emit (bit : Bool) | done
  deriving DecidableEq,Fintype,Repr

/-- Disjoint fixed component labels. Body syntax locations are finite types,
not runtime-sized label/address catalogues. -/
abbrev Label := Control⊕(Fin 9⊕(Block.Label⊕Body.Label))

/-- Literal local control inclusion. -/
def control : Control→Label := Sum.inl
/-- Literal initial-copy procedure inclusion. -/
def copyLabel (l : Fin 9) : Label := .inr (.inl l)
/-- Literal nested block-reader inclusion. -/
def blockLabel (l : Block.Label) : Label := .inr (.inr (.inl l))
/-- Literal frame/log body inclusion. -/
def bodyLabel (l : Body.Label) : Label := .inr (.inr (.inr l))

/-- Initial copy preserves original binary N and acquires its disposable reader. -/
def copyStack : Fin 3→Stack := fun k=>if k=0 then original else if k=1 then .inl .input else .inl .temporary

/-- Real frame logging restores the canonical block and clears its restoration scratch. -/
def bodyStack : Body.Stack→Stack
  | .word => .inl .output
  | .scratch => .inl .scratch
  | .history => history

/-- One actual fixed finite program. Empty width halts instead of looping;
original positive-input metadata supplies the proved positive radix width. -/
def program : Label→C.Instruction Stack Label
  | .inl .start => .base (.peek (.inl .width) (control .done) (control .copyInput) (control .copyInput))
  | .inl .copyInput => .call (copyLabel 0) (control .loop)
  | .inl .loop => .base (.peek (.inl .input) (control .finish) (control .blockCall) (control .blockCall))
  | .inl .blockCall => .call (blockLabel .start) (control .logCall)
  | .inl .logCall => .call (bodyLabel Body.entry) (control .clearBlock)
  | .inl .clearBlock => .base (.pop (.inl .output) (control .loop) (control .clearBlock) (control .clearBlock))
  | .inl .finish => .base (.push output false (control .reverse))
  | .inl .reverse => .base (.pop history (control .done) (control (.emit false)) (control (.emit true)))
  | .inl (.emit b) => .base (.push output b (control .reverse))
  | .inl .done => .base .halt
  | .inr (.inl l) => SemiprimeD1StackMultiplierLink.instruction copyStack copyLabel (SemiprimeD1StackCopy.code l)
  | .inr (.inr (.inl l)) => SemiprimeD1StackValidationLink.instruction Sum.inl blockLabel (Block.program l)
  | .inr (.inr (.inr l)) => SemiprimeD1StackMultiplierLink.instruction bodyStack bodyLabel (Body.code l)

/-- Actual bank store: original N, unread high tail, cached radix, one block,
reverse log and final vector. All other block/copy/trim work is empty. -/
def store (originalWord reader width block historyWord finalOutput : List Bool) : Stack→List Bool :=
  Sum.elim (SemiprimeD1StackDigitBlock.store reader width [] [] [] [] [] block)
    (fun k=>if k=0 then originalWord else if k=1 then historyWord else finalOutput)

/-- Initial word copying has no aliased source/reader/restoration stack. -/
theorem copyStack_injective : Function.Injective copyStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [copyStack,original]

/-- Logging touches only its own block/scratch/log cells. -/
theorem bodyStack_injective : Function.Injective bodyStack := by
  intro i j h
  cases i <;> cases j <;> simp_all [bodyStack,history]

/-- Fixed actual procedure machine; the public metadata caller supplies width
physically, while original N occupies only its binary input stack. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine original output (control .start) program

/-- Every Boolean data alphabet and the fixed finite return alphabet is finite. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite original output (control .start) program

/-- No unbounded input/digit/count datum is in finite internal control. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite original output (control .start) program

end RiemannGaussian.SemiprimeD1StackDigitBank
