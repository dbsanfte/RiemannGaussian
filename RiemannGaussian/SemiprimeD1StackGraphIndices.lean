/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackTransformBounds
import RiemannGaussian.SemiprimeD1StackValidationLink
import RiemannGaussian.SemiprimeD1StackFrame

/-! # Actual word-bit index catalogue program
The retained radius is physically copied twice. Descending physical indices
are framed by the real included Frame code, producing the canonical ascending
catalogue on the output stack. No prepared index/graph/list answer is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackGraphIndices
namespace Meta
export SemiprimeD1StackTransform (Stack Label program input initial)
end Meta
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace LinkB
export SemiprimeD1StackMultiplierLink (instruction DataRel data_unique Rel run_rel)
end LinkB
namespace LinkC
export SemiprimeD1StackValidationLink (instruction Rel run_rel)
end LinkC
/-- Original metadata plus framed output and physical frame scratch. -/
abbrev Stack := Meta.Stack⊕Bool
/-- Seven fixed local program labels. -/
inductive Local where
  | start | ready | copyIndex | emit | check | dec | halt
  deriving DecidableEq,Repr
/-- Exhaustive literal finite local control. -/
instance : Fintype Local where
  elems:={.start,.ready,.copyIndex,.emit,.check,.dec,.halt}
  complete:=by intro pc;cases pc <;> simp
/-- Static metadata, two Copy instances, and the real Frame code. -/
abbrev Label := Local⊕(Meta.Label⊕((Bool×Fin 9)⊕Fin 11))
/-- Original metadata label inclusion. -/
def metaLabel (pc:Meta.Label) : Label := .inr (.inl pc)
/-- Copy radius to remaining or current-index work. -/
def copyOutput (mode:Bool) : Stack := .inl (if mode then .thresholdWork else .squareWork)
/-- Real disjoint Copy roles. -/
def copyStack (mode:Bool) (k:Fin 3) : Stack :=
  if k=0 then .inl .radius else if k=1 then copyOutput mode else .inl .temporary
/-- Fixed Copy labels. -/
def copyLabel (mode:Bool) (pc:Fin 9) : Label := .inr (.inr (.inl (mode,pc)))
/-- Current physical index, output tape, and actual frame scratch. -/
def frameStack (k:Fin 3) : Stack :=
  if k=0 then .inl .thresholdWork else if k=1 then .inr false else .inr true
/-- Static actual Frame instruction labels. -/
def frameLabel (pc:Fin 11) : Label := .inr (.inr (.inr pc))
/-- One fixed finite instruction program before every input. -/
def program : Label→C.Instruction Stack Label
  | .inr (.inl pc) => LinkC.instruction Sum.inl metaLabel (Meta.program pc)
  | .inr (.inr (.inl (mode,pc))) => LinkB.instruction (copyStack mode) (copyLabel mode) (SemiprimeD1StackCopy.code pc)
  | .inr (.inr (.inr pc)) => LinkB.instruction frameStack frameLabel (SemiprimeD1StackFrame.code pc)
  | .inl .start => .call (metaLabel (.inl .start)) (.inl .ready)
  | .inl .ready => .call (copyLabel false 0) (.inl .copyIndex)
  | .inl .copyIndex => .call (copyLabel true 0) (.inl .emit)
  | .inl .emit => .call (frameLabel 0) (.inl .check)
  | .inl .check => .base (.pop (.inl .squareWork) (.inl .halt) (.inl .dec) (.inl .dec))
  | .inl .dec => .base (.pop (.inl .thresholdWork) (.inl .emit) (.inl .emit) (.inl .emit))
  | .inl .halt => .base .halt
/-- Fixed finite original-input machine. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (.inl .input) (.inr false) (.inl .start) program
/-- The only supplied input is original binary N. -/
def input (bits:List Bool) : Stack→List Bool := Sum.elim (Meta.input bits) (fun _=>[])
/-- Actual unprepared initial state. -/
def initial (bits:List Bool) : C.State Stack Label := ⟨some (.inl .start),none,none,input bits,[]⟩
/-- Both Copy operands are pairwise disjoint. -/
theorem copyStack_injective (mode:Bool) : Function.Injective (copyStack mode) := by cases mode <;> decide
/-- The Frame operand map is injective. -/
theorem frameStack_injective : Function.Injective frameStack := by decide
/-- Thirteen fixed Boolean data stacks. -/
theorem stack_card : Fintype.card Stack=13 := by decide
/-- One hundred thirty-five fixed control labels. -/
theorem label_card : Fintype.card Label=135 := by decide
/-- All alphabets are finite, including every return-tag symbol. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite (.inl .input) (.inr false) (.inl .start) program
end RiemannGaussian.SemiprimeD1StackGraphIndices
