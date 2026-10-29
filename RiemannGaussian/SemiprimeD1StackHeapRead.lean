/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMultiplierLink
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode

/-! # Fixed finite unary-reference heap dereference
The original heap, allocation counter and reference are preserved by actual
included copy loops. Local Boolean-stack scans acquire the newest-first depth.
Every skipped and selected record is parsed by the actual included field code.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackHeapRead
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace Link
export SemiprimeD1StackMultiplierLink (instruction DataRel data_initial data_unique Rel run_rel)
end Link
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label active code initial final)
end Field

/-- Ten fixed Boolean data stacks, independent of every heap/address. -/
inductive Stack where
  | heap | counter | reference | reader | depth | referenceWork | temporary
  | fieldScratch | output | valid
  deriving DecidableEq,Repr

/-- Fixed literal stack catalogue. -/
instance : Fintype Stack where
  elems:={.heap,.counter,.reference,.reader,.depth,.referenceWork,.temporary,.fieldScratch,.output,.valid}
  complete:=by intro k;cases k <;> simp

/-- Fixed local scan/clear/call labels. -/
inductive Local where
  | start | afterHeap | afterCounter | afterReference | referenceLoop | referenceStep
  | scan | skipCall | afterSkip | clearSkipped | finalCall | afterFinal
  | clearReader | halt | bad
  deriving DecidableEq,Repr

/-- Fixed literal local-control catalogue. -/
instance : Fintype Local where
  elems:={.start,.afterHeap,.afterCounter,.afterReference,.referenceLoop,.referenceStep,.scan,
    .skipCall,.afterSkip,.clearSkipped,.finalCall,.afterFinal,.clearReader,.halt,.bad}
  complete:=by intro k;cases k <;> simp

/-- Actual copy instances and field labels are static finite code names. -/
abbrev Label := Local⊕((Fin 3×Fin 9)⊕Field.Label)

/-- Source stack of the three actual copy procedures. -/
def copyInput (mode:Fin 3) : Stack :=
  if mode=0 then .heap else if mode=1 then .counter else .reference

/-- Destination stack of each actual copy procedure. -/
def copyOutput (mode:Fin 3) : Stack :=
  if mode=0 then .reader else if mode=1 then .depth else .referenceWork

/-- Literal included Copy operand mapping. -/
def copyStack (mode:Fin 3) (k:Fin 3) : Stack :=
  if k=0 then copyInput mode else if k=1 then copyOutput mode else .temporary

/-- Literal included Copy code-label mapping. -/
def copyLabel (mode:Fin 3) (pc:Fin 9) : Label := .inr (.inl (mode,pc))

/-- Literal included field parser operand mapping. -/
def fieldStack : Field.Stack→Stack
  | .inl .input => .reader
  | .inl .scratch => .fieldScratch
  | .inl .output => .output
  | .inr _ => .valid

/-- Literal included parser code-label mapping. -/
def fieldLabel (pc:Field.Label) : Label := .inr (.inr pc)

/-- Actual fixed instruction table, containing the component instructions themselves. -/
def program : Label→C.Instruction Stack Label
  | .inr (.inl (mode,pc)) => Link.instruction (copyStack mode) (copyLabel mode) (SemiprimeD1StackCopy.code pc)
  | .inr (.inr pc) => Link.instruction fieldStack fieldLabel (Field.code pc)
  | .inl .start => .call (copyLabel 0 0) (.inl .afterHeap)
  | .inl .afterHeap => .call (copyLabel 1 0) (.inl .afterCounter)
  | .inl .afterCounter => .call (copyLabel 2 0) (.inl .afterReference)
  | .inl .afterReference => .base (.pop .depth (.inl .bad) (.inl .referenceLoop) (.inl .referenceLoop))
  | .inl .referenceLoop => .base (.pop .referenceWork (.inl .scan) (.inl .referenceStep) (.inl .referenceStep))
  | .inl .referenceStep => .base (.pop .depth (.inl .bad) (.inl .referenceLoop) (.inl .referenceLoop))
  | .inl .scan => .base (.pop .depth (.inl .finalCall) (.inl .skipCall) (.inl .skipCall))
  | .inl .skipCall => .call (fieldLabel (Field.active .tagPop (none,false))) (.inl .afterSkip)
  | .inl .afterSkip => .base (.pop .valid (.inl .bad) (.inl .bad) (.inl .clearSkipped))
  | .inl .clearSkipped => .base (.pop .output (.inl .scan) (.inl .clearSkipped) (.inl .clearSkipped))
  | .inl .finalCall => .call (fieldLabel (Field.active .tagPop (none,false))) (.inl .afterFinal)
  | .inl .afterFinal => .base (.peek .valid (.inl .bad) (.inl .bad) (.inl .clearReader))
  | .inl .clearReader => .base (.pop .reader (.inl .halt) (.inl .clearReader) (.inl .clearReader))
  | .inl .halt => .base .halt
  | .inl .bad => .base .halt

/-- One fixed actual machine: ten Boolean stacks and one fixed finite return alphabet. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine Stack.heap Stack.output (.inl .start) program

/-- Actual prepared dereference data; all work/output stacks start empty. -/
def input (heap counter reference:List Bool) : Stack→List Bool
  | .heap => heap
  | .counter => counter
  | .reference => reference
  | _ => []

/-- Actual source start with no preloaded continuation. -/
def initial (heap counter reference:List Bool) : C.State Stack Label :=
  ⟨some (.inl .start),none,none,input heap counter reference,[]⟩

/-- Readable protocol state ignores only transient finite read flags. -/
def At (pc:Label) (data:Stack→List Bool) (frames:List Label) (state:C.State Stack Label) : Prop :=
  state.pc=some pc ∧ state.data=data ∧ state.frames=frames

/-- An actually executed fixed-program fragment, retaining every outer return frame. -/
def Runs (time:ℕ) (pc:Label) (data:Stack→List Bool) (next:Label) (out:Stack→List Bool) : Prop :=
  ∀frames state,At pc data frames state→
    ∃finish,C.run program time state=some finish ∧ At next out frames finish

/-- Successful fragment certificates compose actual iterated transitions. -/
theorem Runs.trans {m n:ℕ} {pc mid next:Label} {data work out:Stack→List Bool}
    (h:Runs m pc data mid work) (g:Runs n mid work next out) : Runs (m+n) pc data next out := by
  intro frames state hs
  obtain ⟨temp,ht,hs⟩:=h frames state hs
  obtain ⟨finish,hf,hout⟩:=g frames temp hs
  refine ⟨finish,?_,hout⟩
  rw [SemiprimeD1StackReturnLink.run_add,ht,Option.bind_some,hf]

/-- Empty actual execution fragment. -/
theorem Runs.refl (pc:Label) (data:Stack→List Bool) : Runs 0 pc data pc data := by
  intro frames state h
  exact ⟨state,rfl,h⟩

/-- The three copy instances use distinct actual operand stacks. -/
theorem copyStack_injective (mode:Fin 3) : Function.Injective (copyStack mode) := by
  fin_cases mode <;> decide

/-- Parser reader/scratch/output/flag operands are four distinct actual stacks. -/
theorem fieldStack_injective : Function.Injective fieldStack := by decide
/-- The complete dereference data has ten fixed Boolean stacks. -/
theorem stack_card : Fintype.card Stack=10 := by decide

/-- All local/copy/parser labels total 97, independent of every input heap. -/
theorem label_card : Fintype.card Label=97 := by decide

/-- Every stack alphabet, including the actual fixed return-tag alphabet, is finite. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite Stack.heap Stack.output (.inl .start) program
end RiemannGaussian.SemiprimeD1StackHeapRead
