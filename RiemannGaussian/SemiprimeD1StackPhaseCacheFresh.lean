/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseBankRestoreBounds
import RiemannGaussian.SemiprimeD1StackPhaseChildContextFreshOriginal
/-! # Actual phase-heap dereference and cached-phase fresh-generator acquisition
The only physical inputs are heap/counter/issued-reference and the old UNARY-axis
header. Fresh's complete48-role P48 bank aliases the REAL restored bank directly.
All other Fresh fields are private; the48 allocated shadow slots remain EMPTY.
No geometry/metadata/P arithmetic is replayed and no decoded bank is an operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPhaseCacheFresh
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace R
export SemiprimeD1StackPhaseBankRestore (Stack Label program phaseStack heapStack)
end R
namespace F
export SemiprimeD1StackPhaseChildContextFresh (Stack Label program contextStack aux)
end F
namespace H
export SemiprimeD1StackPhaseChildContext (Stack phaseStack oldStack childStack store oldInput emptyContext)
end H
namespace P
export SemiprimeD1StackPhaseWorkingPrecision (Stack)
end P
namespace Heap
export SemiprimeD1StackHeapRead (Stack input)
end Heap
/-- All58 real restore roles and85 allocated fresh roles, including48 unused shadow slots. -/
abbrev Stack :=R.Stack⊕F.Stack
/-- Whole58-role actual heap reader/field restorer inclusion. -/
def restoreStack :R.Stack→Stack :=Sum.inl
/-- Direct48-role alias; every other Fresh field keeps its own private physical word. -/
def freshStack :F.Stack→Stack
  | .inl (.inl k)=>restoreStack (R.phaseStack k)
  | k=>.inr k
/-- Literal inverse on actual mapped Fresh roles; unused heap-only values are irrelevant. -/
def freshInverse :Stack→F.Stack
  | .inl (.inl k)=>.inl (.inl k)
  | .inr k=>k
  | _=>F.aux .output
/-- Erase every unused private P48 shadow while retaining the actual other Fresh words. -/
def privateView (f:F.Stack→List Bool) :F.Stack→List Bool
  | .inl (.inl _)=>[]
  | k=>f k
/-- Literal physical bank view: shared phase bank, retained heap reader, and private Fresh fields. -/
def data (heap:Heap.Stack→List Bool) (fresh:F.Stack→List Bool) :Stack→List Bool
  | .inl (.inl k)=>fresh (F.contextStack (H.phaseStack k))
  | .inl (.inr k)=>heap k
  | .inr k=>privateView fresh k
/-- Actual original old-header input and otherwise empty Fresh context/allocator tapes. -/
def freshReadyBank (phase:P.Stack→List Bool) (axes:List Bool) :F.Stack→List Bool :=
  SemiprimeD1StackPhaseChildContextFresh.store
    (H.store phase (H.oldInput axes) H.emptyContext [] []) [] [] [] [] []
/-- Only actual heap/counter/issued-reference/header bytes enter the whole consumer. -/
def input (heap counter reference axes:List Bool) :Stack→List Bool :=
  data (Heap.input heap counter reference) (freshReadyBank (fun _=>[]) axes)
/-- Fixed two-call control independent of every original N, phase, context, rank or precision. -/
inductive Control where | start | fresh | done deriving DecidableEq
instance :Fintype Control :=Fintype.ofList [.start,.fresh,.done] (by intro k;cases k <;> simp)
/-- Actual finite real return labels contain only fixed component control. -/
abbrev Label :=Control⊕(R.Label⊕F.Label)
/-- Real restorer control inclusion. -/
def restoreLabel (pc:R.Label) :Label :=.inr (.inl pc)
/-- Real cached-fresh control inclusion. -/
def freshLabel (pc:F.Label) :Label :=.inr (.inr pc)
local notation "ctl" => (Sum.inl : Control→Label)
/-- REAL heap/48field restore→REAL actualP48cache Fresh entry→halt. -/
def program :Label→C.Instruction Stack Label
  | .inl .start=>.call (restoreLabel (.inl .start)) (ctl .fresh)
  | .inl .fresh=>.call (freshLabel .phaseReady) (ctl .done)
  | .inl .done=>.base .halt
  | .inr (.inl pc)=>SemiprimeD1StackValidationLink.instruction restoreStack restoreLabel (R.program pc)
  | .inr (.inr pc)=>SemiprimeD1StackValidationLink.instruction freshStack freshLabel (F.program pc)
/-- Whole source accepts no decoded phase/context/vector/rank/clock payload. -/
def initial (heap counter reference axes:List Bool) :C.State Stack Label :=
  ⟨some (ctl .start),none,none,input heap counter reference axes,[]⟩
/-- Actual designated physical heap source. -/
def originalInput :Stack :=restoreStack (R.heapStack .heap)
/-- Actual full fresh coefficient-vector output tape. -/
def output :Stack :=freshStack (F.aux .output)
/-- One fixed finite143-role machine, before all heap/phase/original-input data. -/
def machine :Turing.FinTM2 :=SemiprimeD1StackCalls.machine originalInput output (ctl .start) program
/-- The shared48phasebank is direct, with no copy or physical address reconstruction. -/
theorem phase_alias (k:P.Stack) :freshStack (F.contextStack (H.phaseStack k))=restoreStack (R.phaseStack k) :=rfl
/-- Every actually used Fresh role has its own distinct actual source/destination word. -/
theorem fresh_inverse (k:F.Stack) :freshInverse (freshStack k)=k :=by
  rcases k with k|k
  · rcases k with k|k <;> rfl
  · rfl
/-- Aliasing only identifies the intended SAME logical P48 role across the two real calls. -/
theorem fresh_injective :Function.Injective freshStack :=by
  intro a b h
  have he:=congrArg freshInverse h
  simpa only [fresh_inverse] using he
/-- Every restore role is physically distinct. -/
theorem restore_injective :Function.Injective restoreStack :=Sum.inl_injective
/-- Literal full allocated inventory includes every48unused P48 shadow slot. -/
theorem stack_card :Fintype.card Stack=143 :=by
  rw [Fintype.card_sum,SemiprimeD1StackPhaseBankRestore.stack_card,SemiprimeD1StackPhaseChildContextFresh.stack_card]
/-- No original N/phase/rank/precision/bank function occurs in the finite control. -/
theorem control_finite :Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every143role alphabet and actual real-return alphabet is fixed finite. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackPhaseCacheFresh
