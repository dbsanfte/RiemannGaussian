/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootOwnerIndexCoordinates
import RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexOriginal
/-! # Original-binary-N root records and actual occurrence-to-owner index
The real1804-role record source runs once. Its complete output and its already
acquired unary LEFT count E alias the two actual inputs of the real17-role index
source. No graph, left count, owner map or record tape is supplied externally.
The standard entry accepts N alone; the second entry accepts the caller's actual
physical prescription/tail. Both source banks and both unused input shadows are
included in the allocated inventory.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootOwnerIndex
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace R
export SemiprimeD1StackRootNetworkRecords (Stack Label program input initial initialPrefix originalInput output)
export SemiprimeD1StackRootNetworkRecordsExecution (done)
end R
namespace I
export SemiprimeD1StackNetworkOwnerIndex (Stack Label program initial)
end I
namespace A
export SemiprimeD1StackRootOwnerIndexCoordinates (leftCount count_ne_output)
end A
/-- Both complete banks, including the two allocated unused index-input shadows. -/
abbrev Stack :=R.Stack⊕I.Stack
/-- Every actual root record/count/source role remains physically present. -/
def rootStack :R.Stack→Stack :=Sum.inl
/-- Only the real record and retained-left-count operands are shared across the two actual sources. -/
def indexStack :I.Stack→Stack
  | .vertices=>rootStack R.output
  | .leftCount=>rootStack A.leftCount
  | k=>.inr k
/-- Static inverse distinguishes the two actual shared source words. -/
def indexInverse :Stack→I.Stack
  | .inl k=>if k=R.output then .vertices else .leftCount
  | .inr k=>k
/-- Both allocated input shadows remain EMPTY; every used index work/output word is retained literally. -/
def privateView (index:I.Stack→List Bool) :I.Stack→List Bool
  | .vertices|.leftCount=>[]
  | k=>index k
/-- Exact root and private-index bank view; all source data remain on real Boolean tapes. -/
def data (root:R.Stack→List Bool) (index:I.Stack→List Bool) :Stack→List Bool :=Sum.elim root (privateView index)
/-- Literal standard/prefix source calls, index call and final halt. -/
inductive Control where | start | prescribed | index | done deriving DecidableEq
instance :Fintype Control :=Fintype.ofList [.start,.prescribed,.index,.done] (by intro k;cases k <;> simp)
/-- Actual fixed return labels, independent of N and every acquired row/count. -/
abbrev Label :=Control⊕(R.Label⊕I.Label)
/-- Actual included complete-record source label. -/
def rootLabel (pc:R.Label) :Label :=.inr (.inl pc)
/-- Actual included physical owner-index source label. -/
def indexLabel (pc:I.Label) :Label :=.inr (.inr pc)
local notation "ctl" => (Sum.inl :Control→Label)
/-- One fixed parameterless finite program from binary N to the original physical owner index. -/
def program :Label→C.Instruction Stack Label
  | .inl .start=>.call (rootLabel (.inl .start)) (ctl .index)
  | .inl .prescribed=>.call (rootLabel (.inl .main)) (ctl .index)
  | .inl .index=>.call (indexLabel (.local .start)) (ctl .done)
  | .inl .done=>.base .halt
  | .inr (.inl pc)=>SemiprimeD1StackValidationLink.instruction rootStack rootLabel (R.program pc)
  | .inr (.inr pc)=>SemiprimeD1StackValidationLink.instruction indexStack indexLabel (I.program pc)
/-- Standard actual input is N alone; count/records/index/shadows are initially empty. -/
def input (bits:List Bool) :Stack→List Bool :=data (R.input bits) (fun _=>[])
/-- Genuine original-N-only front door. -/
def initial (bits:List Bool) :C.State Stack Label :=⟨some (ctl .start),none,none,input bits,[]⟩
/-- Actual caller-prefix entry accepts only N and its real prescription bytes, not a derived graph/count. -/
def initialPrefix (bits pre:List Bool) :C.State Stack Label :=
  ⟨some (ctl .prescribed),none,none,data (R.initialPrefix bits pre).data (fun _=>[]),[]⟩
/-- Original binary-N address remains the designated sole ordinary input. -/
def originalInput :Stack :=rootStack R.originalInput
/-- Actual acquired owner-index catalogue, at its real private source output address. -/
def output :Stack :=indexStack .output
/-- Genuine fixed finite1821-role original-input machine. -/
def machine :Turing.FinTM2 :=SemiprimeD1StackCalls.machine originalInput output (ctl .start) program
/-- Static index source mapping has an exact inverse on every used role. -/
theorem index_inverse (k:I.Stack) :indexInverse (indexStack k)=k :=by
  cases k
  · rfl
  · simp only [indexStack,rootStack,indexInverse,A.count_ne_output,ite_false]
  all_goals rfl
/-- Sharing the actual original record/count words preserves distinctness of every source operand. -/
theorem index_injective :Function.Injective indexStack :=by
  intro a b h
  have he:=congrArg indexInverse h
  simpa only [index_inverse] using he
/-- Every1821allocated physical word, including both unused shared-input shadows, is counted. -/
theorem stack_card :Fintype.card Stack=1821 :=by
  rw [Fintype.card_sum,SemiprimeD1StackRootNetworkRecords.stack_card,SemiprimeD1StackNetworkOwnerIndex.stack_card]
/-- Only finite Boolean read flags and real fixed return labels enter runtime control. -/
theorem control_finite :Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- All1821data and actual-return alphabets are fixed finite before original N. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackRootOwnerIndex
