/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootNetworkRowsOriginal
import RiemannGaussian.SemiprimeD1StackSourceOccurrencesOriginal
/-! # Original binary N acquires the complete compact occurrence-key stream
The real1852-role source acquires original rows/n/F/M once. Its actual rows and
actual n word directly alias the only two inputs to the real21-role occurrence
source. All source caches, all occurrence helpers and both unused input shadows
are included in the fixed allocation. No graph, owner or key supplier enters.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootSourceOccurrences
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace R
export SemiprimeD1StackRootNetworkRows (Stack Label program input initial initialPrefix originalInput output)
export SemiprimeD1StackRootNetworkRowsExecution (done)
end R
namespace Q
export SemiprimeD1StackSourceOccurrences (Stack Label program)
end Q
namespace A
export SemiprimeD1StackRootNetworkRowsOriginal (leftCount)
/-- Actual n is a retained old source role, distinct from the acquired row output. -/
theorem count_ne_output :leftCount≠R.output :=by decide
end A
/-- Both complete source banks, including both allocated unused occurrence-input shadows. -/
abbrev Stack :=R.Stack⊕Q.Stack
/-- Every actual original-N source/cache word is physically retained. -/
def rootStack :R.Stack→Stack :=Sum.inl
/-- Only the actual original row/count inputs share their real acquired source addresses. -/
def occurrenceStack :Q.Stack→Stack
  | .rows=>rootStack R.output
  | .number=>rootStack A.leftCount
  | k=>.inr k
/-- Static inverse on every actual mapped occurrence role. -/
def occurrenceInverse :Stack→Q.Stack
  | .inl k=>if k=R.output then .rows else .number
  | .inr k=>k
/-- Both allocated shared-input shadows are EMPTY; every used private source word remains literal. -/
def privateView (out:Q.Stack→List Bool) :Q.Stack→List Bool
  | .rows|.number=>[]
  | k=>out k
/-- Exact old root bank and real private occurrence bank, with actual shared operands retained in the root. -/
def data (root:R.Stack→List Bool) (out:Q.Stack→List Bool) :Stack→List Bool :=Sum.elim root (privateView out)
/-- Both original-input front doors continue at the same actual occurrence source call. -/
inductive Control where | start | prescribed | occurrences | done deriving DecidableEq
instance :Fintype Control :=Fintype.ofList [.start,.prescribed,.occurrences,.done] (by intro k;cases k <;> simp)
/-- All actual source and return labels are fixed finite before N. -/
abbrev Label :=Control⊕(R.Label⊕Q.Label)
/-- Actual original-source labels. -/
def rootLabel (pc:R.Label) :Label :=.inr (.inl pc)
/-- Actual physical occurrence-source labels. -/
def occurrenceLabel (pc:Q.Label) :Label :=.inr (.inr pc)
local notation "ctl" => (Sum.inl :Control→Label)
/-- One fixed program from binary N to every compact occurrence key, with both actual source calls paid. -/
def program :Label→C.Instruction Stack Label
  | .inl .start=>.call (rootLabel (.inl .start)) (ctl .occurrences)
  | .inl .prescribed=>.call (rootLabel (.inl .prescribed)) (ctl .occurrences)
  | .inl .occurrences=>.call (occurrenceLabel (.local .start)) (ctl .done)
  | .inl .done=>.base .halt
  | .inr (.inl pc)=>SemiprimeD1StackValidationLink.instruction rootStack rootLabel (R.program pc)
  | .inr (.inr pc)=>SemiprimeD1StackValidationLink.instruction occurrenceStack occurrenceLabel (Q.program pc)
/-- Original binary N alone; every derived row/count/key/helper/shadow word is initially EMPTY. -/
def input (bits:List Bool) :Stack→List Bool :=data (R.input bits) (fun _=>[])
/-- Genuine sole-original-input front door. -/
def initial (bits:List Bool) :C.State Stack Label :=⟨some (ctl .start),none,none,input bits,[]⟩
/-- Actual caller-prescription front door, without supplied graph/count/owner/key metadata. -/
def initialPrefix (bits pre:List Bool) :C.State Stack Label :=
  ⟨some (ctl .prescribed),none,none,data (R.initialPrefix bits pre).data (fun _=>[]),[]⟩
/-- Genuine original binary-N input address. -/
def originalInput :Stack :=rootStack R.originalInput
/-- Actual acquired compact ordered owner/factor occurrence-key stream. -/
def output :Stack :=occurrenceStack .output
/-- One fixed finite1873-role original-input machine, counting both real banks and both unused shadows. -/
def machine :Turing.FinTM2 :=SemiprimeD1StackCalls.machine originalInput output (ctl .start) program
/-- Exact inverse on every actual occurrence role. -/
theorem occurrence_inverse (k:Q.Stack) :occurrenceInverse (occurrenceStack k)=k :=by
  cases k
  · rfl
  · simp only [occurrenceStack,rootStack,occurrenceInverse,A.count_ne_output,ite_false]
  all_goals rfl
/-- Sharing actual acquired row/count bytes does not alias any distinct source operands. -/
theorem occurrence_injective :Function.Injective occurrenceStack :=by
  intro a b h
  have he:=congrArg occurrenceInverse h
  simpa only [occurrence_inverse] using he
/-- Every1873allocated data word, including both unused input shadows, is counted. -/
theorem stack_card :Fintype.card Stack=1873 :=by
  rw [Fintype.card_sum,SemiprimeD1StackRootNetworkRows.stack_card,SemiprimeD1StackSourceOccurrences.stack_card]
/-- Control contains only finite Boolean/read/return flags. -/
theorem control_finite :Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- All1873data and actual return alphabets are fixed finite before every original N. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackRootSourceOccurrences
