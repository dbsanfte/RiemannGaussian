/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexCatalogue
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace

/-! # Actual complete-catalogue component calls
The public acquisition and cached-digit scan are physically included with
real continuation frames. No cache/count/limit result is a caller answer.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 4096
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVertexCatalogueComponents
open SemiprimeD1StackVertexCatalogue
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeD1VertexCatalogueModes (Mode Role)

/-- The actual public payload embedding is injective. -/
theorem rootStack_injective : Function.Injective rootStack := Sum.inl_injective
/-- The actual Cartesian store embedding is injective. -/
theorem kernelStack_injective : Function.Injective kernelStack := by
  intro a b h
  simpa only [kernelStack,Sum.inr.injEq,Sum.inl.injEq] using h
/-- Counting aliases only its bank, with every other physical role separate. -/
theorem countStack_injective : Function.Injective countStack := by
  intro a b h
  cases a <;> cases b <;> simp_all [countStack,rootStack]

/-- Readonly source roles never alias an engine limit/index/record word. -/
theorem role_not_kernel (role:Role) (k:Kernel.Stack) : roleStack role≠kernelStack k := by
  cases role <;> simp [roleStack,originalRadius,rootStack,cacheStack,countStack,kernelStack]
/-- Every readonly source is separate from the actual outer Copy scratch. -/
theorem role_not_scratch (role:Role) : roleStack role≠scratchStack := by
  cases role <;> simp [roleStack,originalRadius,rootStack,cacheStack,countStack,scratchStack]
/-- Each concrete outer Copy has disjoint source and destination. -/
theorem copy_input_output (kind:CopyKind) : copyInput kind≠copyOutput kind := by
  cases kind with
  | radiusSucc => simp [copyInput,copyOutput,originalRadius,rootStack,cacheStack]
  | digitsPred => simp [copyInput,copyOutput,countStack,cacheStack]
  | limit mode axis => exact role_not_kernel _ _
/-- Each concrete outer Copy source is separate from scratch. -/
theorem copy_input_scratch (kind:CopyKind) : copyInput kind≠scratchStack := by
  cases kind with
  | radiusSucc => simp [copyInput,originalRadius,rootStack,scratchStack]
  | digitsPred => simp [copyInput,countStack,scratchStack]
  | limit mode axis => exact role_not_scratch _
/-- Each concrete outer Copy destination is separate from scratch. -/
theorem copy_output_scratch (kind:CopyKind) : copyOutput kind≠scratchStack := by
  cases kind <;> simp [copyOutput,cacheStack,kernelStack,scratchStack]
/-- The source/destination/scratch map really is a three-stack inclusion. -/
theorem copyStack_injective (kind:CopyKind) : Function.Injective (copyStack kind) := by
  have h0:=copy_input_output kind
  have h1:=copy_input_scratch kind
  have h2:=copy_output_scratch kind
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [copyStack]

/-- Exact actual outer Copy projection. -/
theorem copy_input (kind:CopyKind) (data:Stack→List Bool) (ht:data scratchStack=[]) :
    LinkB.DataRel (copyStack kind) data
      (SemiprimeD1StackCopy.payload (data (copyInput kind)) (data (copyOutput kind)) []) data := by
  constructor
  · intro k;fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.payload,ht]
  · intro k _;rfl
/-- Returning Copy data preserve every original cache and auxiliary word. -/
theorem copy_output (kind:CopyKind) (data:Stack→List Bool) (ht:data scratchStack=[]) :
    LinkB.DataRel (copyStack kind) data
      (SemiprimeD1StackCopy.payload (data (copyInput kind)) (data (copyInput kind)++data (copyOutput kind)) [])
      (Function.update data (copyOutput kind) (data (copyInput kind)++data (copyOutput kind))) := by
  have h0:=copy_input_output kind
  have h1:=copy_output_scratch kind
  constructor
  · intro k
    fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.payload,Function.update,h0,h1.symm,ht]
  · intro k hk
    have hn:k≠copyOutput kind:=by intro he;exact hk 1 he.symm
    exact Function.update_of_ne hn _ _
/-- Every limit/derived-cache copy executes the included literal Copy procedure. -/
theorem copy_call (kind:CopyKind) (data:Stack→List Bool) (ht:data scratchStack=[])
    (pc next:Label) (hc:program pc=.call (copyLabel kind 0) next) :
    Runs program (5*(data (copyInput kind)).length+4) pc data next
      (Function.update data (copyOutput kind) (data (copyInput kind)++data (copyOutput kind))) := by
  apply SemiprimeD1StackProcedureFragments.included_call program (copyStack kind) (copyLabel kind)
    (copyStack_injective kind) SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc
    (5*(data (copyInput kind)).length+3)
    (SemiprimeD1StackCopy.state 0 none (data (copyInput kind)) (data (copyOutput kind)) [])
    (SemiprimeD1StackCopy.done (data (copyInput kind)) (data (copyInput kind)++data (copyOutput kind)))
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words _ _ none
  · exact copy_input kind data ht
  · exact copy_output kind data ht

/-- Actual completed public source store, with no new cache/index answer supplied. -/
def afterRoot (bits:List Bool) : Stack→List Bool :=
  Sum.elim (SemiprimeD1BinaryPublicAcquisitionComponents.result bits) (fun _=>[])
/-- Actual completed cache count changes precisely its physical count stack. -/
def afterCount (bits:List Bool) : Stack→List Bool :=
  Function.update (afterRoot bits) (countStack .count)
    (List.replicate (SemiprimeD1StackDigitCountBounds.originalWords bits).length true)

/-- The whole original-input public producer executes ONCE inside this literal caller. -/
theorem root_call (bits:List Bool) (hb:bits≠[]) :
    ∃m≤SemiprimeD1BinaryPublicAcquisitionExecution.timeBound bits+1,
      Runs program m (.inl .acquireRoot) (input bits) (.inl .acquireCount) (afterRoot bits) := by
  obtain ⟨m,hm,hr⟩:=SemiprimeD1BinaryPublicAcquisitionExecution.source_run bits hb
  refine ⟨m+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program rootStack rootLabel rootStack_injective
    Root.program (Root.mainLabel .start) (fun _=>rfl) (.inl .acquireRoot) (.inl .acquireCount) rfl m
    (Root.initial bits) (⟨none,none,none,SemiprimeD1BinaryPublicAcquisitionComponents.result bits,[]⟩:C.State Root.Stack Root.Label)
    (input bits) (afterRoot bits)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      cases k with
      | inl k => exact False.elim (hk k rfl)
      | inr k => rfl

/-- Actual count output equals its actual input store plus one physically constructed count word. -/
theorem count_done_update (words:List (List Bool)) :
    (SemiprimeD1StackDigitCountExecution.done words).data=
      Function.update (SemiprimeD1StackDigitCountExecution.initial (SemiprimeD1TensorTapeCodec.vectorBits words)).data
        _root_.RiemannGaussian.SemiprimeD1StackDigitCount.Stack.count (List.replicate words.length true) := by
  funext k
  cases k <;> simp [SemiprimeD1StackDigitCountExecution.done,SemiprimeD1StackDigitCountExecution.initial,
    SemiprimeD1StackDigitCount.data,Function.update]

/-- The digitCount supplier actually parses the acquired bank; no count answer is passed. -/
theorem count_call (bits:List Bool) :
    Runs program (SemiprimeD1StackDigitCountExecution.totalTime (SemiprimeD1StackDigitCountBounds.originalWords bits)+1)
      (.inl .acquireCount) (afterRoot bits) (.inl .copyRadiusSucc) (afterCount bits) := by
  let words:=SemiprimeD1StackDigitCountBounds.originalWords bits
  have hin:LinkB.DataRel countStack (afterRoot bits)
      (SemiprimeD1StackDigitCountExecution.initial (SemiprimeD1TensorTapeCodec.vectorBits words)).data (afterRoot bits):=by
    constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  have hout:=SemiprimeD1StackMultiplierLink.data_update countStack countStack_injective
    (afterRoot bits) _ _ hin _root_.RiemannGaussian.SemiprimeD1StackDigitCount.Stack.count (List.replicate words.length true)
  rw [←count_done_update] at hout
  apply SemiprimeD1StackProcedureCallsTrace.included_call program countStack countLabel countStack_injective
    Count.program (.inl .main) (fun _=>rfl) (.inl .acquireCount) (.inl .copyRadiusSucc) rfl
    (SemiprimeD1StackDigitCountExecution.totalTime words)
    (SemiprimeD1StackDigitCountExecution.initial (SemiprimeD1TensorTapeCodec.vectorBits words))
    (SemiprimeD1StackDigitCountExecution.done words) (afterRoot bits) (afterCount bits)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackDigitCountExecution.acquire_run words
  · exact hin
  · exact hout
end RiemannGaussian.SemiprimeD1StackVertexCatalogueComponents
