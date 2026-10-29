/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsView
/-! # One final paid reversal emits chronological stable heap references -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsFinish
open SemiprimeD1StackRootPhaseFreshRecords SemiprimeD1StackRootPhaseFreshRecordsEncoding
open SemiprimeD1StackRootPhaseFreshRecordsPrimitives SemiprimeD1StackRootPhaseFreshRecordsView
open SemiprimeD1StackProcedureTrace
open SemiprimeD1StackRootPhaseParametersEncoding (stream references vector_stream)
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- One actual final reversal consumes the whole history and retains all other roles. -/
theorem reverse_call (bank:Stack→List Bool) (hp:bank (aux .recordScratch)=[])
    (ht:bank (aux .refScratch)=[]) :
    Runs program (2*(bank (aux .refsHistory)).length+3) .reverseCall bank .done
      (Function.update (Function.update bank (aux .refsHistory) []) (aux .refsOutput)
        ((bank (aux .refsHistory)).reverse++bank (aux .refsOutput))) :=by
  let before:SemiprimeD1StackBytecode.State V.Stack V.Label:=
    ⟨some .reverse,none,SemiprimeD1StackVertexRecordStream.data [] [] (bank (aux .refsHistory)) (bank (aux .refsOutput))⟩
  let after:SemiprimeD1StackBytecode.State V.Stack V.Label:=
    ⟨none,none,SemiprimeD1StackVertexRecordStream.data [] [] [] ((bank (aux .refsHistory)).reverse++bank (aux .refsOutput))⟩
  have hin:Link.DataRel reverseStack bank before.store bank:=by
    constructor
    · intro k;cases k
      · exact hp
      · exact ht
      · rfl
      · rfl
    · intro k _;rfl
  apply included_call program reverseStack Label.reverse reverse_injective V.code .reverse (fun _=>rfl)
    .reverseCall .done rfl (2*(bank (aux .refsHistory)).length+2) before after _ _ rfl rfl
    (SemiprimeD1StackVertexRecordStream.reverse_run _ [] [] _ none) hin
  have h0:=Link.data_update reverseStack reverse_injective bank before.store bank hin .history []
  have h1:=Link.data_update reverseStack reverse_injective bank _ _ h0 .output
    ((bank (aux .refsHistory)).reverse++bank (aux .refsOutput))
  have he:Function.update (Function.update before.store .history []) .output
      ((bank (aux .refsHistory)).reverse++bank (aux .refsOutput))=after.store:=by
    funext k;cases k <;> rfl
  simpa only [he,reverseStack] using h1
/-- Final real output seed and ONE actual reverse restore original allocation
order. Every phase word and row-local scratch stays physically clear. -/
theorem finish_run (root:R.Stack→List Bool) (cached:List (List Bool)) :
    Runs program (2*(stream (references cached.length)).length+4) .finishSeed
      (loop root [] (SemiprimeD1StackHeapAllocate.heapBytes cached) cached.length (stream (references cached.length)).reverse)
      .done (finished root cached) :=by
  let bank:=loop root [] (SemiprimeD1StackHeapAllocate.heapBytes cached) cached.length (stream (references cached.length)).reverse
  let seeded:=view root (cacheInput root [] [false])
    (work [] [] (SemiprimeD1StackHeapAllocate.heapBytes cached)
      (List.replicate cached.length true) [] (stream (references cached.length)).reverse [false])
  have h0:Runs program 1 .finishSeed bank .reverseCall seeded:=by
    apply one_base program _ _ (.push output false .reverseCall) _ _ rfl
    · rfl
    · exact update_output _ _ _ _ _ _ _ _ _ _
  have h1:=reverse_call seeded rfl rfl
  have he:Function.update (Function.update seeded (aux .refsHistory) []) (aux .refsOutput)
      ((seeded (aux .refsHistory)).reverse++seeded (aux .refsOutput))=finished root cached:=by
    dsimp only [seeded]
    rw [update_history,update_output]
    change view root (cacheInput root [] [false])
      (work [] [] (SemiprimeD1StackHeapAllocate.heapBytes cached)
        (List.replicate cached.length true) [] [] ((stream (references cached.length)).reverse.reverse++[false]))=finished root cached
    rw [List.reverse_reverse,←vector_stream]
    rfl
  rw [he] at h1
  have hh:=compose h0 h1
  change Runs program (1+(2*(stream (references cached.length)).reverse.length+3)) .finishSeed bank .done (finished root cached) at hh
  simpa only [List.length_reverse,show 1+(2*(stream (references cached.length)).length+3)=2*(stream (references cached.length)).length+4 by omega] using hh
end RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsFinish
