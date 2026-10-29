/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSelectedDescriptorRecord
import RiemannGaussian.SemiprimeD1StackTransformSelectorsExecution
/-! # Real selector acquisition, physical success peek and metadata-record calls -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackSelectedDescriptorRecordComponents
open SemiprimeD1StackSelectedDescriptorRecord SemiprimeD1StackProcedureTrace
open SemiprimeD1StackStaticTableSpec (CheckerTrace)
open SemiprimeD1TensorTapeCodec (vectorBits)
variable {K L : Type} [DecidableEq K] [Fintype K] (s : T.Static K L) (sourceMap : K→Option (Fin 6))
omit [Fintype K] in
/-- Both original physical words are copied/read before actual singleton
selectors are pushed into the DIRECTLY ALIASED loader source fields. -/
theorem selector_call (oldTemplate : K→List Bool) (raw : Fin 6→List Bool)
    (tagCode : Fin 18) (trCode : Fin 3) (second : Bool)
    (htag : raw 1=List.replicate tagCode.val true) (htr : raw 2=List.replicate trCode.val true)
    (hcode : SemiprimeD1StackTransformSelectors.tagDispatch tagCode=.copyTransform second)
    (oldStage oldInverse bank hist out : List Bool) :
    Runs (program s sourceMap)
      (SemiprimeD1StackTransformSelectorsExecution.timeBound (raw 1) (raw 2) oldStage oldInverse+1)
      (.inl .start) (initial s oldTemplate raw oldStage oldInverse bank hist out).data (.inl .guard)
      (afterSelectors s oldTemplate raw second (trCode.val==2) bank hist out) :=by
  have hr:=SemiprimeD1StackTransformSelectorsExecution.source_run tagCode trCode second hcode oldStage oldInverse
  rw [←htag,←htr] at hr
  apply SemiprimeD1StackProcedureCallsTrace.included_call (program s sourceMap) selectorStack selectorLabel
    selectorStack_injective S.program .start (fun _=>rfl) (.inl .start) (.inl .guard) rfl _
    (S.initial (raw 1) (raw 2) oldStage oldInverse) (S.done (raw 1) (raw 2) second (trCode.val==2))
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk
      cases k with
      | inl k=>
        cases k with
        | inl k=>rfl
        | inr k=>
          cases k with
          | inl i=>
            fin_cases i
            · rfl
            · exact (hk SemiprimeD1StackTransformSelectors.Stack.stage rfl).elim
            · exact (hk SemiprimeD1StackTransformSelectors.Stack.inverse rfl).elim
            · rfl
            · rfl
            · rfl
          | inr k=>rfl
      | inr k=>cases k <;> rfl
omit [Fintype K] in
/-- The caller physically tests the nonempty stage singleton BEFORE entering
the loader. An aborted selector leaves it empty and takes the other branch. -/
theorem guard_run (oldTemplate : K→List Bool) (raw : Fin 6→List Bool) (second inverse : Bool)
    (bank hist out : List Bool) :
    Runs (program s sourceMap) 1 (.inl .guard) (afterSelectors s oldTemplate raw second inverse bank hist out)
      (.inl .record) (afterSelectors s oldTemplate raw second inverse bank hist out) :=by
  apply one_base (program s sourceMap) _ _ (.peek (selectorStack .stage) (.inl .abort) (.inl .record) (.inl .record)) _ _ rfl
  · cases second <;> rfl
  · rfl
/-- The actual descriptor template loader and entire record source run with
only physical acquired selector words, retaining all six original raw fields. -/
theorem descriptor_call (oldTemplate : K→List Bool) (raw : Fin 6→List Bool) (second inverse : Bool)
    (hraw : SemiprimeD1StackDescriptorRecord.selected sourceMap (fields raw [second] [inverse]) s.raw=[])
    (answer : List Bool→Bool) (budget : Nat→Nat)
    (hc : CheckerTrace s (SemiprimeD1StackDescriptorRecord.selected sourceMap (fields raw [second] [inverse])) answer budget)
    (words : List (List Bool)) (hist out : List Bool) :
    ∃t≤SemiprimeD1StackDescriptorRecordExecution.timeBound s sourceMap oldTemplate (fields raw [second] [inverse])
      words answer budget hist out,
      Runs (program s sourceMap) (t+1) (.inl .record)
        (afterSelectors s oldTemplate raw second inverse (vectorBits words) hist out) (.inl .done)
        (done s sourceMap raw second inverse words answer hist out).data :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackDescriptorRecordExecution.source_run s sourceMap oldTemplate
    (fields raw [second] [inverse]) hraw answer budget hc words hist out
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call (program s sourceMap) descriptorStack descriptorLabel
    Sum.inl_injective (D.program s sourceMap) (.inl .start) (fun _=>rfl) (.inl .record) (.inl .done) rfl t
    (SemiprimeD1StackDescriptorRecord.initial s oldTemplate (fields raw [second] [inverse]) (vectorBits words) hist out)
    (SemiprimeD1StackDescriptorRecord.done s sourceMap (fields raw [second] [inverse]) words answer hist out)
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
      | inl k=>exact (hk k rfl).elim
      | inr k=>rfl
end RiemannGaussian.SemiprimeD1StackSelectedDescriptorRecordComponents
