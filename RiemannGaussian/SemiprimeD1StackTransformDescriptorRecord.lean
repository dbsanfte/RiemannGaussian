/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSelectedDescriptorRecordBounds
import RiemannGaussian.SemiprimeD1StackTransformSelectorsOriginal
import RiemannGaussian.SemiprimeD1StackPublicTransformRecordOriginal
import RiemannGaussian.SemiprimeD1StackPublicTransformRecordClock
/-! # Actual450-role transform descriptor, physical stage/inverse and entire row
Only original acquired fields/scope and charged dirty words are supplied.
Both singleton flags are pushed by bounded physical source decoding before
the actual complete template/table/serializer/logger source is called.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackTransformDescriptorRecord
namespace I
export SemiprimeD1StackPublicTransformTable (static inputTemplate)
end I
namespace P
export SemiprimeD1StackPublicTransformTable.P (inputRole second inverse assignment)
end P
namespace G
export SemiprimeD1StackSelectedDescriptorRecord (descriptorStack selectorStack rawSource history output fields)
end G
namespace T
export SemiprimeD1StackPublicTransformTableTrace (answer budget actual_trace)
end T
/-- Fixed actual204-role complete transform checker. -/
abbrev Checker :=SemiprimeD1StackPublicTransform.Stack
/-- Static map ONLY N0 and the two ACTUALLY CONSTRUCTED singleton selectors1/2. -/
def sourceMap (k : Checker) : Option (Fin 6) :=
  if k=P.inputRole then some 0 else if k=P.second then some 1 else if k=P.inverse then some 2 else none
/-- All450 physical words, including every dormant loader/selector/record shadow. -/
abbrev Stack :=SemiprimeD1StackSelectedDescriptorRecord.Stack Checker
/-- All actual nested copy/load/checker/serializer/logger/return labels. -/
abbrev Label :=SemiprimeD1StackSelectedDescriptorRecord.Label SemiprimeD1StackPublicTransform.Label I.static.roles.length
/-- One literal fixed program, independent of original N and every descriptor value. -/
def program : Label→SemiprimeD1StackCalls.Instruction Stack Label :=
  SemiprimeD1StackSelectedDescriptorRecord.program I.static sourceMap
/-- Only actual original words/scope, caller accumulators and paid dirty words. -/
def initial (oldTemplate : Checker→List Bool) (raw : Fin 6→List Bool)
    (oldStage oldInverse bank hist out : List Bool) : SemiprimeD1StackCalls.State Stack Label :=
  SemiprimeD1StackSelectedDescriptorRecord.initial I.static oldTemplate raw oldStage oldInverse bank hist out
/-- Same genuine finite machine before every original N and descriptor. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackSelectedDescriptorRecord.machine I.static sourceMap
/-- Literal original constructor code corresponding to the PROOF-side stage flag. -/
def tagCode (second : Bool) : Fin 18 :=if second then 3 else 1
/-- Both literal original stage entries have the actual physical dispatch. -/
theorem tag_dispatch (second : Bool) : SemiprimeD1StackTransformSelectors.tagDispatch (tagCode second)=.copyTransform second :=by
  cases second <;> rfl
/-- Complete physical role count, including all alias shadows. -/
theorem stack_card : Fintype.card Stack=450 :=by
  rw [SemiprimeD1StackSelectedDescriptorRecord.stack_card,SemiprimeD1StackPublicTransform.stack_card]
/-- Selected ACTUAL source words equal exactly the frozen original initialization:
N and two singleton flags, every source/cache/count/assignment/verdict empty. -/
theorem selected_template (raw : Fin 6→List Bool) (second inverse : Bool) :
    SemiprimeD1StackDescriptorRecord.selected sourceMap (G.fields raw [second] [inverse])=
      I.inputTemplate (raw 0) second inverse :=by
  funext k
  rw [SemiprimeD1StackPublicTransformTableTrace.template_only]
  change (if k=P.inputRole then some 0 else if k=P.second then some 1 else if k=P.inverse then some 2 else none).elim []
    (G.fields raw [second] [inverse])=_
  by_cases hn:k=P.inputRole
  · subst k;rfl
  · by_cases hs:k=P.second
    · subst k;rfl
    · by_cases hi:k=P.inverse
      · subst k;rfl
      · simp only [hn,hs,hi,ite_false];rfl
/-- Actual final state after both acquired selectors and the complete original row source. -/
def done (raw : Fin 6→List Bool) (second inverse : Bool) (words : List (List Bool)) (hist out : List Bool) :
    SemiprimeD1StackCalls.State Stack Label :=
  SemiprimeD1StackSelectedDescriptorRecord.done I.static sourceMap raw second inverse words
    (T.answer (raw 0) second inverse) hist out
/-- Complete own source clock; stage/inverse are proof-side output notation only. -/
def timeBound (oldTemplate : Checker→List Bool) (raw : Fin 6→List Bool) (second inverse : Bool)
    (words : List (List Bool)) (oldStage oldInverse hist out : List Bool) : Nat :=
  SemiprimeD1StackSelectedDescriptorRecordExecution.timeBound I.static sourceMap oldTemplate raw second inverse words
    (T.answer (raw 0) second inverse) (T.budget (raw 0)) oldStage oldInverse hist out
/-- Actual complete source. Both selectors are derived from the original raw
constructor/coord0 bytes; no generic checker or selector supplier remains. -/
theorem source_run (oldTemplate : Checker→List Bool) (raw : Fin 6→List Bool) (second : Bool) (code : Fin 3)
    (htag : raw 1=List.replicate (tagCode second).val true) (htr : raw 2=List.replicate code.val true)
    (hc : SemiprimeSourceCompactBits.Compact (raw 0)) (hN : 0<SemiprimeBitArithmetic.bitValue (raw 0))
    (words : List (List Bool)) (oldStage oldInverse hist out : List Bool) :
    ∃t≤timeBound oldTemplate raw second (code.val==2) words oldStage oldInverse hist out,
      SemiprimeD1StackCalls.run program t (initial oldTemplate raw oldStage oldInverse
        (SemiprimeD1TensorTapeCodec.vectorBits words) hist out)=some (done raw second (code.val==2) words hist out) :=by
  apply SemiprimeD1StackSelectedDescriptorRecordExecution.source_run I.static sourceMap oldTemplate raw
    (tagCode second) code second htag htr (tag_dispatch second)
  · rw [selected_template];rfl
  · rw [selected_template]
    exact T.actual_trace (raw 0) second (code.val==2) hc hN
/-- Same genuine fixed machine, including every actual nested return-stack cell. -/
noncomputable def recordInTime (oldTemplate : Checker→List Bool) (raw : Fin 6→List Bool) (second : Bool) (code : Fin 3)
    (htag : raw 1=List.replicate (tagCode second).val true) (htr : raw 2=List.replicate code.val true)
    (hc : SemiprimeSourceCompactBits.Compact (raw 0)) (hN : 0<SemiprimeBitArithmetic.bitValue (raw 0))
    (words : List (List Bool)) (oldStage oldInverse hist out : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial oldTemplate raw oldStage oldInverse (SemiprimeD1TensorTapeCodec.vectorBits words) hist out))
      (some (SemiprimeD1StackCalls.configuration (done raw second (code.val==2) words hist out)))
      (timeBound oldTemplate raw second (code.val==2) words oldStage oldInverse hist out) :=by
  apply SemiprimeD1StackSelectedDescriptorRecordExecution.recordInTime I.static sourceMap oldTemplate raw
    (tagCode second) code second htag htr (tag_dispatch second)
  · rw [selected_template];rfl
  · rw [selected_template]
    exact T.actual_trace (raw 0) second (code.val==2) hc hN
/-- Closed whole original checker clock plus ACTUAL finite selectors, charged
template acquisition, paid ordinal serialization and all literal tensor frames. -/
def runBound (oldTemplate : Checker→List Bool) (raw : Fin 6→List Bool) (second inverse : Bool)
    (words : List (List Bool)) (M : Nat) (oldStage oldInverse hist out : List Bool) : Nat :=
  SemiprimeD1StackTransformSelectorsExecution.timeBound (raw 1) (raw 2) oldStage oldInverse+
    SemiprimeD1StackDescriptorRecordExecution.prepareBound I.static oldTemplate (G.fields raw [second] [inverse])
      (SemiprimeD1TensorTapeCodec.vectorBits words) hist out+
    SemiprimeD1StackPublicTransformRecordClock.runBound (raw 0) second inverse words M+6
/-- Complete same-source own bit clock, without native report transport. -/
theorem timeBound_le (oldTemplate : Checker→List Bool) (raw : Fin 6→List Bool) (second inverse : Bool)
    (words : List (List Bool)) (M : Nat) (oldStage oldInverse hist out : List Bool)
    (hl : ∀w∈words,w.length≤M) (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    timeBound oldTemplate raw second inverse words oldStage oldInverse hist out≤
      runBound oldTemplate raw second inverse words M oldStage oldInverse hist out :=by
  have h:=SemiprimeD1StackPublicTransformRecordClock.timeBound_le (raw 0) second inverse words M hl hv
  change SemiprimeD1StackStaticRecordExecution.timeBound I.static
    (I.inputTemplate (raw 0) second inverse) words (T.answer (raw 0) second inverse) (T.budget (raw 0))≤_ at h
  unfold timeBound SemiprimeD1StackSelectedDescriptorRecordExecution.timeBound
    SemiprimeD1StackDescriptorRecordExecution.timeBound runBound
  rw [selected_template]
  omega
/-- The entire frozen436-role record result after actual selector/template acquisition. -/
theorem component_done (raw : Fin 6→List Bool) (second inverse : Bool) (words : List (List Bool)) (hist out : List Bool)
    (k : SemiprimeD1StackPublicTransformRecord.Stack) :
    (done raw second inverse words hist out).data (G.descriptorStack (SemiprimeD1StackDescriptorRecord.recordStack k))=
      (SemiprimeD1StackPublicTransformRecordExecution.done (raw 0) second inverse words hist out).data k :=by
  unfold done SemiprimeD1StackSelectedDescriptorRecord.done SemiprimeD1StackSelectedDescriptorRecord.data
    SemiprimeD1StackDescriptorRecord.done
  rw [selected_template]
  rfl
/-- All six original acquired words survive in their own physical locations. -/
theorem retained_raw (raw : Fin 6→List Bool) (second inverse : Bool) (words : List (List Bool))
    (hist out : List Bool) (i : Fin 6) : (done raw second inverse words hist out).data (G.rawSource i)=raw i :=by
  exact SemiprimeD1StackSelectedDescriptorRecordExecution.retained_raw I.static sourceMap raw second inverse words
    (T.answer (raw 0) second inverse) hist out i
end RiemannGaussian.SemiprimeD1StackTransformDescriptorRecord
