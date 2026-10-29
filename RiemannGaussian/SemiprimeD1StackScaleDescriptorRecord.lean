/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSelectedDescriptorRecordBounds
import RiemannGaussian.SemiprimeD1StackTransformSelectorsOriginal
import RiemannGaussian.SemiprimeD1StackPublicScaleRecordOriginal
import RiemannGaussian.SemiprimeD1StackPublicScaleRecordClock
/-! # Actual362-role scale descriptor, physically decoded inverse, entire old row
Only original acquired fields and scope words are supplied. The inverse is
constructed by the actual bounded selector, then copied by the real complete
template loader before the actual whole table/serializer/logger source runs.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackScaleDescriptorRecord
namespace I
export SemiprimeD1StackPublicScaleTable (static inputTemplate)
end I
namespace P
export SemiprimeD1StackPublicScaleTable.P (inputRole stride frequency selector assignment)
end P
namespace G
export SemiprimeD1StackSelectedDescriptorRecord (descriptorStack selectorStack rawSource history output fields)
end G
namespace T
export SemiprimeD1StackPublicScaleTableTrace (answer budget actual_trace)
end T
/-- Fixed actual160-role checker bank. -/
abbrev Checker :=SemiprimeD1StackPublicScale.Stack
/-- Static source map: N0, actual j3/k4 marker fields and physically computed inverse2. -/
def sourceMap (k : Checker) : Option (Fin 6) :=
  if k=P.inputRole then some 0 else if k=P.stride then some 3
  else if k=P.frequency then some 4 else if k=P.selector then some 2 else none
/-- Complete362-role physical inventory, including all five dormant alias shadows. -/
abbrev Stack :=SemiprimeD1StackSelectedDescriptorRecord.Stack Checker
/-- Every actual selector/template/table/serializer/logger/return label is finite. -/
abbrev Label :=SemiprimeD1StackSelectedDescriptorRecord.Label SemiprimeD1StackPublicScale.Label I.static.roles.length
/-- One fixed literal source before all original N and descriptor values. -/
def program : Label→SemiprimeD1StackCalls.Instruction Stack Label :=
  SemiprimeD1StackSelectedDescriptorRecord.program I.static sourceMap
/-- Only six acquired original words, scope/caller bytes and charged dirty template/selectors. -/
def initial (oldTemplate : Checker→List Bool) (raw : Fin 6→List Bool)
    (oldStage oldInverse bank hist out : List Bool) : SemiprimeD1StackCalls.State Stack Label :=
  SemiprimeD1StackSelectedDescriptorRecord.initial I.static oldTemplate raw oldStage oldInverse bank hist out
/-- Fixed genuine finite-control machine, with no runtime selector supplier. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackSelectedDescriptorRecord.machine I.static sourceMap
/-- Every physical register and alias shadow is counted. -/
theorem stack_card : Fintype.card Stack=362 :=by
  rw [SemiprimeD1StackSelectedDescriptorRecord.stack_card,SemiprimeD1StackPublicScale.stack_card]
/-- The actual loader sources select exactly the frozen scale initialization;
all arithmetic sources, caches, assignments, counts and verdicts remain empty. -/
theorem selected_template (raw : Fin 6→List Bool) (second inverse : Bool) :
    SemiprimeD1StackDescriptorRecord.selected sourceMap (G.fields raw [second] [inverse])=
      I.inputTemplate (raw 0) (raw 3) (raw 4) inverse :=by
  funext k
  rw [SemiprimeD1StackPublicScaleTableTrace.template_only]
  change (if k=P.inputRole then some 0 else if k=P.stride then some 3
    else if k=P.frequency then some 4 else if k=P.selector then some 2 else none).elim [] (G.fields raw [second] [inverse])=_
  by_cases hn:k=P.inputRole
  · subst k;rfl
  · by_cases hj:k=P.stride
    · subst k;rfl
    · by_cases hk:k=P.frequency
      · subst k;rfl
      · by_cases hi:k=P.selector
        · subst k;rfl
        · simp only [hn,hj,hk,hi,ite_false];rfl
/-- Actual result after physically decoded inverse, actual template loading and the entire row source. -/
def done (raw : Fin 6→List Bool) (inverse : Bool) (words : List (List Bool)) (hist out : List Bool) :
    SemiprimeD1StackCalls.State Stack Label :=
  SemiprimeD1StackSelectedDescriptorRecord.done I.static sourceMap raw false inverse words
    (T.answer (raw 0) (raw 3) (raw 4) inverse) hist out
/-- Complete own source clock; inverse occurs only in this proof-side bound/result notation. -/
def timeBound (oldTemplate : Checker→List Bool) (raw : Fin 6→List Bool) (inverse : Bool)
    (words : List (List Bool)) (oldStage oldInverse hist out : List Bool) : Nat :=
  SemiprimeD1StackSelectedDescriptorRecordExecution.timeBound I.static sourceMap oldTemplate raw false inverse words
    (T.answer (raw 0) (raw 3) (raw 4) inverse) (T.budget (raw 0) (raw 3) (raw 4)) oldStage oldInverse hist out
/-- Complete concrete actual trace: inverse is decoded from actual copied coord0;
the frozen entire scale checker discharges every generic trace premise. -/
theorem source_run (oldTemplate : Checker→List Bool) (raw : Fin 6→List Bool) (code : Fin 3)
    (htag : raw 1=[true,true]) (htr : raw 2=List.replicate code.val true)
    (hj : raw 3=SemiprimeD1StackUnaryDivmod.unary (raw 3).length)
    (hk : raw 4=SemiprimeD1StackUnaryDivmod.unary (raw 4).length)
    (hc : SemiprimeSourceCompactBits.Compact (raw 0)) (hN : 0<SemiprimeBitArithmetic.bitValue (raw 0))
    (words : List (List Bool)) (oldStage oldInverse hist out : List Bool) :
    ∃t≤timeBound oldTemplate raw (code.val==2) words oldStage oldInverse hist out,
      SemiprimeD1StackCalls.run program t (initial oldTemplate raw oldStage oldInverse
        (SemiprimeD1TensorTapeCodec.vectorBits words) hist out)=some (done raw (code.val==2) words hist out) :=by
  apply SemiprimeD1StackSelectedDescriptorRecordExecution.source_run I.static sourceMap oldTemplate raw 2 code false htag htr rfl
  · rw [selected_template];rfl
  · rw [selected_template]
    exact T.actual_trace (raw 0) (raw 3) (raw 4) (code.val==2) hj hk hc hN
/-- Same genuine finite-machine execution with its own complete source clock. -/
noncomputable def recordInTime (oldTemplate : Checker→List Bool) (raw : Fin 6→List Bool) (code : Fin 3)
    (htag : raw 1=[true,true]) (htr : raw 2=List.replicate code.val true)
    (hj : raw 3=SemiprimeD1StackUnaryDivmod.unary (raw 3).length)
    (hk : raw 4=SemiprimeD1StackUnaryDivmod.unary (raw 4).length)
    (hc : SemiprimeSourceCompactBits.Compact (raw 0)) (hN : 0<SemiprimeBitArithmetic.bitValue (raw 0))
    (words : List (List Bool)) (oldStage oldInverse hist out : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial oldTemplate raw oldStage oldInverse (SemiprimeD1TensorTapeCodec.vectorBits words) hist out))
      (some (SemiprimeD1StackCalls.configuration (done raw (code.val==2) words hist out)))
      (timeBound oldTemplate raw (code.val==2) words oldStage oldInverse hist out) :=by
  apply SemiprimeD1StackSelectedDescriptorRecordExecution.recordInTime I.static sourceMap oldTemplate raw 2 code false htag htr rfl
  · rw [selected_template];rfl
  · rw [selected_template]
    exact T.actual_trace (raw 0) (raw 3) (raw 4) (code.val==2) hj hk hc hN
/-- Concrete own clock: actual selector code, charged dirty-template load and
frozen scale table bit clock, paid scope conversion, consuming logger and returns. -/
def runBound (oldTemplate : Checker→List Bool) (raw : Fin 6→List Bool) (inverse : Bool)
    (words : List (List Bool)) (M : Nat) (oldStage oldInverse hist out : List Bool) : Nat :=
  SemiprimeD1StackTransformSelectorsExecution.timeBound (raw 1) (raw 2) oldStage oldInverse+
    SemiprimeD1StackDescriptorRecordExecution.prepareBound I.static oldTemplate (G.fields raw [false] [inverse])
      (SemiprimeD1TensorTapeCodec.vectorBits words) hist out+
    SemiprimeD1StackPublicScaleRecordClock.runBound (raw 0) (raw 3) (raw 4) inverse words M+6
/-- The actual complete source obeys the concrete same-checker bound. -/
theorem timeBound_le (oldTemplate : Checker→List Bool) (raw : Fin 6→List Bool) (inverse : Bool)
    (words : List (List Bool)) (M : Nat) (oldStage oldInverse hist out : List Bool)
    (hl : ∀w∈words,w.length≤M) (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    timeBound oldTemplate raw inverse words oldStage oldInverse hist out≤
      runBound oldTemplate raw inverse words M oldStage oldInverse hist out :=by
  have h:=SemiprimeD1StackPublicScaleRecordClock.timeBound_le (raw 0) (raw 3) (raw 4) inverse words M hl hv
  change SemiprimeD1StackStaticRecordExecution.timeBound I.static
    (I.inputTemplate (raw 0) (raw 3) (raw 4) inverse) words
    (T.answer (raw 0) (raw 3) (raw 4) inverse) (T.budget (raw 0) (raw 3) (raw 4))≤_ at h
  unfold timeBound SemiprimeD1StackSelectedDescriptorRecordExecution.timeBound
    SemiprimeD1StackDescriptorRecordExecution.timeBound runBound
  rw [selected_template]
  omega
/-- Exact frozen complete348-role record result after actual physical selector/template acquisition. -/
theorem component_done (raw : Fin 6→List Bool) (inverse : Bool) (words : List (List Bool)) (hist out : List Bool)
    (k : SemiprimeD1StackPublicScaleRecord.Stack) :
    (done raw inverse words hist out).data (G.descriptorStack (SemiprimeD1StackDescriptorRecord.recordStack k))=
      (SemiprimeD1StackPublicScaleRecordExecution.done (raw 0) (raw 3) (raw 4) inverse words hist out).data k :=by
  unfold done SemiprimeD1StackSelectedDescriptorRecord.done SemiprimeD1StackSelectedDescriptorRecord.data
    SemiprimeD1StackDescriptorRecord.done
  rw [selected_template]
  rfl
/-- Every original acquired field is physically retained, including raw tag and transform code. -/
theorem retained_raw (raw : Fin 6→List Bool) (inverse : Bool) (words : List (List Bool))
    (hist out : List Bool) (i : Fin 6) : (done raw inverse words hist out).data (G.rawSource i)=raw i :=by
  exact SemiprimeD1StackSelectedDescriptorRecordExecution.retained_raw I.static sourceMap raw false inverse words
    (T.answer (raw 0) (raw 3) (raw 4) inverse) hist out i
end RiemannGaussian.SemiprimeD1StackScaleDescriptorRecord
