/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackTransformDescriptorRecord
/-! # Complete actual scale metadata source bound and all450-role prefixes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackTransformDescriptorRecordBounds
open SemiprimeD1StackTransformDescriptorRecord
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- The entire actual source trace with its closed concrete original-checker clock. -/
theorem source_run_bounded (oldTemplate : Checker→List Bool) (raw : Fin 6→List Bool) (second : Bool) (code : Fin 3)
    (htag : raw 1=List.replicate (tagCode second).val true) (htr : raw 2=List.replicate code.val true)
    (hc : SemiprimeSourceCompactBits.Compact (raw 0)) (hN : 0<SemiprimeBitArithmetic.bitValue (raw 0))
    (words : List (List Bool)) (M : Nat) (oldStage oldInverse hist out : List Bool)
    (hl : ∀w∈words,w.length≤M) (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    ∃t≤runBound oldTemplate raw second (code.val==2) words M oldStage oldInverse hist out,
      SemiprimeD1StackCalls.run program t (initial oldTemplate raw oldStage oldInverse (vectorBits words) hist out)=
        some (done raw second (code.val==2) words hist out) :=by
  obtain ⟨t,ht,hr⟩:=source_run oldTemplate raw second code htag htr hc hN words oldStage oldInverse hist out
  exact ⟨t,ht.trans (timeBound_le oldTemplate raw second (code.val==2) words M oldStage oldInverse hist out hl hv),hr⟩
/-- Every physical input is charged, including dirty template/selectors and all raw fields. -/
def inputSize (oldTemplate : Checker→List Bool) (raw : Fin 6→List Bool) (oldStage oldInverse bank hist out : List Bool) : Nat :=
  SemiprimeD1StackSelectedDescriptorRecordBounds.inputSize I.static oldTemplate raw oldStage oldInverse bank hist out
/-- All450 actual data roles, five dormant shadows, source fields and every
actual nested return cell, before/inside/after selector computation and record acquisition. -/
theorem prefix_cells (oldTemplate : Checker→List Bool) (raw : Fin 6→List Bool) (second : Bool) (code : Fin 3)
    (htag : raw 1=List.replicate (tagCode second).val true) (htr : raw 2=List.replicate code.val true)
    (hc : SemiprimeSourceCompactBits.Compact (raw 0)) (hN : 0<SemiprimeBitArithmetic.bitValue (raw 0))
    (words : List (List Bool)) (oldStage oldInverse hist out : List Bool) (fuel : Nat)
    (finish : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel
      (initial oldTemplate raw oldStage oldInverse (vectorBits words) hist out)=some finish) :
    (∑k:Stack,(finish.data k).length)+finish.frames.length≤
      451*(inputSize oldTemplate raw oldStage oldInverse (vectorBits words) hist out+
        timeBound oldTemplate raw second (code.val==2) words oldStage oldInverse hist out+1) :=by
  have hraw:SemiprimeD1StackDescriptorRecord.selected sourceMap (G.fields raw [second] [code.val==2]) I.static.raw=[]:=by
    rw [selected_template];rfl
  have hc0:SemiprimeD1StackStaticTableSpec.CheckerTrace I.static
      (SemiprimeD1StackDescriptorRecord.selected sourceMap (G.fields raw [second] [code.val==2]))
      (T.answer (raw 0) second (code.val==2)) (T.budget (raw 0)):=by
    rw [selected_template];exact T.actual_trace (raw 0) second (code.val==2) hc hN
  have h:=SemiprimeD1StackSelectedDescriptorRecordBounds.prefix_cells I.static sourceMap oldTemplate raw
    (tagCode second) code second htag htr (tag_dispatch second) hraw (T.answer (raw 0) second (code.val==2))
    (T.budget (raw 0)) hc0 words oldStage oldInverse hist out fuel finish hr
  rw [SemiprimeD1StackPublicTransform.stack_card] at h
  exact h
/-- Same complete prefix inventory on the genuine compiled finite-control machine. -/
theorem machine_prefix_cells (oldTemplate : Checker→List Bool) (raw : Fin 6→List Bool) (second : Bool) (code : Fin 3)
    (htag : raw 1=List.replicate (tagCode second).val true) (htr : raw 2=List.replicate code.val true)
    (hc : SemiprimeSourceCompactBits.Compact (raw 0)) (hN : 0<SemiprimeBitArithmetic.bitValue (raw 0))
    (words : List (List Bool)) (oldStage oldInverse hist out : List Bool) (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial oldTemplate raw oldStage oldInverse (vectorBits words) hist out)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      451*(inputSize oldTemplate raw oldStage oldInverse (vectorBits words) hist out+
        timeBound oldTemplate raw second (code.val==2) words oldStage oldInverse hist out+1) :=by
  have hraw:SemiprimeD1StackDescriptorRecord.selected sourceMap (G.fields raw [second] [code.val==2]) I.static.raw=[]:=by
    rw [selected_template];rfl
  have hc0:SemiprimeD1StackStaticTableSpec.CheckerTrace I.static
      (SemiprimeD1StackDescriptorRecord.selected sourceMap (G.fields raw [second] [code.val==2]))
      (T.answer (raw 0) second (code.val==2)) (T.budget (raw 0)):=by
    rw [selected_template];exact T.actual_trace (raw 0) second (code.val==2) hc hN
  have h:=SemiprimeD1StackSelectedDescriptorRecordBounds.machine_prefix_cells I.static sourceMap oldTemplate raw
    (tagCode second) code second htag htr (tag_dispatch second) hraw (T.answer (raw 0) second (code.val==2))
    (T.budget (raw 0)) hc0 words oldStage oldInverse hist out fuel cfg hr
  rw [SemiprimeD1StackPublicTransform.stack_card] at h
  exact h
end RiemannGaussian.SemiprimeD1StackTransformDescriptorRecordBounds
