/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformRecordExecution
import RiemannGaussian.SemiprimeD1StackStaticRecordBounds
import RiemannGaussian.SemiprimeD1StackPublicTransformTableBounds
/-! # Concrete transform record clock and all436-role physical prefixes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformRecordBounds
open SemiprimeD1StackPublicTransformRecord SemiprimeD1StackPublicTransformRecordExecution
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Actual scalar compiler bound plus paid scope conversion, logging and returns. -/
def runBound (bits : List Bool) (second inverse : Bool) (words : List (List Bool)) : Nat :=
  SemiprimeD1StackPublicTransformTableBounds.runBound bits words+
    SemiprimeD1StackPortOrdinalStreamExecution.timeBound words+
    SemiprimeD1StackVertexRecordStream.recordTime (SemiprimeD1StackPortOrdinalStream.result words)
      (SemiprimeD1StackPublicTransformTableExecution.table bits second inverse words)+4
/-- Complete source bound uses the actual original checker's proved clock. -/
theorem timeBound_le (bits : List Bool) (second inverse : Bool) (words : List (List Bool)) :
    timeBound bits second inverse words≤runBound bits second inverse words := by
  have h0:=SemiprimeD1StackStaticTableBounds.timeBound_le I.static (I.inputTemplate bits second inverse)
    words (T.answer bits second inverse) (T.budget bits)
  have h1:=SemiprimeD1StackPublicTransformTableBounds.timeBound_le bits second inverse words
  unfold timeBound SemiprimeD1StackStaticRecordExecution.timeBound runBound
    SemiprimeD1StackPublicTransformTableExecution.table
  change SemiprimeD1StackStaticTableExecution.timeBound I.static (I.inputTemplate bits second inverse)
    words (T.answer bits second inverse) (T.budget bits)≤_ at h0
  change SemiprimeD1StackStaticTableBounds.runBound I.static (I.inputTemplate bits second inverse)
    words (T.budget bits)≤_ at h1
  omega
/-- Fully closed concrete source execution, no checker trace supplier remains. -/
theorem source_run_bounded (bits : List Bool) (second inverse : Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool))
    (hist out : List Bool) :
    ∃t≤runBound bits second inverse words,SemiprimeD1StackCalls.run program t
      (initial bits second inverse (vectorBits words) hist out)=some (done bits second inverse words hist out) := by
  obtain ⟨t,ht,hr⟩:=source_run bits second inverse hc hN words hist out
  exact ⟨t,ht.trans (timeBound_le bits second inverse words),hr⟩
/-- Same genuine finite machine with the full concrete own source bound. -/
noncomputable def machineRecord (bits : List Bool) (second inverse : Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool))
    (hist out : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits second inverse (vectorBits words) hist out))
      (some (SemiprimeD1StackCalls.configuration (done bits second inverse words hist out))) (runBound bits second inverse words) := by
  let h:=recordInTime bits second inverse hc hN words hist out
  exact ⟨h.toEvalsTo,h.steps_le_m.trans (timeBound_le bits second inverse words)⟩
/-- Every436-role source word and every real nested return cell at every prefix. -/
theorem prefix_cells (bits : List Bool) (second inverse : Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool))
    (hist out : List Bool) (fuel : Nat) (finish : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial bits second inverse (vectorBits words) hist out)=some finish) :
    (∑k:Stack,(finish.data k).length)+finish.frames.length≤
      437*(204*(bits.length+1)+(vectorBits words).length+hist.length+out.length+
        runBound bits second inverse words+1) := by
  have h:=SemiprimeD1StackStaticRecordBounds.prefix_cells I.static (I.inputTemplate bits second inverse)
    (I.template_raw bits second inverse) (T.answer bits second inverse) (T.budget bits)
    (T.actual_trace bits second inverse hc hN) words hist out fuel finish hr
  rw [SemiprimeD1StackPublicTransform.stack_card] at h
  have ht:=timeBound_le bits second inverse words
  have hb:=SemiprimeD1StackPublicTransformTableBounds.template_bytes bits second inverse
  change _≤437*(SemiprimeD1StackStaticTableSpec.inputBytes (I.inputTemplate bits second inverse)+
    (vectorBits words).length+hist.length+out.length+timeBound bits second inverse words+1) at h
  exact h.trans (by omega)
/-- The complete inventory on the actual finite-control machine itself. -/
theorem machine_prefix_cells (bits : List Bool) (second inverse : Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool))
    (hist out : List Bool) (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits second inverse (vectorBits words) hist out)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      437*(204*(bits.length+1)+(vectorBits words).length+hist.length+out.length+
        runBound bits second inverse words+1) := by
  have h:=SemiprimeD1StackStaticRecordBounds.machine_prefix_cells I.static (I.inputTemplate bits second inverse)
    (I.template_raw bits second inverse) (T.answer bits second inverse) (T.budget bits)
    (T.actual_trace bits second inverse hc hN) words hist out fuel cfg hr
  rw [SemiprimeD1StackPublicTransform.stack_card] at h
  have ht:=timeBound_le bits second inverse words
  have hb:=SemiprimeD1StackPublicTransformTableBounds.template_bytes bits second inverse
  change _≤437*(SemiprimeD1StackStaticTableSpec.inputBytes (I.inputTemplate bits second inverse)+
    (vectorBits words).length+hist.length+out.length+timeBound bits second inverse words+1) at h
  exact h.trans (by omega)
end RiemannGaussian.SemiprimeD1StackPublicTransformRecordBounds
