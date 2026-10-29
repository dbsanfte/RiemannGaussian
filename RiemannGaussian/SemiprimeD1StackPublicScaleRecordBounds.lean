/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicScaleRecordExecution
import RiemannGaussian.SemiprimeD1StackStaticRecordBounds
import RiemannGaussian.SemiprimeD1StackPublicScaleTableBounds
/-! # Concrete scale record clock and all348-role physical prefixes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicScaleRecordBounds
open SemiprimeD1StackPublicScaleRecord SemiprimeD1StackPublicScaleRecordExecution
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Actual scalar compiler bound plus paid scope conversion, logging and returns. -/
def runBound (bits stride frequency : List Bool) (inverse : Bool) (words : List (List Bool)) : Nat :=
  SemiprimeD1StackPublicScaleTableBounds.runBound bits stride frequency words+
    SemiprimeD1StackPortOrdinalStreamExecution.timeBound words+
    SemiprimeD1StackVertexRecordStream.recordTime (SemiprimeD1StackPortOrdinalStream.result words)
      (SemiprimeD1StackPublicScaleTableExecution.table bits stride frequency inverse words)+4
/-- Complete source bound uses the actual original checker's proved clock. -/
theorem timeBound_le (bits stride frequency : List Bool) (inverse : Bool) (words : List (List Bool)) :
    timeBound bits stride frequency inverse words≤runBound bits stride frequency inverse words := by
  have h0:=SemiprimeD1StackStaticTableBounds.timeBound_le I.static (I.inputTemplate bits stride frequency inverse)
    words (T.answer bits stride frequency inverse) (T.budget bits stride frequency)
  have h1:=SemiprimeD1StackPublicScaleTableBounds.timeBound_le bits stride frequency inverse words
  unfold timeBound SemiprimeD1StackStaticRecordExecution.timeBound runBound
    SemiprimeD1StackPublicScaleTableExecution.table
  change SemiprimeD1StackStaticTableExecution.timeBound I.static (I.inputTemplate bits stride frequency inverse)
    words (T.answer bits stride frequency inverse) (T.budget bits stride frequency)≤_ at h0
  change SemiprimeD1StackStaticTableBounds.runBound I.static (I.inputTemplate bits stride frequency inverse)
    words (T.budget bits stride frequency)≤_ at h1
  omega
/-- Fully closed concrete source execution, no checker trace supplier remains. -/
theorem source_run_bounded (bits stride frequency : List Bool) (inverse : Bool) (hj : stride=SemiprimeD1StackUnaryDivmod.unary stride.length)
    (hk : frequency=SemiprimeD1StackUnaryDivmod.unary frequency.length)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool))
    (hist out : List Bool) :
    ∃t≤runBound bits stride frequency inverse words,SemiprimeD1StackCalls.run program t
      (initial bits stride frequency inverse (vectorBits words) hist out)=some (done bits stride frequency inverse words hist out) := by
  obtain ⟨t,ht,hr⟩:=source_run bits stride frequency inverse hj hk hc hN words hist out
  exact ⟨t,ht.trans (timeBound_le bits stride frequency inverse words),hr⟩
/-- Same genuine finite machine with the full concrete own source bound. -/
noncomputable def machineRecord (bits stride frequency : List Bool) (inverse : Bool) (hj : stride=SemiprimeD1StackUnaryDivmod.unary stride.length)
    (hk : frequency=SemiprimeD1StackUnaryDivmod.unary frequency.length)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool))
    (hist out : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits stride frequency inverse (vectorBits words) hist out))
      (some (SemiprimeD1StackCalls.configuration (done bits stride frequency inverse words hist out))) (runBound bits stride frequency inverse words) := by
  let h:=recordInTime bits stride frequency inverse hj hk hc hN words hist out
  exact ⟨h.toEvalsTo,h.steps_le_m.trans (timeBound_le bits stride frequency inverse words)⟩
/-- Every348-role source word and every real nested return cell at every prefix. -/
theorem prefix_cells (bits stride frequency : List Bool) (inverse : Bool) (hj : stride=SemiprimeD1StackUnaryDivmod.unary stride.length)
    (hk : frequency=SemiprimeD1StackUnaryDivmod.unary frequency.length)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool))
    (hist out : List Bool) (fuel : Nat) (finish : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial bits stride frequency inverse (vectorBits words) hist out)=some finish) :
    (∑k:Stack,(finish.data k).length)+finish.frames.length≤
      349*(160*(bits.length+stride.length+frequency.length+1)+(vectorBits words).length+hist.length+out.length+
        runBound bits stride frequency inverse words+1) := by
  have h:=SemiprimeD1StackStaticRecordBounds.prefix_cells I.static (I.inputTemplate bits stride frequency inverse)
    (I.template_raw bits stride frequency inverse) (T.answer bits stride frequency inverse) (T.budget bits stride frequency)
    (T.actual_trace bits stride frequency inverse hj hk hc hN) words hist out fuel finish hr
  rw [SemiprimeD1StackPublicScale.stack_card] at h
  have ht:=timeBound_le bits stride frequency inverse words
  have hb:=SemiprimeD1StackPublicScaleTableBounds.template_bytes bits stride frequency inverse
  change _≤349*(SemiprimeD1StackStaticTableSpec.inputBytes (I.inputTemplate bits stride frequency inverse)+
    (vectorBits words).length+hist.length+out.length+timeBound bits stride frequency inverse words+1) at h
  exact h.trans (by omega)
/-- The complete inventory on the actual finite-control machine itself. -/
theorem machine_prefix_cells (bits stride frequency : List Bool) (inverse : Bool) (hj : stride=SemiprimeD1StackUnaryDivmod.unary stride.length)
    (hk : frequency=SemiprimeD1StackUnaryDivmod.unary frequency.length)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool))
    (hist out : List Bool) (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits stride frequency inverse (vectorBits words) hist out)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      349*(160*(bits.length+stride.length+frequency.length+1)+(vectorBits words).length+hist.length+out.length+
        runBound bits stride frequency inverse words+1) := by
  have h:=SemiprimeD1StackStaticRecordBounds.machine_prefix_cells I.static (I.inputTemplate bits stride frequency inverse)
    (I.template_raw bits stride frequency inverse) (T.answer bits stride frequency inverse) (T.budget bits stride frequency)
    (T.actual_trace bits stride frequency inverse hj hk hc hN) words hist out fuel cfg hr
  rw [SemiprimeD1StackPublicScale.stack_card] at h
  have ht:=timeBound_le bits stride frequency inverse words
  have hb:=SemiprimeD1StackPublicScaleTableBounds.template_bytes bits stride frequency inverse
  change _≤349*(SemiprimeD1StackStaticTableSpec.inputBytes (I.inputTemplate bits stride frequency inverse)+
    (vectorBits words).length+hist.length+out.length+timeBound bits stride frequency inverse words+1) at h
  exact h.trans (by omega)
end RiemannGaussian.SemiprimeD1StackPublicScaleRecordBounds
