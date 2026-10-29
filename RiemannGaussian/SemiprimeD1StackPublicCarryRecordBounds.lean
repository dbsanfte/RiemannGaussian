/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicCarryRecordExecution
import RiemannGaussian.SemiprimeD1StackStaticRecordBounds
import RiemannGaussian.SemiprimeD1StackPublicCarryTableBounds
/-! # Concrete carry record clock and all130-role physical prefixes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicCarryRecordBounds
open SemiprimeD1StackPublicCarryRecord SemiprimeD1StackPublicCarryRecordExecution
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Actual scalar compiler bound plus paid scope conversion, logging and returns. -/
def runBound (bits indexWord : List Bool) (words : List (List Bool)) : Nat :=
  SemiprimeD1StackPublicCarryTableBounds.runBound bits indexWord words+
    SemiprimeD1StackPortOrdinalStreamExecution.timeBound words+
    SemiprimeD1StackVertexRecordStream.recordTime (SemiprimeD1StackPortOrdinalStream.result words)
      (SemiprimeD1StackPublicCarryTableExecution.table bits indexWord words)+4
/-- Complete source bound uses the actual original checker's proved clock. -/
theorem timeBound_le (bits indexWord : List Bool) (words : List (List Bool)) :
    timeBound bits indexWord words≤runBound bits indexWord words := by
  have h0:=SemiprimeD1StackStaticTableBounds.timeBound_le I.static (I.inputTemplate bits indexWord)
    words (T.answer bits indexWord) (T.budget bits indexWord)
  have h1:=SemiprimeD1StackPublicCarryTableBounds.timeBound_le bits indexWord words
  unfold timeBound SemiprimeD1StackStaticRecordExecution.timeBound runBound
    SemiprimeD1StackPublicCarryTableExecution.table
  change SemiprimeD1StackStaticTableExecution.timeBound I.static (I.inputTemplate bits indexWord)
    words (T.answer bits indexWord) (T.budget bits indexWord)≤_ at h0
  change SemiprimeD1StackStaticTableBounds.runBound I.static (I.inputTemplate bits indexWord)
    words (T.budget bits indexWord)≤_ at h1
  omega
/-- Fully closed concrete source execution, no checker trace supplier remains. -/
theorem source_run_bounded (bits indexWord : List Bool) (hb : bits≠[]) (words : List (List Bool))
    (hist out : List Bool) :
    ∃t≤runBound bits indexWord words,SemiprimeD1StackCalls.run program t
      (initial bits indexWord (vectorBits words) hist out)=some (done bits indexWord words hist out) := by
  obtain ⟨t,ht,hr⟩:=source_run bits indexWord hb words hist out
  exact ⟨t,ht.trans (timeBound_le bits indexWord words),hr⟩
/-- Same genuine finite machine with the full concrete own source bound. -/
noncomputable def machineRecord (bits indexWord : List Bool) (hb : bits≠[]) (words : List (List Bool))
    (hist out : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits indexWord (vectorBits words) hist out))
      (some (SemiprimeD1StackCalls.configuration (done bits indexWord words hist out))) (runBound bits indexWord words) := by
  let h:=recordInTime bits indexWord hb words hist out
  exact ⟨h.toEvalsTo,h.steps_le_m.trans (timeBound_le bits indexWord words)⟩
/-- Every130-role source word and every real nested return cell at every prefix. -/
theorem prefix_cells (bits indexWord : List Bool) (hb : bits≠[]) (words : List (List Bool))
    (hist out : List Bool) (fuel : Nat) (finish : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial bits indexWord (vectorBits words) hist out)=some finish) :
    (∑k:Stack,(finish.data k).length)+finish.frames.length≤
      131*(51*(bits.length+indexWord.length)+(vectorBits words).length+hist.length+out.length+
        runBound bits indexWord words+1) := by
  have h:=SemiprimeD1StackStaticRecordBounds.prefix_cells I.static (I.inputTemplate bits indexWord)
    (I.template_raw bits indexWord) (T.answer bits indexWord) (T.budget bits indexWord)
    (T.actual_trace bits indexWord hb) words hist out fuel finish hr
  rw [SemiprimeD1StackPublicCarry.stack_card] at h
  have ht:=timeBound_le bits indexWord words
  have hb:=SemiprimeD1StackPublicCarryTableBounds.template_bytes bits indexWord
  change _≤131*(SemiprimeD1StackStaticTableSpec.inputBytes (I.inputTemplate bits indexWord)+
    (vectorBits words).length+hist.length+out.length+timeBound bits indexWord words+1) at h
  exact h.trans (by omega)
/-- The complete inventory on the actual finite-control machine itself. -/
theorem machine_prefix_cells (bits indexWord : List Bool) (hb : bits≠[]) (words : List (List Bool))
    (hist out : List Bool) (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits indexWord (vectorBits words) hist out)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      131*(51*(bits.length+indexWord.length)+(vectorBits words).length+hist.length+out.length+
        runBound bits indexWord words+1) := by
  have h:=SemiprimeD1StackStaticRecordBounds.machine_prefix_cells I.static (I.inputTemplate bits indexWord)
    (I.template_raw bits indexWord) (T.answer bits indexWord) (T.budget bits indexWord)
    (T.actual_trace bits indexWord hb) words hist out fuel cfg hr
  rw [SemiprimeD1StackPublicCarry.stack_card] at h
  have ht:=timeBound_le bits indexWord words
  have hb:=SemiprimeD1StackPublicCarryTableBounds.template_bytes bits indexWord
  change _≤131*(SemiprimeD1StackStaticTableSpec.inputBytes (I.inputTemplate bits indexWord)+
    (vectorBits words).length+hist.length+out.length+timeBound bits indexWord words+1) at h
  exact h.trans (by omega)
end RiemannGaussian.SemiprimeD1StackPublicCarryRecordBounds
