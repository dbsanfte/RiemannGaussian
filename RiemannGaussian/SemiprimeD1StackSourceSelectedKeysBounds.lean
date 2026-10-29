/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectedKeysExecution
import RiemannGaussian.SemiprimeD1StackSourceSelectedKeysBytes
/-! # Own complete physical-byte polynomial clock, without replaying selection or old report clocks -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectedKeysBounds
open SemiprimeD1StackSourceSelectedKeys SemiprimeD1StackSourceSelectedKeysEncoding
open SemiprimeD1StackSourceSelectedKeysExecution SemiprimeD1StackSourceSelectedKeysBytes
open SemiprimeD1StackSourceSelectedKeysSetup SemiprimeD1StackSourceSelectedKeysFinish
open SemiprimeD1StackSourceSelectedKeysLoop
/-- Fixed whole bit-clock bound before every selected prefix and occurrence input. -/
def polynomial (i:Inputs) :Nat :=10000000*(inputSize i)^3
/-- Every actual lookup/copy/frame/log/drain/finalreverse step belongs to this SAME source's cubic acquired-byte clock. -/
theorem runBound_le (i:Inputs) :runBound i ≤ polynomial i :=by
  let S:Nat:=inputSize i
  have hS:1 ≤ S:=inputSize_pos i
  have hM:i.rows.length ≤ S:=occurrence_count_le i
  have h0:=rowsTime_le i i.rows (fun row h=>endpoint_widths i row h)
  change rowsTime i i.rows ≤ i.rows.length*(10000*S^2)+1 at h0
  have hm:=Nat.mul_le_mul_right (10000*S^2) hM
  have hscan:rowsTime i i.rows ≤ 10000*S^3+1:=by nlinarith only [h0,hm]
  have h1:=stream_length i i.rows
  change (stream i.ids i.rows).length ≤ i.rows.length*(6*S+4) at h1
  have hl:=Nat.mul_le_mul_right (6*S+4) hM
  have hlog:(stream i.ids i.rows).length ≤ 10*S^2:=by nlinarith only [h1,hl,hS]
  have hq:i.query.length ≤ S:=by
    dsimp only [S]
    unfold inputSize SemiprimeD1StackSourceEnvironmentBounds.cacheSize
    omega
  have ht:(tape i).length ≤ S:=(basic_bounds i).1
  have h23:S^2 ≤ S^3:=by
    calc
      _=S^2*1:=by omega
      _ ≤ S^2*S:=Nat.mul_le_mul_left _ hS
      _=S^3:=by ring
  have h12:S ≤ S^2:=Nat.le_pow (by decide:0<(2:Nat))
  have h13:=h12.trans h23
  have h03:=hS.trans h13
  change runBound i ≤ 10000000*S^3
  unfold runBound setupTime finishTime
  rw [List.length_reverse]
  nlinarith only [hscan,hlog,hq,ht,h23,h13,h03]
/-- Complete same actual source halts within the fixed physical-byte polynomial, including selectedIDzero and all repetitions. -/
theorem source_run_bounded (i:Inputs) (hc:Complete i) :
    ∃q ≤ polynomial i,SemiprimeD1StackCalls.run program q (source i)=some (done i) :=by
  obtain ⟨q,hq,hr⟩:=source_run i hc
  exact ⟨q,hq.trans (runBound_le i),hr⟩
/-- Actual compiled39-role complete-cache/tape source uses its own whole bit-clock. -/
noncomputable def machineSource (i:Inputs) (hc:Complete i) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (source i))
      (some (SemiprimeD1StackCalls.configuration (done i))) (polynomial i) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .source) (aux .output) .start program
  let h:=source_run_bounded i hc
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackSourceSelectedKeysBounds
