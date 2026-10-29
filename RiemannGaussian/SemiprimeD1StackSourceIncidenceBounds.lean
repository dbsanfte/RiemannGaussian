/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceExecution
import RiemannGaussian.SemiprimeD1StackSourceIncidenceOuterBound
/-! # Complete own polynomial physical-byte clock of the SAME47-role query -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceBounds
open SemiprimeD1StackSourceIncidence SemiprimeD1StackSourceIncidenceEncoding
open SemiprimeD1StackSourceIncidenceExecution SemiprimeD1StackSourceIncidenceOuter
open SemiprimeD1StackSourceIncidenceSetup SemiprimeD1StackSourceIncidenceFinish
open SemiprimeD1StackSourceIncidenceInnerBound SemiprimeD1StackSourceIncidenceOuterBound
open SemiprimeD1StackSourceIncidenceBytes
/-- A fixed whole query bit-clock bound, selected before every original source/prefix. -/
def polynomial (i:Inputs) :Nat :=1000000000*(inputSize i)^6
/-- Elementary proof-side monomial comparison; no numeric exponent becomes a runtime operand. -/
theorem pow_mono (s:Nat) (hs:1 ≤ s) (a b:Nat) (hab:a ≤ b) :s^a ≤ s^b :=by
  have hp:0 < s^(b-a):=pow_pos (by omega) _
  calc
    _ ≤ s^a*s^(b-a):=Nat.le_mul_of_pos_right _ hp
    _=s^b:=by rw [←pow_add];congr 1;omega
/-- Whole actual trace's scalar/byte expression is bounded using actual M² multiplicity and paid accumulator growth. -/
theorem runBound_le (i:Inputs) :runBound i ≤ polynomial i :=by
  let S:Nat:=inputSize i
  let M:Nat:=i.rows.length
  let P:Nat:=rowWidth i
  have hS:1 ≤ S:=inputSize_pos i
  have hM:M ≤ S:=occurrence_count_le i
  have hP:P ≤ S+1:=(basic_bounds i).2.2.2
  have h23:=pow_mono S hS 2 3 (by decide)
  have h13:=pow_mono S hS 1 3 (by decide)
  have h03:=pow_mono S hS 0 3 (by decide)
  simp only [pow_one,pow_zero] at h13 h03
  have hB:M*M*P ≤ 2*S^3:=by
    calc
      _ ≤ S*S*(S+1):=Nat.mul_le_mul (Nat.mul_le_mul hM hM) hP
      _ ≤ 2*S^3:=by nlinarith only [h23]
  have hcap:([ ]:List Bool).length+i.rows.length*i.rows.length*rowWidth i ≤ 2*S^3:=by
    simpa only [List.length_nil,Nat.zero_add] using hB
  have hc:=outerClock_le i (2*S^3) i.rows [] (fun row h=>endpoint_widths i row h) hcap
  change outerClock i i.rows [] ≤ (M+1)*outerCeiling i (2*S^3) at hc
  have hC:ceiling i (2*S^3) ≤ 200000*S^3:=by
    change 100000*S^2+100*(2*S^3+S+1) ≤ 200000*S^3
    nlinarith only [h23,h13,h03]
  have hH:outerCeiling i (2*S^3) ≤ (M+1)*(200000*S^3)+100*(S+1):=by
    unfold outerCeiling
    exact Nat.add_le_add_right (Nat.mul_le_mul_left (M+1) hC) _
  have hMplus:M+1 ≤ 2*S:=by omega
  have h56:=pow_mono S hS 5 6 (by decide)
  have h26:=pow_mono S hS 2 6 (by decide)
  have houter:outerClock i i.rows [] ≤ 800400*S^6:=by
    calc
      _ ≤ (M+1)*((M+1)*(200000*S^3)+100*(S+1)):=hc.trans (Nat.mul_le_mul_left _ hH)
      _ ≤ (2*S)*((2*S)*(200000*S^3)+200*S):=by
        apply Nat.mul_le_mul hMplus
        exact Nat.add_le_add (Nat.mul_le_mul_right _ hMplus) (by omega)
      _=800000*S^5+400*S^2:=by ring
      _ ≤ 800400*S^6:=by nlinarith only [h56,h26]
  have hq:i.query.length ≤ S:=by
    dsimp only [S]
    unfold inputSize SemiprimeD1StackSourceEnvironmentBounds.cacheSize
    omega
  have ht:(tape i).length ≤ S:=(basic_bounds i).1
  have hends:setupTime i+finishTime i+1 ≤ 33*S:=by
    unfold setupTime finishTime
    omega
  have h16:=pow_mono S hS 1 6 (by decide)
  simp only [pow_one] at h16
  change runBound i ≤ 1000000000*S^6
  unfold runBound
  nlinarith only [houter,hends,h16]
/-- SAME complete source query uses its own fixed physical polynomial, not any old native histogram/report clock. -/
theorem source_run_bounded (i:Inputs) :
    ∃q ≤ polynomial i,SemiprimeD1StackCalls.run program q (source i)=some (done i) :=by
  obtain ⟨q,hq,hr⟩:=source_run i
  exact ⟨q,hq.trans (runBound_le i),hr⟩
/-- Genuine compiled fixed47-role query certificate for the full acquired multiword source. -/
noncomputable def machineQuery (i:Inputs) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (source i))
      (some (SemiprimeD1StackCalls.configuration (done i))) (polynomial i) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .source) (aux .total) .start program
  let h:=source_run_bounded i
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackSourceIncidenceBounds
