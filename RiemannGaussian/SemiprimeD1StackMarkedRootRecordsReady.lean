/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsResources
/-! # All-role resources for the SAME actual retained-root-cache continuation -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsReady
open SemiprimeD1StackMarkedRootRecords SemiprimeD1StackMarkedRootRecordsExecution
open SemiprimeD1StackMarkedRootRecordsBounds SemiprimeD1StackMarkedRootRecordsView
open SemiprimeBitArithmetic (bitValue)
/-- Initial continuation caches are paid by their actual old1804 acquisition, never supplied answers. -/
theorem initial_length (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits)
    (k : Stack) : ((ready bits hN).data k).length ≤ bits.length+RB.runBound bits := by
  rcases k with k|k
  · exact retained_length bits hc hN k
  · rcases k with k|k
    · exact Nat.zero_le _
    · rcases k with k|k
      · change (privateTable (SemiprimeD1StackMarkedRootRecordsTableView.tableWords bits [] [] [] [] []) k).length ≤ _
        rw [congrFun (private_empty bits) k]
        simp [privateTable]
      · cases k <;> exact Nat.zero_le _
/-- SAME ready source cannot execute successfully beyond its actual final halt. -/
theorem prefix_fuel_le (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits)
    (fuel : Nat) (finish : C.State Stack Label) (hr : C.run program fuel (ready bits hN)=some finish) :
    fuel ≤ readyBound bits hN := by
  obtain ⟨t,ht,he⟩ := ready_run bits hc hN
  have hf : fuel ≤ t := by
    by_contra hn
    have h : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done bits hN)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- Every ready-source prefix counts all retained1804/fresh53/private144/Aux10 and real returns. -/
theorem prefix_cells (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits)
    (fuel : Nat) (finish : C.State Stack Label) (hr : C.run program fuel (ready bits hN)=some finish) :
    (∑ k : Stack,(finish.data k).length)+finish.frames.length ≤
      2012*(bits.length+RB.runBound bits+readyBound bits hN) := by
  have hd := SemiprimeD1StackReturnLink.run_data_bound program fuel (bits.length+RB.runBound bits) _ finish
    (initial_length bits hc hN) hr
  have hf := SemiprimeD1StackCalls.run_frame_bound program fuel _ finish hr
  change finish.frames.length ≤ 0+fuel at hf
  have ht := prefix_fuel_le bits hc hN fuel finish hr
  have hs : (∑ k : Stack,(finish.data k).length) ≤ 2011*(bits.length+RB.runBound bits+fuel) := by
    calc
      _ ≤ ∑ _k : Stack,(bits.length+RB.runBound bits+fuel) := Finset.sum_le_sum (fun k _ => hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  omega
/-- The continuation has its own paid source bound under the same fixed original-scope envelope. -/
theorem readyBound_le (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits) :
    readyBound bits hN ≤ runBound bits := by
  have h0 : readyBound bits hN ≤ timeBound bits hN := by unfold timeBound;omega
  exact h0.trans (timeBound_le bits hc hN)
/-- Actual compiled continuation starts with exactly the ACTUALLY acquired root cache. -/
noncomputable def machineReady (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (ready bits hN))
      (some (SemiprimeD1StackCalls.configuration (done bits hN))) (readyBound bits hN) := by
  apply SemiprimeD1StackCalls.evalsCorrect originalInput (aux .output) (ctl .start) program
  let h := ready_run bits hc hN
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Actual compiled ready prefixes include the complete2011-field bank and the real return word. -/
theorem machine_prefix_cells (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits)
    (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q => q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (ready bits hN)))=some cfg) :
    (∑ k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      2012*(bits.length+RB.runBound bits+readyBound bits hN) := by
  have he := SemiprimeD1StackCalls.run_correct originalInput (aux .output) (ctl .start) program fuel (ready bits hN)
  have hh := he.trans hr
  cases hrun : C.run program fuel (ready bits hN) with
  | none => rw [hrun] at hh;cases hh
  | some finish =>
    rw [hrun] at hh
    have hc' : SemiprimeD1StackCalls.configuration finish=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells bits hc hN fuel finish hrun
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsReady
