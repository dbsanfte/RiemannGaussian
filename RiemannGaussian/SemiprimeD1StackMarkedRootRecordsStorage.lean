/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsExecution
/-! # Genuine initialization and all2011 data words plus every actual return cell
The prefix estimates use the SAME complete actual halted trace. Retained old
cache words and the unused shared-N shadow are included in the sum.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsStorage
open SemiprimeD1StackMarkedRootRecords SemiprimeD1StackMarkedRootRecordsExecution
open SemiprimeBitArithmetic (bitValue)
/-- Whole source physically initializes only ONE binary-N word. -/
theorem input_single (bits : List Bool) : input bits=fun k => if k=originalInput then bits else [] := by
  funext k
  rcases k with k|k
  · change R.input bits k=_
    rw [SemiprimeD1StackRootNetworkRecordsResources.input_single]
    simp only [originalInput,root,Sum.inl.injEq]
  · rcases k with k|k
    · rfl
    · rcases k with k|k
      · simp [input,data,privateTable,originalInput,root]
      · rfl
/-- Actual finite-machine initialization is genuine Turing.initList on original binary N. -/
theorem initial_eq (bits : List Bool) : Turing.initList machine bits=
    SemiprimeD1StackCalls.configuration (initial bits) := by
  have hi : initial bits=SemiprimeD1StackCalls.initial originalInput (ctl .start) bits := by
    unfold initial SemiprimeD1StackCalls.initial
    rw [input_single]
  rw [hi]
  exact (SemiprimeD1StackCalls.initial_correct originalInput (aux .output) (ctl .start) program bits).symm
/-- Every original input role fits its physically supplied byte length. -/
theorem initial_length (bits : List Bool) (k : Stack) : ((initial bits).data k).length ≤ bits.length := by
  change (input bits k).length ≤ bits.length
  rw [input_single]
  by_cases h : k=originalInput <;> simp [h]
/-- A real successful prefix cannot continue beyond the actual proved halt. -/
theorem prefix_fuel_le (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits)
    (fuel : Nat) (finish : C.State Stack Label) (hr : C.run program fuel (initial bits)=some finish) :
    fuel ≤ timeBound bits hN := by
  obtain ⟨t,ht,he⟩ := source_run bits hc hN
  have hf : fuel ≤ t := by
    by_contra hn
    have h : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done bits hN)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- ALL2011 allocated roles, retained caches, alias shadow and actual return cells at EVERY source prefix. -/
theorem prefix_cells (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits)
    (fuel : Nat) (finish : C.State Stack Label) (hr : C.run program fuel (initial bits)=some finish) :
    (∑ k : Stack,(finish.data k).length)+finish.frames.length ≤ 2012*(bits.length+timeBound bits hN) := by
  have hd := SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length _ finish (initial_length bits) hr
  have hf := SemiprimeD1StackCalls.run_frame_bound program fuel _ finish hr
  change finish.frames.length ≤ 0+fuel at hf
  have ht := prefix_fuel_le bits hc hN fuel finish hr
  have hs : (∑ k : Stack,(finish.data k).length) ≤ 2011*(bits.length+fuel) := by
    calc
      _ ≤ ∑ _k : Stack,(bits.length+fuel) := Finset.sum_le_sum (fun k _ => hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  omega
/-- The SAME original-input source is an actual compiled finite-machine certificate. -/
noncomputable def sourceInTime (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits hN))) (timeBound bits hN) := by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect originalInput (aux .output) (ctl .start) program
  let h := source_run bits hc hN
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Every actual compiled prefix counts exactly the same2011 role words and real saved-return word. -/
theorem machine_prefix_cells (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits)
    (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q => q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑ k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 2012*(bits.length+timeBound bits hN) := by
  rw [initial_eq] at hr
  have he := SemiprimeD1StackCalls.run_correct originalInput (aux .output) (ctl .start) program fuel (initial bits)
  have hh := he.trans hr
  cases hrun : C.run program fuel (initial bits) with
  | none => rw [hrun] at hh;cases hh
  | some finish =>
    rw [hrun] at hh
    have hc' : SemiprimeD1StackCalls.configuration finish=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells bits hc hN fuel finish hrun
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsStorage
