/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackScheduleActiveExecution

/-! # Own elapsed time and complete prefix storage of the active-call decision -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackScheduleActiveBounds
open SemiprimeD1StackScheduleActive SemiprimeD1StackScheduleActiveExecution
/-- Complete actual time bound, in actual retained bounded-metadata bytes. -/
def runBound (v:Param→Nat) : Nat := 200*(volume v+1)
/-- Same actual program executes within its own proved input-dependent bound. -/
noncomputable def guardInTime (v:Param→Nat) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (start v))
      (some (SemiprimeD1StackCalls.configuration (done v))) (runBound v) := by
  apply SemiprimeD1StackCalls.evalsCorrect Stack.leaf Stack.output (.inl (.left .leaf)) program
  let h:=source_run v
  let t:=Classical.choose h
  have ht:=Classical.choose_spec h
  exact ⟨⟨t,ht.2⟩,ht.1⟩
/-- Every retained parameter word is already paid by the physical input inventory. -/
theorem parameter_le (v:Param→Nat) (k:Param) : v k ≤ volume v := by
  cases k <;> unfold volume <;> omega
/-- A successful prefix cannot continue after the same actual final halt. -/
theorem prefix_fuel_le (v:Param→Nat) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (start v)=some out) : fuel ≤ runBound v := by
  obtain ⟨t,ht,he⟩:=source_run v
  have hf:fuel ≤ t := by
    by_contra hn
    have h:fuel=t+(1+(fuel-(t+1))) := by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz:SemiprimeD1StackCalls.run program 1 (done v)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- All ten physical roles, including copy/comparator work, and every real return cell. -/
theorem prefix_cells (v:Param→Nat) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (start v)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 11*(volume v+runBound v) := by
  have hi:∀k:Stack,((start v).data k).length ≤ volume v := by
    intro k;cases k <;> simp only [start,data,unaryWords,List.length_replicate,List.length_nil]
    all_goals first | exact parameter_le v _ | exact Nat.zero_le _
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (volume v) (start v) out hi hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel (start v) out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length) ≤ 10*(volume v+fuel) := by
    calc
      _ ≤ ∑_k:Stack,(volume v+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le v fuel out hr
  omega
/-- Same complete storage inventory at every actual compiled-machine prefix. -/
theorem machine_prefix_cells (v:Param→Nat) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (start v)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 11*(volume v+runBound v) := by
  have he:=SemiprimeD1StackCalls.run_correct Stack.leaf Stack.output
    (.inl (.left .leaf)) program fuel (start v)
  change (SemiprimeD1StackCalls.run program fuel (start v)).map
    SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (start v))) at he
  rw [hr] at he
  cases hrun:SemiprimeD1StackCalls.run program fuel (start v) with
  | none => rw [hrun] at he;cases he
  | some out =>
    rw [hrun] at he
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj he
    subst cfg
    exact prefix_cells v fuel out hrun
/-- Each compiled transition uses at most four literal fundamental commands. -/
theorem compile_depth (pc:Label) :
    SemiprimeD1StackBytecode.statementDepth (machine.m pc) ≤ 4 :=
  SemiprimeD1StackCalls.compile_depth (.inl (.left .leaf):Label) (program pc)
end RiemannGaussian.SemiprimeD1StackScheduleActiveBounds
