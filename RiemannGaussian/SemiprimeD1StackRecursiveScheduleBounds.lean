/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecursiveScheduleExecution

/-! # One own clock and complete storage for the physical recursive schedule gate -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackRecursiveScheduleBounds
open SemiprimeD1StackRecursiveSchedule SemiprimeD1StackRecursiveScheduleExecution
/-- Same actual machine execution, with every nested call and conditional cost included. -/
noncomputable def scheduleInTime (a:List Bool) (v:SemiprimeD1StackScheduleActive.Param→Nat) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (initial a v))
      (some (SemiprimeD1StackCalls.configuration (done a v))) (runBound a v) := by
  apply SemiprimeD1StackCalls.evalsCorrect (guardStack .leaf) (guardStack .output) (.inl .start) program
  let h:=source_run a v
  let t:=Classical.choose h
  have ht:=Classical.choose_spec h
  exact ⟨⟨t,ht.2⟩,ht.1⟩
/-- No physical operand or unused alias shadow is omitted from the initial inventory. -/
theorem initial_role_bound (a:List Bool) (v:SemiprimeD1StackScheduleActive.Param→Nat) :
    ∀k:Stack,((initial a v).data k).length ≤ A.volume v+a.length := by
  intro k
  cases k with
  | inl k=>
    cases k <;> simp [initial,payload,SemiprimeD1StackScheduleActiveExecution.start,
      SemiprimeD1StackScheduleActive.data,A.unaryWords,A.volume]
    all_goals omega
  | inr k=>
    cases k <;> simp [initial,payload,S.initial,SemiprimeD1StackScheduleSuccessor.data]
/-- Successful prefixes stop at the same actual program's final halt. -/
theorem prefix_fuel_le (a:List Bool) (v:SemiprimeD1StackScheduleActive.Param→Nat)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial a v)=some out) : fuel ≤ runBound a v := by
  obtain ⟨t,ht,he⟩:=source_run a v
  have hf:fuel ≤ t := by
    by_contra hn
    have h:fuel=t+(1+(fuel-(t+1))) := by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz:SemiprimeD1StackCalls.run program 1 (done a v)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- Every one of sixteen physical data roles and every actual return cell is counted. -/
theorem prefix_cells (a:List Bool) (v:SemiprimeD1StackScheduleActive.Param→Nat)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial a v)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 17*(A.volume v+a.length+runBound a v) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (A.volume v+a.length)
    (initial a v) out (initial_role_bound a v) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel (initial a v) out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length) ≤ 16*(A.volume v+a.length+fuel) := by
    calc
      _ ≤ ∑_k:Stack,(A.volume v+a.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le a v fuel out hr
  omega
/-- Same all-role inventory at every real compiled-machine prefix. -/
theorem machine_prefix_cells (a:List Bool) (v:SemiprimeD1StackScheduleActive.Param→Nat)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial a v)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 17*(A.volume v+a.length+runBound a v) := by
  have he:=SemiprimeD1StackCalls.run_correct (guardStack .leaf) (guardStack .output)
    (.inl .start) program fuel (initial a v)
  change (SemiprimeD1StackCalls.run program fuel (initial a v)).map
    SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial a v))) at he
  rw [hr] at he
  cases hrun:SemiprimeD1StackCalls.run program fuel (initial a v) with
  | none=>rw [hrun] at he;cases he
  | some out=>
    rw [hrun] at he
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj he
    subst cfg
    exact prefix_cells a v fuel out hrun
/-- Every actual transition has at most four fundamental compiled commands. -/
theorem compile_depth (pc:Label) :
    SemiprimeD1StackBytecode.statementDepth (machine.m pc) ≤ 4 :=
  SemiprimeD1StackCalls.compile_depth (.inl .start:Label) (program pc)
end RiemannGaussian.SemiprimeD1StackRecursiveScheduleBounds
