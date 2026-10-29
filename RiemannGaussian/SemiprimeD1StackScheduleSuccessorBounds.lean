/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackScheduleSuccessorExecution

/-! # Own linear clock and all-stack space for the physical schedule successor -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackScheduleSuccessorBounds
open SemiprimeD1StackScheduleSuccessor SemiprimeD1StackScheduleSuccessorExecution
/-- Pairwise physical scan time is linear, including empty and odd words. -/
theorem halfTime_le (u:List Bool) : halfTime u ≤ 2*u.length+1 := by
  induction u using List.twoStepInduction with
  | nil => decide
  | singleton b => simp [halfTime]
  | cons_cons b c u ih _ => simp only [halfTime,List.length_cons];omega
/-- The same complete clock pays every actual copy, scan, return and halt. -/
theorem runTime_le (a u:List Bool) : runTime a u ≤ 20*(a.length+u.length+1) := by
  have h:=halfTime_le u
  have hd:=Nat.div_mul_le_self u.length 2
  unfold runTime
  omega
/-- Every compiled transition has bounded literal command depth. -/
theorem compile_depth (pc:Label) :
    SemiprimeD1StackBytecode.statementDepth (machine.m pc) ≤ 4 :=
  SemiprimeD1StackCalls.compile_depth (.inl .start:Label) (program pc)
/-- Actual compiled execution from the prepared payload, with its own linear clock. -/
def scheduleInTime (a u:List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial a u))
      (some (SemiprimeD1StackCalls.configuration (done a u)))
      (20*(a.length+u.length+1)) := by
  apply SemiprimeD1StackCalls.evalsCorrect Stack.levels Stack.nextExponent
    (.inl .start) program
  exact ⟨⟨runTime a u,source_run a u⟩,runTime_le a u⟩
/-- No successful executed prefix can extend beyond the actual final halt. -/
theorem prefix_fuel_le (a u:List Bool) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial a u)=some out) :
    fuel ≤ runTime a u := by
  by_contra hn
  have ht:fuel=runTime a u+(1+(fuel-(runTime a u+1))) := by omega
  rw [ht,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hz:SemiprimeD1StackCalls.run program 1 (done a u)=none := rfl
  rw [hz,Option.bind_none] at hr
  cases hr
/-- All six physical data stacks and every real return cell are charged. -/
theorem prefix_cells (a u:List Bool) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial a u)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤
      7*(a.length+u.length+20*(a.length+u.length+1)) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (a.length+u.length)
    (initial a u) out (by intro k;cases k <;> simp [initial,data]) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel (initial a u) out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length) ≤ 6*(a.length+u.length+fuel) := by
    calc
      _ ≤ ∑_k:Stack,(a.length+u.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht: fuel ≤ 20*(a.length+u.length+1) := (prefix_fuel_le a u fuel out hr).trans (runTime_le a u)
  omega
/-- The same inventory holds at every prefix of the actual compiled machine. -/
theorem machine_prefix_cells (a u:List Bool) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial a u)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      7*(a.length+u.length+20*(a.length+u.length+1)) := by
  have he:=SemiprimeD1StackCalls.run_correct Stack.levels Stack.nextExponent
    (.inl .start) program fuel (initial a u)
  change (SemiprimeD1StackCalls.run program fuel (initial a u)).map
    SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial a u))) at he
  rw [hr] at he
  cases hrun:SemiprimeD1StackCalls.run program fuel (initial a u) with
  | none => rw [hrun] at he;cases he
  | some out =>
    rw [hrun] at he
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj he
    subst cfg
    exact prefix_cells a u fuel out hrun
end RiemannGaussian.SemiprimeD1StackScheduleSuccessorBounds
