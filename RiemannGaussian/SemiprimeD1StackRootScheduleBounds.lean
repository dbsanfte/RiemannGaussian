/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootScheduleExecution
/-! # Own polynomial root-schedule time and all15-role/return storage -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackRootScheduleBounds
open SemiprimeD1StackRootSchedule SemiprimeD1StackRootScheduleExecution
/-- Every successful prefix ends before the proved actual source halt. -/
theorem prefix_fuel_le (bits : List Bool) (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial bits)=some out) : fuel≤runBound bits := by
  obtain ⟨t,ht,hh⟩:=source_run bits
  have hf:fuel≤t:=by
    by_contra hn
    have he:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hh,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:SemiprimeD1StackCalls.run program 1 (done bits)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- Every actual initial data role is bounded by the ONLY supplied binary word. -/
theorem initial_bound (bits : List Bool) (k : Stack) : ((initial bits).data k).length≤bits.length := by
  rcases k with k|k
  · cases k <;> simp [initial,input,store,Boot.payload]
  · rcases k with k|k <;> exact Nat.zero_le _
/-- No Boolean role, marker, divisor/remainder cell or real return cell is omitted. -/
theorem prefix_cells (bits : List Bool) (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial bits)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤16*(bits.length+runBound bits) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length (initial bits) out (initial_bound bits) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel (initial bits) out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤15*(bits.length+fuel):=by
    calc
      _≤∑_k:Stack,(bits.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits fuel out hr
  omega
/-- Same complete physical inventory at EVERY prefix of the actual one-input machine. -/
theorem machine_prefix_cells (bits : List Bool) (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤16*(bits.length+runBound bits) := by
  rw [initial_eq] at hr
  have he:=SemiprimeD1StackCalls.run_correct (boot .input) (aux .exponent) Label.start program fuel (initial bits)
  change (SemiprimeD1StackCalls.run program fuel (initial bits)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial bits))) at he
  have hh:=he.trans hr
  cases hrun:SemiprimeD1StackCalls.run program fuel (initial bits) with
  | none=>rw [hrun] at hh;cases hh
  | some out=>
    rw [hrun] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells bits fuel out hrun
/-- A fixed explicit cubic bounds the full actual bit-cell footprint. -/
theorem polynomial_space (bits : List Bool) :
    16*(bits.length+runBound bits)≤2000000000*(bits.length+1)^3 := by
  have hn:bits.length≤(bits.length+1)^3:=by
    have h:bits.length+1≤(bits.length+1)^3:=by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1≤bits.length+1) (by decide : 1≤3)
    omega
  unfold runBound
  omega
/-- Every compiled source transition has at most four fundamental stack commands. -/
theorem compile_depth (pc : Label) :
    SemiprimeD1StackBytecode.statementDepth (machine.m pc)≤4 :=
  SemiprimeD1StackCalls.compile_depth Label.start (program pc)
end RiemannGaussian.SemiprimeD1StackRootScheduleBounds
