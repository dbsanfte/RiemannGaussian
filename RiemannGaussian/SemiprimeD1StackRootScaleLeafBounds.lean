/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootScaleLeafExecution
/-! # Complete25-role and real-return bounds for both actual entries -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1StackRootScaleLeafBounds
open SemiprimeD1StackRootScaleLeaf SemiprimeD1StackRootScaleLeafComponents
open SemiprimeD1StackRootScaleLeafExecution
/-- Actual full-source prefixes cannot exceed the proved actual halt. -/
theorem prefix_fuel_le (bits : List Bool) (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial bits)=some out) :fuel≤runBound bits :=by
  obtain ⟨t,ht,hh⟩:=source_run bits
  have hf:fuel≤t:=by
    by_contra hn
    have he:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hh,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:SemiprimeD1StackCalls.run program 1 (done bits)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- The ready entry's own clock excludes the earlier metadata source call. -/
theorem ready_prefix_fuel_le (bits : List Bool) (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (ready bits)=some out) :fuel≤readyBound bits :=by
  obtain ⟨t,ht,hh⟩:=ready_run bits
  have hf:fuel≤t:=by
    by_contra hn
    have he:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hh,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:SemiprimeD1StackCalls.run program 1 (done bits)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- Only the original binary word is present at the whole-source entry. -/
theorem initial_bound (bits : List Bool) (j : Stack) :((initial bits).data j).length≤bits.length :=by
  rcases j with j|j
  · exact SemiprimeD1StackRootScheduleBounds.initial_bound bits j
  · rcases j with j|j <;> exact Nat.zero_le _
/-- Every old cached field is bounded using its ACTUAL concrete producing trace,
not an unknown cache/time supplier or a decoded numerical magnitude. -/
theorem old_cache_bound (bits : List Bool) (j : R.Stack) :
    (SemiprimeD1StackRootScheduleExecution.result bits j).length≤
      bits.length+SemiprimeD1StackRootScheduleExecution.runBound bits :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackRootScheduleExecution.source_run bits
  have hd:=SemiprimeD1StackReturnLink.run_data_bound R.program t bits.length (R.initial bits)
    (SemiprimeD1StackRootScheduleExecution.done bits) (SemiprimeD1StackRootScheduleBounds.initial_bound bits) hr j
  exact hd.trans (by omega)
/-- ALL ready input roles are actual cache words or EMPTY fresh work/output. -/
theorem ready_initial_bound (bits : List Bool) (j : Stack) :((ready bits).data j).length≤
    bits.length+SemiprimeD1StackRootScheduleExecution.runBound bits :=by
  rcases j with j|j
  · exact old_cache_bound bits j
  · rcases j with j|j <;> exact Nat.zero_le _
/-- Full actual prefix counts all25 Boolean stacks and every real return cell. -/
theorem prefix_cells (bits : List Bool) (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial bits)=some out) :
    (∑j:Stack,(out.data j).length)+out.frames.length≤26*(bits.length+runBound bits) :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length (initial bits) out (initial_bound bits) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel (initial bits) out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑j:Stack,(out.data j).length)≤25*(bits.length+fuel):=by
    calc
      _≤∑_j:Stack,(bits.length+fuel):=Finset.sum_le_sum (fun j _=>hd j)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits fuel out hr
  omega
/-- The ready prefix counts the entire old cache and all fresh work/output/frame
cells, even while real scaling creates its largest unary metadata word. -/
theorem ready_prefix_cells (bits : List Bool) (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (ready bits)=some out) :
    (∑j:Stack,(out.data j).length)+out.frames.length≤
      26*(bits.length+SemiprimeD1StackRootScheduleExecution.runBound bits+readyBound bits) :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel
    (bits.length+SemiprimeD1StackRootScheduleExecution.runBound bits) (ready bits) out (ready_initial_bound bits) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel (ready bits) out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑j:Stack,(out.data j).length)≤25*(bits.length+SemiprimeD1StackRootScheduleExecution.runBound bits+fuel):=by
    calc
      _≤∑_j:Stack,(bits.length+SemiprimeD1StackRootScheduleExecution.runBound bits+fuel):=Finset.sum_le_sum (fun j _=>hd j)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=ready_prefix_fuel_le bits fuel out hr
  omega
/-- One original-width cubic bounds the entire whole-source footprint. -/
theorem polynomial_space (bits : List Bool) :
    26*(bits.length+runBound bits)≤1000000000000000*(bits.length+1)^3 :=by
  have hn:bits.length≤(bits.length+1)^3:=by
    have h:bits.length+1≤(bits.length+1)^3:=by simpa only [pow_one] using Nat.pow_le_pow_right (by omega :1≤bits.length+1) (by decide :1≤3)
    omega
  unfold runBound
  omega
/-- The same cubic also bounds every ready-stage cache and fresh/return cell. -/
theorem ready_polynomial_space (bits : List Bool) :
    26*(bits.length+SemiprimeD1StackRootScheduleExecution.runBound bits+readyBound bits)≤
      1000000000000000*(bits.length+1)^3 :=by
  have hn:bits.length≤(bits.length+1)^3:=by
    have h:bits.length+1≤(bits.length+1)^3:=by simpa only [pow_one] using Nat.pow_le_pow_right (by omega :1≤bits.length+1) (by decide :1≤3)
    omega
  unfold readyBound SemiprimeD1StackRootScheduleExecution.runBound
  omega
/-- Complete actual one-input finite-machine prefix, including all real frames. -/
theorem machine_prefix_cells (bits : List Bool) (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑j:Stack,(cfg.stk (some j)).length)+(cfg.stk none).length≤26*(bits.length+runBound bits) :=by
  rw [initial_eq] at hr
  have he:=SemiprimeD1StackCalls.run_correct (rootStack (R.boot .input)) (aux .leaf) Label.start program fuel (initial bits)
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
/-- Complete actual ready-stage finite-machine prefix with the same real return accounting. -/
theorem ready_machine_prefix_cells (bits : List Bool) (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (ready bits)))=some cfg) :
    (∑j:Stack,(cfg.stk (some j)).length)+(cfg.stk none).length≤
      26*(bits.length+SemiprimeD1StackRootScheduleExecution.runBound bits+readyBound bits) :=by
  have he:=SemiprimeD1StackCalls.run_correct (rootStack (R.boot .input)) (aux .leaf) Label.start program fuel (ready bits)
  change (SemiprimeD1StackCalls.run program fuel (ready bits)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (ready bits))) at he
  have hh:=he.trans hr
  cases hrun:SemiprimeD1StackCalls.run program fuel (ready bits) with
  | none=>rw [hrun] at hh;cases hh
  | some out=>
    rw [hrun] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact ready_prefix_cells bits fuel out hrun
/-- Constant elementary-command bound pays the fixed compiled statements too. -/
theorem compile_depth (pc : Label) :SemiprimeD1StackBytecode.statementDepth (machine.m pc)≤4 :=
  SemiprimeD1StackCalls.compile_depth Label.start (program pc)
end RiemannGaussian.SemiprimeD1StackRootScaleLeafBounds
