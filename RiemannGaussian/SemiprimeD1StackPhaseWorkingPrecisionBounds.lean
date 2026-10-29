/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionExecution
/-! # All48 physical roles and real returns, for whole and acquired-cache entries -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionBounds
open SemiprimeD1StackPhaseWorkingPrecision SemiprimeD1StackPhaseWorkingPrecisionComponents
open SemiprimeD1StackPhaseWorkingPrecisionExecution
/-- Whole initial bank contains ONLY actual original physical input words. -/
theorem initial_bound (a u edges : Nat) (t p : List Bool) (k : Stack) :
    ((initial a u edges t p).data k).length≤ edges+a+u+t.length+p.length :=by
  rcases k with k|k
  · exact SemiprimeD1StackPhaseWorkingPrecisionMetadataBounds.initial_bound a u edges t p k
  · exact Nat.zero_le _
/-- Cache bound is obtained from the ACTUAL frozen metadata source trace, never advice. -/
theorem cache_bound (a u edges : Nat) (t p : List Bool) (j : M.Stack) :
    (old a u edges t p j).length≤ edges+a+u+t.length+p.length+1000000*(edges+a+u+t.length+p.length+1)^2 :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackPhaseWorkingPrecisionMetadataExecution.source_run a u edges t p
  have hd:=SemiprimeD1StackReturnLink.run_data_bound M.program q (edges+a+u+t.length+p.length)
    (SemiprimeD1StackPhaseWorkingPrecisionMetadata.initial a u edges t p)
    (SemiprimeD1StackPhaseWorkingPrecisionMetadataExecution.done a u edges t p)
    (SemiprimeD1StackPhaseWorkingPrecisionMetadataBounds.initial_bound a u edges t p) hr
  have hx:(old a u edges t p j).length≤ edges+a+u+t.length+p.length+q:=hd j
  change q≤1000000*(edges+a+u+t.length+p.length+1)^2 at hq
  omega
/-- Every old cache field is charged at the ready front door; all new binary work is empty. -/
theorem ready_initial_bound (a u edges : Nat) (t p : List Bool) (k : Stack) :
    ((ready a u edges t p).data k).length≤ edges+a+u+t.length+p.length+1000000*(edges+a+u+t.length+p.length+1)^2 :=by
  rcases k with k|k
  · exact cache_bound a u edges t p k
  · exact Nat.zero_le _
/-- No successful whole-source prefix can extend beyond the actual halt. -/
theorem prefix_fuel_le (a u edges : Nat) (t p : List Bool) (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial a u edges t p)=some out) : fuel≤ runBound a u edges t p :=by
  obtain ⟨q,hq,hfinal⟩:=source_run a u edges t p
  have hf:fuel≤ q:=by
    by_contra hn
    have he:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hfinal,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz:SemiprimeD1StackCalls.run program 1 (done a u edges t p)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans hq
/-- The ready continuation has its own actual halt and own smaller polynomial clock. -/
theorem ready_prefix_fuel_le (a u edges : Nat) (t p : List Bool) (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (ready a u edges t p)=some out) : fuel≤ readyBound a u edges t p :=by
  obtain ⟨q,hq,hfinal⟩:=ready_run a u edges t p
  have hf:fuel≤ q:=by
    by_contra hn
    have he:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hfinal,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz:SemiprimeD1StackCalls.run program 1 (done a u edges t p)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans hq
/-- Complete inventory includes ALL48 role words, cached unary metadata and actual returns. -/
theorem prefix_cells (a u edges : Nat) (t p : List Bool) (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial a u edges t p)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤1000000000000000*(edges+a+u+t.length+p.length+1)^4 :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (edges+a+u+t.length+p.length) _ out
    (initial_bound a u edges t p) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤48*(edges+a+u+t.length+p.length+fuel):=by
    calc
      _≤∑_k:Stack,(edges+a+u+t.length+p.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le a u edges t p fuel out hr
  unfold runBound at ht
  have hp:edges+a+u+t.length+p.length+1≤(edges+a+u+t.length+p.length+1)^4:=Nat.le_pow (by decide : 0<(4:Nat))
  omega
/-- Every ready prefix counts all48 roles INCLUDING every actually acquired old cache cell. -/
theorem ready_prefix_cells (a u edges : Nat) (t p : List Bool) (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (ready a u edges t p)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤1000000000000000*(edges+a+u+t.length+p.length+1)^4 :=by
  let J:=edges+a+u+t.length+p.length
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (J+1000000*(J+1)^2) _ out
    (ready_initial_bound a u edges t p) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤48*(J+1000000*(J+1)^2+fuel):=by
    calc
      _≤∑_k:Stack,(J+1000000*(J+1)^2+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=ready_prefix_fuel_le a u edges t p fuel out hr
  change fuel≤1000000000*(J+1)^4 at ht
  have hp:J+1≤(J+1)^4:=Nat.le_pow (by decide : 0<(4:Nat))
  have hsq:(J+1)^2≤(J+1)^4:=by
    calc
      _≤((J+1)^2)^2:=Nat.le_pow (by decide : 0<(2:Nat))
      _=_:=by ring
  change _≤1000000000000000*(J+1)^4
  omega
/-- SAME all48/real-return storage bound for every reached actual compiled-machine prefix. -/
theorem machine_prefix_cells (a u edges : Nat) (t p : List Bool) (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial a u edges t p)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤1000000000000000*(edges+a+u+t.length+p.length+1)^4 :=by
  have he:=SemiprimeD1StackCalls.run_correct (metadataStack (M.aux .edges)) (aux .output) .start program fuel (initial a u edges t p)
  change (SemiprimeD1StackCalls.run program fuel (initial a u edges t p)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial a u edges t p))) at he
  have hh:=he.trans hr
  cases hc:SemiprimeD1StackCalls.run program fuel (initial a u edges t p) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells a u edges t p fuel out hc
/-- SAME inventory for the genuine SAME-machine ready-cache continuation. -/
theorem ready_machine_prefix_cells (a u edges : Nat) (t p : List Bool) (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (ready a u edges t p)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤1000000000000000*(edges+a+u+t.length+p.length+1)^4 :=by
  have he:=SemiprimeD1StackCalls.run_correct (metadataStack (M.aux .edges)) (aux .output) .start program fuel (ready a u edges t p)
  change (SemiprimeD1StackCalls.run program fuel (ready a u edges t p)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (ready a u edges t p))) at he
  have hh:=he.trans hr
  cases hc:SemiprimeD1StackCalls.run program fuel (ready a u edges t p) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact ready_prefix_cells a u edges t p fuel out hc
end RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionBounds
