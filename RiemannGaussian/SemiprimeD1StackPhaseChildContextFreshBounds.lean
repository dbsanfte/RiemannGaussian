/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseChildContextFreshExecution
/-! # Own whole/ready clocks and ALL85 physical roles plus actual returns
Rank and precision VALUE materialization remains explicitly charged by the
original context resource. There is no polynomial-in-binary-precision-bytes claim.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1StackPhaseChildContextFreshBounds
open SemiprimeD1StackPhaseChildContextFresh SemiprimeD1StackPhaseChildContextFreshComponents
open SemiprimeD1StackPhaseChildContextFreshExecution
/-- Exact original VALUE-charged context resource, including both ranks and precision widths. -/
abbrev resource :=SemiprimeD1StackPhaseChildContextBounds.resource
/-- Both actual rank VALUES are already included in the honest context resource. -/
theorem ranks_bound (a u edges : Nat) (t p : List Bool) (axes : List Nat) :
    rank a u edges t axes+axes.prod+1≤ resource a u edges t p axes+1 :=by
  unfold resource SemiprimeD1StackPhaseChildContextBounds.resource SemiprimeD1StackJetContextBounds.resource rank
  omega
/-- Complete cache-ready allocation clock is linear in the original VALUE-charged inventory. -/
theorem ready_polynomial (a u edges : Nat) (t p : List Bool) (axes : List Nat) :
    readyBound a u edges t axes≤ 100*(resource a u edges t p axes+1) :=by
  have h:=ranks_bound a u edges t p axes
  unfold readyBound
  split <;> omega
/-- Whole-source cost sums the real original phase/context pipeline and all fresh-vector bytes. -/
theorem run_polynomial (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x) :
    runBound a u edges t p axes≤ 1000000000000000000*(resource a u edges t p axes+1)^4 :=by
  have h0:=SemiprimeD1StackPhaseChildContextBounds.run_polynomial a u edges t p axes hp
  change _≤ 1000000000000000*(resource a u edges t p axes+1)^4 at h0
  have h1:=ready_polynomial a u edges t p axes
  have hz:resource a u edges t p axes+1≤(resource a u edges t p axes+1)^4:=Nat.le_pow (by decide : 0<(4:Nat))
  unfold runBound
  omega
/-- P48-cache entry pays real old/new context VALUE expansion and complete allocation. -/
theorem phase_ready_polynomial (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x) :
    phaseReadyBound a u edges t p axes≤ 1000000000*(resource a u edges t p axes+1)^2 :=by
  have h0:=SemiprimeD1StackPhaseChildContextBounds.ready_polynomial a u edges t p axes hp
  change _≤ 1000000*(resource a u edges t p axes+1)^2 at h0
  have h1:=ready_polynomial a u edges t p axes
  have hz:resource a u edges t p axes+1≤(resource a u edges t p axes+1)^2:=Nat.le_pow (by decide : 0<(2:Nat))
  unfold phaseReadyBound
  omega
/-- Whole initial inventory contains no context/rank/q/P/vector answers. -/
theorem initial_bound (a u edges : Nat) (t p : List Bool) (axes : List Nat) (k : Stack) :
    ((initial a u edges t p (Old.header axes)).data k).length≤ edges+a+u+t.length+p.length+(Old.header axes).length :=by
  rcases k with k|k
  · exact SemiprimeD1StackPhaseChildContextBounds.initial_bound a u edges t p axes k
  · cases k <;> exact Nat.zero_le _
/-- Every retained80-role context-cache cell is bounded from its ACTUAL whole original source. -/
theorem cache_bound (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x) (k : H.Stack) :
    (cache a u edges t p axes k).length≤ edges+a+u+t.length+p.length+(Old.header axes).length+
      SemiprimeD1StackPhaseChildContextExecution.runBound a u edges t p axes :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackPhaseChildContextExecution.source_run a u edges t p axes hp
  have hd:=SemiprimeD1StackReturnLink.run_data_bound H.program q
    (edges+a+u+t.length+p.length+(Old.header axes).length) _ _
    (SemiprimeD1StackPhaseChildContextBounds.initial_bound a u edges t p axes) hr
  exact (hd k).trans (by omega)
/-- Direct cache-ready entry retains every physically acquired context/P48 field. -/
theorem ready_initial_bound (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x) (k : Stack) :
    ((ready a u edges t p axes).data k).length≤ edges+a+u+t.length+p.length+(Old.header axes).length+
      SemiprimeD1StackPhaseChildContextExecution.runBound a u edges t p axes :=by
  rcases k with k|k
  · exact cache_bound a u edges t p axes hp k
  · cases k <;> exact Nat.zero_le _
/-- P48-ready entry has only actual P48 cache and original oldheader, with both contexts unacquired. -/
theorem phase_ready_initial_bound (a u edges : Nat) (t p : List Bool) (axes : List Nat) (k : Stack) :
    ((phaseReady a u edges t p (Old.header axes)).data k).length≤ edges+a+u+t.length+p.length+(Old.header axes).length+
      SemiprimeD1StackPhaseWorkingPrecisionExecution.runBound a u edges t p :=by
  rcases k with k|k
  · exact SemiprimeD1StackPhaseChildContextBounds.ready_initial_bound a u edges t p axes k
  · cases k <;> exact Nat.zero_le _
/-- Successful prefixes stop at the actual halt; all allocated fields and real return cells count. -/
theorem inventory (start stop : C.State Stack Label) (B cap fuel : Nat) (out : C.State Stack Label)
    (hi : ∀k,(start.data k).length≤ B) (hf : start.frames=[])
    (hh : ∃q≤ cap,SemiprimeD1StackCalls.run program q start=some stop) (hs : stop.pc=none)
    (hr : SemiprimeD1StackCalls.run program fuel start=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤ 86*(B+cap+1) :=by
  obtain ⟨q,hq,hstop⟩:=hh
  have ht:fuel≤ q:=by
    by_contra hn
    have he:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:SemiprimeD1StackCalls.run program 1 stop=none:=by cases stop with | mk pc flag ret data frames=>cases hs;rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel B start out hi hr
  have hframes:=SemiprimeD1StackCalls.run_frame_bound program fuel start out hr
  rw [hf,List.length_nil] at hframes
  have hsum:(∑k:Stack,(out.data k).length)≤ 85*(B+fuel):=by
    calc
      _≤∑_k:Stack,(B+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  omega
/-- Every whole-source prefix charges ALL85 roles and real returns, including both context expansions. -/
theorem prefix_cells (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x)
    (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial a u edges t p (Old.header axes))=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤ 1000000000000000000000*(resource a u edges t p axes+1)^4 :=by
  have h0:=inventory _ (done a u edges t p axes) _ _ fuel out (initial_bound a u edges t p axes) rfl (source_run a u edges t p axes hp) rfl hr
  have ht:=run_polynomial a u edges t p axes hp
  have hi:edges+a+u+t.length+p.length+(Old.header axes).length≤ resource a u edges t p axes+1:=by
    unfold resource SemiprimeD1StackPhaseChildContextBounds.resource SemiprimeD1StackJetContextBounds.resource Old.header
    omega
  have hz:resource a u edges t p axes+1≤(resource a u edges t p axes+1)^4:=Nat.le_pow (by decide : 0<(4:Nat))
  omega
/-- Direct context-ready prefixes count ALL retained cache words plus every fresh allocator role/return. -/
theorem ready_prefix_cells (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x)
    (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (ready a u edges t p axes)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤ 1000000000000000000000*(resource a u edges t p axes+1)^4 :=by
  have h0:=inventory _ (done a u edges t p axes) _ _ fuel out (ready_initial_bound a u edges t p axes hp) rfl (ready_run a u edges t p axes) rfl hr
  have ht:=ready_polynomial a u edges t p axes
  have hc:=SemiprimeD1StackPhaseChildContextBounds.run_polynomial a u edges t p axes hp
  change _≤ 1000000000000000*(resource a u edges t p axes+1)^4 at hc
  have hi:edges+a+u+t.length+p.length+(Old.header axes).length≤ resource a u edges t p axes+1:=by
    unfold resource SemiprimeD1StackPhaseChildContextBounds.resource SemiprimeD1StackJetContextBounds.resource Old.header
    omega
  have hz:resource a u edges t p axes+1≤(resource a u edges t p axes+1)^4:=Nat.le_pow (by decide : 0<(4:Nat))
  omega
/-- P48-ready prefixes include the actual old/new context acquisitions and every physical field/return. -/
theorem phase_ready_prefix_cells (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x)
    (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (phaseReady a u edges t p (Old.header axes))=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤ 1000000000000000000000*(resource a u edges t p axes+1)^4 :=by
  have h0:=inventory _ (done a u edges t p axes) _ _ fuel out (phase_ready_initial_bound a u edges t p axes) rfl (phase_ready_run a u edges t p axes hp) rfl hr
  have ht:=phase_ready_polynomial a u edges t p axes hp
  have hi:edges+a+u+t.length+p.length+(Old.header axes).length≤ resource a u edges t p axes+1:=by
    unfold resource SemiprimeD1StackPhaseChildContextBounds.resource SemiprimeD1StackJetContextBounds.resource Old.header
    omega
  have hI:edges+a+u+t.length+p.length+1≤ resource a u edges t p axes+1:=by unfold resource SemiprimeD1StackPhaseChildContextBounds.resource;omega
  have hpow:(edges+a+u+t.length+p.length+1)^4≤(resource a u edges t p axes+1)^4:=by gcongr
  have hs2:(resource a u edges t p axes+1)^2≤(resource a u edges t p axes+1)^4:=by
    calc
      _≤((resource a u edges t p axes+1)^2)^2:=Nat.le_pow (by decide : 0<(2:Nat))
      _=_:=by ring
  have hz:resource a u edges t p axes+1≤(resource a u edges t p axes+1)^4:=Nat.le_pow (by decide : 0<(4:Nat))
  unfold SemiprimeD1StackPhaseWorkingPrecisionExecution.runBound at h0
  omega
/-- SAME all85/real-return bound for every actual compiled whole prefix. -/
theorem machine_prefix_cells (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x)
    (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial a u edges t p (Old.header axes))))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤ 1000000000000000000000*(resource a u edges t p axes+1)^4 :=by
  have he:=SemiprimeD1StackCalls.run_correct (contextStack (H.oldStack H.J.axesCache)) (aux .output) .start program fuel (initial a u edges t p (Old.header axes))
  change (SemiprimeD1StackCalls.run program fuel (initial a u edges t p (Old.header axes))).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial a u edges t p (Old.header axes)))) at he
  have hh:=he.trans hr
  cases hc:SemiprimeD1StackCalls.run program fuel (initial a u edges t p (Old.header axes)) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells a u edges t p axes hp fuel out hc
/-- SAME all85/real-return bound for every actual compiled ready_ prefix. -/
theorem ready_machine_prefix_cells (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x)
    (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (ready a u edges t p axes)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤ 1000000000000000000000*(resource a u edges t p axes+1)^4 :=by
  have he:=SemiprimeD1StackCalls.run_correct (contextStack (H.oldStack H.J.axesCache)) (aux .output) .start program fuel (ready a u edges t p axes)
  change (SemiprimeD1StackCalls.run program fuel (ready a u edges t p axes)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (ready a u edges t p axes))) at he
  have hh:=he.trans hr
  cases hc:SemiprimeD1StackCalls.run program fuel (ready a u edges t p axes) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact ready_prefix_cells a u edges t p axes hp fuel out hc
/-- SAME all85/real-return bound for every actual compiled phase_ready_ prefix. -/
theorem phase_ready_machine_prefix_cells (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x)
    (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (phaseReady a u edges t p (Old.header axes))))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤ 1000000000000000000000*(resource a u edges t p axes+1)^4 :=by
  have he:=SemiprimeD1StackCalls.run_correct (contextStack (H.oldStack H.J.axesCache)) (aux .output) .start program fuel (phaseReady a u edges t p (Old.header axes))
  change (SemiprimeD1StackCalls.run program fuel (phaseReady a u edges t p (Old.header axes))).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (phaseReady a u edges t p (Old.header axes)))) at he
  have hh:=he.trans hr
  cases hc:SemiprimeD1StackCalls.run program fuel (phaseReady a u edges t p (Old.header axes)) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact phase_ready_prefix_cells a u edges t p axes hp fuel out hc
end RiemannGaussian.SemiprimeD1StackPhaseChildContextFreshBounds
