/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseChildContextExecution
/-! # Own VALUE-charged clock and all80 physical roles, including real returns
Both old/new ranks and numeric precision VALUES are included: a unary width cache
cannot be bounded polynomially in the binary precision word's length alone.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1StackPhaseChildContextBounds
open SemiprimeD1StackPhaseChildContext SemiprimeD1StackPhaseChildContextPrimitives
open SemiprimeD1StackPhaseChildContextArithmetic SemiprimeD1StackPhaseChildContextComponents
open SemiprimeD1StackPhaseChildContextExecution
/-- Physical input bytes plus BOTH actual old/new rank and precision VALUE inventories. -/
def resource (a u edges : Nat) (t p : List Bool) (axes : List Nat) : Nat :=
  edges+a+u+t.length+p.length+1+
  SemiprimeD1StackJetContextBounds.resource axes p+
  SemiprimeD1StackJetContextBounds.resource (count a u edges t::axes) (precision a u edges t p)+
  count a u edges t+10
/-- Accepted ready execution pays the two real quadratic context sources; rejection costs four. -/
theorem ready_polynomial (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x) :
    readyBound a u edges t p axes≤ 1000000*(resource a u edges t p axes+1)^2 :=by
  by_cases hg:good a u edges t=true
  · have hq:=((good_true a u edges t).mp hg).2
    have h0:=SemiprimeD1StackJetContextBounds.budget_polynomial axes hp p
    have h1:=SemiprimeD1StackJetContextBounds.budget_polynomial (count a u edges t::axes)
      (child_positive axes hp _ hq) (precision a u edges t p)
    have hR0:SemiprimeD1StackJetContextBounds.resource axes p≤ resource a u edges t p axes:=by unfold resource;omega
    have hR1:SemiprimeD1StackJetContextBounds.resource (count a u edges t::axes) (precision a u edges t p)≤ resource a u edges t p axes:=by unfold resource;omega
    have hc:p.length+(header axes).length+count a u edges t+(precision a u edges t p).length+1≤ resource a u edges t p axes:=by
      unfold resource SemiprimeD1StackJetContextBounds.resource header
      omega
    have h0':SemiprimeD1StackJetContextCorrectness.budget axes p≤ 1000*(resource a u edges t p axes+1)^2:=h0.trans (by gcongr)
    have h1':SemiprimeD1StackJetContextCorrectness.budget (count a u edges t::axes) (precision a u edges t p)≤ 1000*(resource a u edges t p axes+1)^2:=h1.trans (by gcongr)
    have hs:resource a u edges t p axes+1≤(resource a u edges t p axes+1)^2:=Nat.le_pow (by decide : 0<(2:Nat))
    simp only [readyBound,hg,ite_true]
    unfold SemiprimeD1StackPhaseChildContextSteps.acquireBound
    omega
  · have hf:good a u edges t=false:=Bool.eq_false_iff.mpr hg
    simp only [readyBound,hf,Bool.false_eq_true,ite_false]
    have hs:0<(resource a u edges t p axes+1)^2:=pow_pos (by omega) _
    omega
/-- Whole clock is a fixed quartic in the explicitly VALUE-charged physical inventory. -/
theorem run_polynomial (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x) :
    runBound a u edges t p axes≤ 1000000000000000*(resource a u edges t p axes+1)^4 :=by
  have hb:=ready_polynomial a u edges t p axes hp
  have hi:edges+a+u+t.length+p.length+1≤ resource a u edges t p axes+1:=by unfold resource;omega
  have hpow:(edges+a+u+t.length+p.length+1)^4≤(resource a u edges t p axes+1)^4:=by gcongr
  have hs:(resource a u edges t p axes+1)^2≤(resource a u edges t p axes+1)^4:=by
    calc
      _≤((resource a u edges t p axes+1)^2)^2:=Nat.le_pow (by decide : 0<(2:Nat))
      _=_:=by ring
  have hz:0<(resource a u edges t p axes+1)^4:=pow_pos (by omega) _
  unfold runBound SemiprimeD1StackPhaseWorkingPrecisionExecution.runBound
  omega
/-- Every old-context input/cache/work field is charged without a rank supplier. -/
theorem old_input_bound (axes : List Bool) (k : J.Stack) : (oldInput axes k).length≤ axes.length :=by
  rcases k with k|k
  · exact Nat.zero_le _
  · rcases k with k|k
    · exact Nat.zero_le _
    · fin_cases k <;> simp [oldInput,SemiprimeD1StackJetContext.initial,SemiprimeD1StackJetContext.bank,SemiprimeD1StackJetContext.cached]
/-- Every not-yet-acquired child-context field is physically empty. -/
theorem empty_context (k : J.Stack) : emptyContext k=[] :=by
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · fin_cases k <;> rfl
/-- Whole front door contains only actual phase inputs and the caller's old axes header. -/
theorem initial_bound (a u edges : Nat) (t p : List Bool) (axes : List Nat) (k : Stack) :
    ((initial a u edges t p (header axes)).data k).length≤ edges+a+u+t.length+p.length+(header axes).length :=by
  rcases k with k|k
  · exact (SemiprimeD1StackPhaseWorkingPrecisionBounds.initial_bound a u edges t p k).trans (by omega)
  · rcases k with k|k
    · exact (old_input_bound (header axes) k).trans (by omega)
    · rcases k with k|k
      · change (emptyContext k).length≤ _
        rw [empty_context];exact Nat.zero_le _
      · cases k <;> exact Nat.zero_le _
/-- Actual retained P48 cache is bounded by its OWN frozen source execution. -/
theorem phase_cache_bound (a u edges : Nat) (t p : List Bool) (k : P.Stack) :
    (phase a u edges t p k).length≤ edges+a+u+t.length+p.length+
      SemiprimeD1StackPhaseWorkingPrecisionExecution.runBound a u edges t p :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackPhaseWorkingPrecisionExecution.source_run a u edges t p
  have hd:=SemiprimeD1StackReturnLink.run_data_bound P.program q (edges+a+u+t.length+p.length) _ _
    (SemiprimeD1StackPhaseWorkingPrecisionBounds.initial_bound a u edges t p) hr
  exact (hd k).trans (by omega)
/-- Ready source reuses all ACTUALLY acquired P48 cells, while both contexts still need acquisition. -/
theorem ready_initial_bound (a u edges : Nat) (t p : List Bool) (axes : List Nat) (k : Stack) :
    ((ready a u edges t p (header axes)).data k).length≤ edges+a+u+t.length+p.length+(header axes).length+
      SemiprimeD1StackPhaseWorkingPrecisionExecution.runBound a u edges t p :=by
  rcases k with k|k
  · exact (phase_cache_bound a u edges t p k).trans (by omega)
  · rcases k with k|k
    · exact (old_input_bound (header axes) k).trans (by omega)
    · rcases k with k|k
      · change (emptyContext k).length≤ _
        rw [empty_context];exact Nat.zero_le _
      · cases k <;> exact Nat.zero_le _
/-- Every whole-source prefix ends before the SAME fixed program's proved halt. -/
theorem prefix_fuel_le (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x)
    (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial a u edges t p (header axes))=some out) :
    fuel≤ runBound a u edges t p axes :=by
  obtain ⟨q,hq,hfinal⟩:=source_run a u edges t p axes hp
  have hf:fuel≤ q:=by
    by_contra hn
    have he:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hfinal,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:SemiprimeD1StackCalls.run program 1 (done a u edges t p axes)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans hq
/-- Ready prefixes stop at their OWN actual cache-continuation halt. -/
theorem ready_prefix_fuel_le (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x)
    (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (ready a u edges t p (header axes))=some out) :
    fuel≤ readyBound a u edges t p axes :=by
  obtain ⟨q,hq,hfinal⟩:=ready_run a u edges t p axes hp
  have hf:fuel≤ q:=by
    by_contra hn
    have he:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hfinal,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:SemiprimeD1StackCalls.run program 1 (done a u edges t p axes)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans hq
/-- Complete allocated inventory counts ALL80 roles and actual physical return cells. -/
theorem prefix_cells (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x)
    (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial a u edges t p (header axes))=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤ 1000000000000000000*(resource a u edges t p axes+1)^4 :=by
  let B:=edges+a+u+t.length+p.length+(header axes).length
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel B _ out (initial_bound a u edges t p axes) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤ 80*(B+fuel):=by
    calc
      _≤∑_k:Stack,(B+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht: fuel≤ 1000000000000000*(resource a u edges t p axes+1)^4:=
    (prefix_fuel_le a u edges t p axes hp fuel out hr).trans (run_polynomial a u edges t p axes hp)
  have hB:B≤ resource a u edges t p axes+1:=by unfold B resource SemiprimeD1StackJetContextBounds.resource header;omega
  have hz:resource a u edges t p axes+1≤(resource a u edges t p axes+1)^4:=Nat.le_pow (by decide : 0<(4:Nat))
  omega
/-- Ready storage includes every retained P48 cell and both actual acquired context expansions. -/
theorem ready_prefix_cells (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x)
    (fuel : Nat) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (ready a u edges t p (header axes))=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤ 1000000000000000000*(resource a u edges t p axes+1)^4 :=by
  let B:=edges+a+u+t.length+p.length+(header axes).length+SemiprimeD1StackPhaseWorkingPrecisionExecution.runBound a u edges t p
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel B _ out (ready_initial_bound a u edges t p axes) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤ 80*(B+fuel):=by
    calc
      _≤∑_k:Stack,(B+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht: fuel≤ 1000000*(resource a u edges t p axes+1)^2:=
    (ready_prefix_fuel_le a u edges t p axes hp fuel out hr).trans (ready_polynomial a u edges t p axes hp)
  have hB0:edges+a+u+t.length+p.length+(header axes).length≤ resource a u edges t p axes+1:=by
    unfold resource SemiprimeD1StackJetContextBounds.resource header;omega
  have hi:edges+a+u+t.length+p.length+1≤ resource a u edges t p axes+1:=by unfold resource;omega
  have hpow:(edges+a+u+t.length+p.length+1)^4≤(resource a u edges t p axes+1)^4:=by gcongr
  have hs2:(resource a u edges t p axes+1)^2≤(resource a u edges t p axes+1)^4:=by
    calc
      _≤((resource a u edges t p axes+1)^2)^2:=Nat.le_pow (by decide : 0<(2:Nat))
      _=_:=by ring
  have hz:resource a u edges t p axes+1≤(resource a u edges t p axes+1)^4:=Nat.le_pow (by decide : 0<(4:Nat))
  unfold B SemiprimeD1StackPhaseWorkingPrecisionExecution.runBound at hs
  omega
/-- SAME all80-role/real-return cap for the actual compiled whole machine. -/
theorem machine_prefix_cells (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x)
    (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial a u edges t p (header axes))))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤ 1000000000000000000*(resource a u edges t p axes+1)^4 :=by
  have he:=SemiprimeD1StackCalls.run_correct (oldStack J.axesCache) (childStack J.rankCache) .start program fuel (initial a u edges t p (header axes))
  change (SemiprimeD1StackCalls.run program fuel (initial a u edges t p (header axes))).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial a u edges t p (header axes)))) at he
  have hh:=he.trans hr
  cases hc:SemiprimeD1StackCalls.run program fuel (initial a u edges t p (header axes)) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells a u edges t p axes hp fuel out hc
/-- SAME all80-role/real-return cap for the actual compiled ready machine. -/
theorem ready_machine_prefix_cells (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x)
    (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (ready a u edges t p (header axes))))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤ 1000000000000000000*(resource a u edges t p axes+1)^4 :=by
  have he:=SemiprimeD1StackCalls.run_correct (oldStack J.axesCache) (childStack J.rankCache) .start program fuel (ready a u edges t p (header axes))
  change (SemiprimeD1StackCalls.run program fuel (ready a u edges t p (header axes))).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (ready a u edges t p (header axes)))) at he
  have hh:=he.trans hr
  cases hc:SemiprimeD1StackCalls.run program fuel (ready a u edges t p (header axes)) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact ready_prefix_cells a u edges t p axes hp fuel out hc
end RiemannGaussian.SemiprimeD1StackPhaseChildContextBounds
