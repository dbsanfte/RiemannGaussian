/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRecipeNumeric
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRecipeBounds
open SemiprimeD1StackPortOwnerRecipe SemiprimeD1StackPortOwnerRecipeSpec
open SemiprimeD1StackPortOwnerRecipeAcquisition SemiprimeD1StackPortOwnerRecipeDecision
open SemiprimeD1StackPortOwnerRecipeEmit SemiprimeD1StackPortOwnerRecipeExecution
open SemiprimeD1StackPortOwnerRecipeNumeric
/-- Exact fixed physical data-role inventory, before every original graph dimension. -/
theorem stack_card : Fintype.card Stack=56 := by decide
/-- Whole SAME-source chronological bound, including all actual primitive preparation and emitter calls. -/
theorem budget_cap (p:Counters) (tag:Tag) : budget p tag≤50000*(cap p+1)^2 := by
  have hp:=remainingBudget_le p 41 0
  have hm:=mass_le p (selected p tag)
  obtain ⟨h9,hr,ht,hd,hg,_⟩:=operand_caps p
  unfold budget
  nlinarith
/-- Fresh scalar power substitution, independent of original dimensions. -/
theorem fourth_numeric (s:ℕ) (hs:1 ≤ s) : 50000*(s^2+1)^2≤200000*s^4 := by
  have hs2:1 ≤ s^2:=by nlinarith
  have hh:s^2+1≤2*s^2:=by omega
  calc
    _≤50000*(2*s^2)^2:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hh 2)
    _=_:=by ring
/-- One fixed fourth-power bound in the ACTUAL acquired operand inventory. -/
theorem budget_polynomial (p:Counters) (tag:Tag) : budget p tag≤200000*(volume p+1)^4 := by
  exact (budget_cap p tag).trans (fourth_numeric (volume p+1) (by omega))
/-- Actual all-constructor procedure execution has a fixed acquired-byte polynomial. -/
theorem source_run_polynomial (p:Counters) (tag:Tag) (ht:p.tag=(tagCode tag).val) (hd:0<p.digits) :
    ∃time≤200000*(volume p+1)^4,C.run program time (initial (words p))=some (done p tag) := by
  obtain ⟨time,he,hr⟩:=source_run p tag ht hd
  exact ⟨time,he.trans (budget_polynomial p tag),hr⟩
/-- No successful prefix can pass the SAME actual source's proved final halt. -/
theorem prefix_fuel (p:Counters) (tag:Tag) (ht:p.tag=(tagCode tag).val) (hd:0<p.digits)
    (fuel:ℕ) (out:C.State Stack Label) (hr:C.run program fuel (initial (words p))=some out) :
    fuel≤budget p tag := by
  obtain ⟨time,he,hfinish⟩:=source_run p tag ht hd
  have hf:fuel≤time:=by
    by_contra hn
    have hh:fuel=time+(1+(fuel-(time+1))):=by omega
    rw [hh,SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run program 1 (done p tag)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans he
/-- Every source prefix counts ALL56 Boolean roles and all real finite return frames. -/
theorem prefix_cells (p:Counters) (tag:Tag) (ht:p.tag=(tagCode tag).val) (hd:0<p.digits)
    (fuel:ℕ) (out:C.State Stack Label) (hr:C.run program fuel (initial (words p))=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤
      57*(2*(cap p+1)^2+budget p tag) := by
  have hwidth:=SemiprimeD1StackReturnLink.run_data_bound program fuel (2*(cap p+1)^2) _ out (by
    intro k
    rcases k with k|k
    · exact input_length_le p k
    · exact Nat.zero_le _) hr
  have hframes:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hframes
  have hs:(∑k:Stack,(out.data k).length)≤56*(2*(cap p+1)^2+fuel):=by
    calc
      _≤∑_k:Stack,(2*(cap p+1)^2+fuel):=Finset.sum_le_sum (fun k _=>hwidth k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have hf:=prefix_fuel p tag ht hd fuel out hr
  omega
/-- The SAME actual compiled machine inherits the proved genuine execution trace. -/
noncomputable def machineRecipe (p:Counters) (tag:Tag) (ht:p.tag=(tagCode tag).val) (hd:0<p.digits) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (words p)))
      (some (SemiprimeD1StackCalls.configuration (done p tag))) (200000*(volume p+1)^4) := by
  apply SemiprimeD1StackCalls.evalsCorrect (arg .r) (aux .output) (.local .start) program
  let time:=Classical.choose (source_run_polynomial p tag ht hd)
  have hs:=Classical.choose_spec (source_run_polynomial p tag ht hd)
  exact ⟨⟨time,hs.2⟩,hs.1⟩
/-- Same complete physical role/return inventory at every genuine compiled-machine prefix. -/
theorem machine_prefix_cells (p:Counters) (tag:Tag) (ht:p.tag=(tagCode tag).val) (hd:0<p.digits)
    (fuel:ℕ) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial (words p))))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      57*(2*(cap p+1)^2+budget p tag) := by
  have he:=SemiprimeD1StackCalls.run_correct (arg .r) (aux .output) (.local .start) program fuel (initial (words p))
  change (C.run program fuel (initial (words p))).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial (words p)))) at he
  have hh:=he.trans hr
  cases hc:C.run program fuel (initial (words p)) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells p tag ht hd fuel out hc
end RiemannGaussian.SemiprimeD1StackPortOwnerRecipeBounds
