/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerMaddExecution
/-! # Actual routing arithmetic time and all-prefix physical cells
The unary operands are actual internally acquired coordinate words. These
bounds concern the SAME real Copy/Product/Copy source, not a report transport.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackPortOwnerMaddBounds
open SemiprimeD1StackPortOwnerMadd SemiprimeD1StackPortOwnerMaddExecution
/-- Fixed polynomial bound already proved from actual nested calls. -/
def budget (a b c:ℕ) : ℕ := 5*a+5*c+5*(a*(2*b+3)+1)+10
/-- Exact finite role inventory of the actual arithmetic source. -/
theorem stack_card : Fintype.card Stack=7 := by decide
/-- Actual prepared-coordinate machine execution, with no slot/cost answer input. -/
noncomputable def machineMadd (a b c:ℕ) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial a b c))
      (some (SemiprimeD1StackCalls.configuration (done a b c))) (budget a b c) := by
  apply SemiprimeD1StackCalls.evalsCorrect (.inl .a) (.inr .output) (.inl .start) program
  let time:=Classical.choose (source_run a b c)
  have hspec:=Classical.choose_spec (source_run a b c)
  exact ⟨⟨time,hspec.2⟩,hspec.1⟩
/-- Every successful prefix is bounded by its actual proved terminal trace. -/
theorem prefix_fuel_le (a b c fuel:ℕ) (out:C.State Stack Label)
    (hr:C.run program fuel (initial a b c)=some out) : fuel≤budget a b c := by
  obtain ⟨time,ht,he⟩:=source_run a b c
  have hf:fuel≤time:=by
    by_contra hn
    have hh:fuel=time+(1+(fuel-(time+1))):=by omega
    rw [hh,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run program 1 (done a b c)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- Every source prefix counts all seven Boolean data stacks and real return cells. -/
theorem prefix_cells (a b c fuel:ℕ) (out:C.State Stack Label)
    (hr:C.run program fuel (initial a b c)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤8*(a+b+c+budget a b c) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (a+b+c) _ out (by
    intro k;rcases k with k|k <;> cases k <;>
      simp [initial,data,SemiprimeD1StackUnaryDivmod.unary] <;> omega) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤7*(a+b+c+fuel):=by
    calc
      _≤∑_k:Stack,(a+b+c+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le a b c fuel out hr
  omega
/-- Same complete inventory for every genuine compiled-machine arithmetic prefix. -/
theorem machine_prefix_cells (a b c fuel:ℕ) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial a b c)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤8*(a+b+c+budget a b c) := by
  have he:=SemiprimeD1StackCalls.run_correct (.inl .a) (.inr .output) (.inl .start) program fuel (initial a b c)
  change (C.run program fuel (initial a b c)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial a b c))) at he
  have hh:=he.trans hr
  cases hc:C.run program fuel (initial a b c) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells a b c fuel out hc
end RiemannGaussian.SemiprimeD1StackPortOwnerMaddBounds
