/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesBounds
/-! # Genuine compiled two-tape source and all25-role/return prefix resources
The certificate honestly starts with actual rows and actual nested child words.
It supplies neither a denominator list, product, row count nor native clock.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesResources
open SemiprimeD1StackRecoveryEntries
open SemiprimeD1StackRecoveryEntriesEncoding (childTape)
open SemiprimeD1StackRecoveryDenominatorEncoding (Row tape)
open SemiprimeD1StackRecoveryEntriesExecution SemiprimeD1StackRecoveryEntriesBounds
open SemiprimeD1StackCalls (run configuration)
/-- Both genuinely initialized words are paid by their physical tape lengths. -/
theorem initial_length (rs:List Row) (children:List (List (List Bool))) (k:Stack):
    ((initial (tape rs) (childTape children)).data k).length ≤resource rs children:=by
  change (input (tape rs) (childTape children) k).length ≤_
  simp only [input,Function.update_apply]
  split_ifs <;> simp only [List.length_nil,resource] <;> omega
/-- Same deterministic successful source halt bounds every successful actual prefix. -/
theorem prefix_fuel (rs:List Row) (children:List (List (List Bool))) (fuel:Nat) (out:C.State Stack Label)
    (hr:run program fuel (initial (tape rs) (childTape children))=some out):fuel ≤runBound rs children:=by
  have he:=source_run rs children
  have hh:run program 1 (done rs children)=none:=rfl
  have hf:fuel ≤timeBound rs children:=by
    by_contra hn
    have h:fuel=timeBound rs children+(1+(fuel-(timeBound rs children+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hh,Option.bind_none] at hr
    cases hr
  exact hf.trans (timeBound_le rs children)
/-- All25 allocated data roles, including both indexed query/value shadows, are counted. -/
theorem word_sum (words:Stack → List Bool) (cap:Nat) (h:∀k,(words k).length ≤cap):
    (∑k:Stack,(words k).length) ≤25*cap:=by
  calc
    _ ≤∑_k:Stack,cap:=Finset.sum_le_sum (fun k _=>h k)
    _=25*cap:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
/-- Every actual source prefix pays all25 tapes and every real return cell. -/
theorem prefix_cells (rs:List Row) (children:List (List (List Bool))) (fuel:Nat) (out:C.State Stack Label)
    (hr:run program fuel (initial (tape rs) (childTape children))=some out):
    (∑k:Stack,(out.data k).length)+out.frames.length ≤26*(resource rs children+runBound rs children):=by
  have ht:=prefix_fuel rs children fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (resource rs children) _ _
    (initial_length rs children) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ _ hr
  change out.frames.length ≤0+fuel at hf
  have hs:=word_sum out.data (resource rs children+fuel) hd
  omega
/-- Fixed quartic memory bound includes all data/shadow/actual return cells. -/
theorem prefix_cells_quartic (rs:List Row) (children:List (List (List Bool))) (fuel:Nat) (out:C.State Stack Label)
    (hr:run program fuel (initial (tape rs) (childTape children))=some out):
    (∑k:Stack,(out.data k).length)+out.frames.length ≤100000000000000*(resource rs children+1)^4:=by
  have hh:=prefix_cells rs children fuel out hr
  have hp:resource rs children ≤(resource rs children+1)^4:=by
    have h:resource rs children+1 ≤(resource rs children+1)^4:=by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega:1 ≤resource rs children+1) (by decide:1 ≤4)
    omega
  unfold runBound at hh
  omega
/-- Genuine fixed finite-machine certificate from the two actual physical input words. -/
noncomputable def entriesInTime (rs:List Row) (children:List (List (List Bool))):
    StateTransition.EvalsToInTime machine.step (configuration (initial (tape rs) (childTape children)))
      (some (configuration (done rs children))) (runBound rs children):=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .rows) output (.local .start) program
  have h:=source_run_bounded rs children
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Every genuine compiled prefix obeys the same25-tape and actual-return quartic bound. -/
theorem machine_prefix_cells (rs:List Row) (children:List (List (List Bool))) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (configuration (initial (tape rs) (childTape children))))=some cfg):
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤100000000000000*(resource rs children+1)^4:=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .rows) output (.local .start) program fuel (initial (tape rs) (childTape children))
  have hh:=he.trans hr
  cases hout:run program fuel (initial (tape rs) (childTape children)) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells_quartic rs children fuel out hout
/-- Each actual source instruction expands into at most four genuine finite statements. -/
theorem compile_depth (pc:Label):SemiprimeD1StackBytecode.statementDepth (machine.m pc) ≤4:=by
  change SemiprimeD1StackBytecode.statementDepth
    (SemiprimeD1StackCalls.compileInstruction (Label.local Control.start) (program pc)) ≤4
  exact SemiprimeD1StackCalls.compile_depth (Label.local Control.start) (program pc)
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesResources
