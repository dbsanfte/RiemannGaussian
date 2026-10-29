/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateBounds
/-! # Genuine compiled two-tape source and all21-role/return prefix resources
The certificate honestly starts with actual retained phase-block bytes and an actual binary coordinate.
It supplies neither a coordinate cache, rank, precision, getter nor native clock.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryCoordinateResources
open SemiprimeD1StackRecoveryCoordinate
open SemiprimeD1StackRecoveryCoordinateEncoding (Phases tape)
open SemiprimeD1StackRecoveryCoordinateExecution SemiprimeD1StackRecoveryCoordinateBounds
open SemiprimeD1StackCalls (run configuration)
/-- Both genuinely initialized phase-bank/query words are paid by their physical tape lengths. -/
theorem initial_length (phases:Phases) (key:List Bool) (k:Stack):
    ((initial (tape phases) key).data k).length ≤resource phases key:=by
  change (input (tape phases) key k).length ≤_
  simp only [input,Function.update_apply]
  split_ifs <;> simp only [List.length_nil,resource] <;> omega
/-- Same deterministic successful source halt bounds every successful actual prefix. -/
theorem prefix_fuel (phases:Phases) (key:List Bool) (fuel:Nat) (out:C.State Stack Label)
    (hr:run program fuel (initial (tape phases) key)=some out):fuel ≤runBound phases key:=by
  have he:=source_run phases key
  have hh:run program 1 (done phases key)=none:=rfl
  have hf:fuel ≤timeBound phases key:=by
    by_contra hn
    have h:fuel=timeBound phases key+(1+(fuel-(timeBound phases key+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hh,Option.bind_none] at hr
    cases hr
  exact hf.trans (timeBound_le phases key)
/-- All21 allocated data roles, including all binary-reader work roles, are counted. -/
theorem word_sum (words:Stack → List Bool) (cap:Nat) (h:∀k,(words k).length ≤cap):
    (∑k:Stack,(words k).length) ≤21*cap:=by
  calc
    _ ≤∑_k:Stack,cap:=Finset.sum_le_sum (fun k _=>h k)
    _=21*cap:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
/-- Every actual source prefix pays all21 tapes and every real return cell. -/
theorem prefix_cells (phases:Phases) (key:List Bool) (fuel:Nat) (out:C.State Stack Label)
    (hr:run program fuel (initial (tape phases) key)=some out):
    (∑k:Stack,(out.data k).length)+out.frames.length ≤22*(resource phases key+runBound phases key):=by
  have ht:=prefix_fuel phases key fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (resource phases key) _ _
    (initial_length phases key) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ _ hr
  change out.frames.length ≤0+fuel at hf
  have hs:=word_sum out.data (resource phases key+fuel) hd
  omega
/-- Fixed quartic memory bound includes all data/shadow/actual return cells. -/
theorem prefix_cells_quartic (phases:Phases) (key:List Bool) (fuel:Nat) (out:C.State Stack Label)
    (hr:run program fuel (initial (tape phases) key)=some out):
    (∑k:Stack,(out.data k).length)+out.frames.length ≤100000000000000*(resource phases key+1)^4:=by
  have hh:=prefix_cells phases key fuel out hr
  have hp:resource phases key ≤(resource phases key+1)^4:=by
    have h:resource phases key+1 ≤(resource phases key+1)^4:=by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega:1 ≤resource phases key+1) (by decide:1 ≤4)
    omega
  unfold runBound at hh
  omega
/-- Genuine fixed finite-machine certificate from the two actual physical input words. -/
noncomputable def coordinateInTime (phases:Phases) (key:List Bool):
    StateTransition.EvalsToInTime machine.step (configuration (initial (tape phases) key))
      (some (configuration (done phases key))) (runBound phases key):=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .phases) output (.local .start) program
  have h:=source_run_bounded phases key
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Every genuine compiled prefix obeys the same21-tape and actual-return quartic bound. -/
theorem machine_prefix_cells (phases:Phases) (key:List Bool) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (configuration (initial (tape phases) key)))=some cfg):
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤100000000000000*(resource phases key+1)^4:=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .phases) output (.local .start) program fuel (initial (tape phases) key)
  have hh:=he.trans hr
  cases hout:run program fuel (initial (tape phases) key) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells_quartic phases key fuel out hout
/-- Each actual source instruction expands into at most four genuine finite statements. -/
theorem compile_depth (pc:Label):SemiprimeD1StackBytecode.statementDepth (machine.m pc) ≤4:=by
  change SemiprimeD1StackBytecode.statementDepth
    (SemiprimeD1StackCalls.compileInstruction (Label.local Control.start) (program pc)) ≤4
  exact SemiprimeD1StackCalls.compile_depth (Label.local Control.start) (program pc)
end RiemannGaussian.SemiprimeD1StackRecoveryCoordinateResources
