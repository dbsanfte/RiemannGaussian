/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishBounds
/-! # All35 actual data tapes and genuine return cells at every recovery prefix
The machine certificate honestly starts from the three prepared physical input
words. It does not assert original-N acquisition of a recovery numerator.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishResources
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishExecution
open SemiprimeD1StackRecoveryFinishBounds
open SemiprimeD1StackCalls (run configuration)
open SemiprimeBitIndexClipping (SignedWord)
/-- Every actual initialized word is charged to the three physical input word lengths. -/
theorem initial_length (n:SignedWord) (d:List Bool) (p:Nat) (k:Stack):
    ((initial (B.signedTape n) d (List.replicate p true)).data k).length ≤resource n d p:=by
  change (input (B.signedTape n) d (List.replicate p true) k).length ≤_
  simp only [input,Function.update_apply]
  split_ifs
  all_goals simp only [List.length_replicate,List.length_nil,resource]
  all_goals omega
/-- The same actual successful source halt bounds every deterministic successful prefix. -/
theorem prefix_fuel (n:SignedWord) (d:List Bool) (hd:0 < SemiprimeBitArithmetic.bitValue d) (p fuel:Nat)
    (out:C.State Stack Label)
    (hr:run program fuel (initial (B.signedTape n) d (List.replicate p true))=some out):
    fuel ≤runBound n d p:=by
  have he:=source_run n d hd p
  have hh:run program 1 (done n d p)=none:=rfl
  have hf:fuel ≤timeBound n d p:=by
    by_contra hn
    have h:fuel=timeBound n d p+(1+(fuel-(timeBound n d p+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hh,Option.bind_none] at hr
    cases hr
  exact hf.trans (timeBound_le n d p)
/-- Finite sum bound counts every allocated role, including the unused add WIDTH shadow. -/
theorem word_sum (words:Stack → List Bool) (cap:Nat) (h:∀k,(words k).length ≤cap):
    (∑k:Stack,(words k).length) ≤35*cap:=by
  calc
    _ ≤∑_k:Stack,cap:=Finset.sum_le_sum (fun k _=>h k)
    _=35*cap:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
/-- Every actual prefix pays all35 data words and its real return stack. -/
theorem prefix_cells (n:SignedWord) (d:List Bool) (hd:0 < SemiprimeBitArithmetic.bitValue d) (p fuel:Nat)
    (out:C.State Stack Label)
    (hr:run program fuel (initial (B.signedTape n) d (List.replicate p true))=some out):
    (∑k:Stack,(out.data k).length)+out.frames.length ≤36*(resource n d p+runBound n d p):=by
  have ht:=prefix_fuel n d hd p fuel out hr
  have hd':=SemiprimeD1StackReturnLink.run_data_bound program fuel (resource n d p) _ _
    (initial_length n d p) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ _ hr
  change out.frames.length ≤0+fuel at hf
  have hs:=word_sum out.data (resource n d p+fuel) hd'
  omega
/-- Fixed quartic all-tape/real-return cap uses only actual input bytes. -/
theorem prefix_cells_quartic (n:SignedWord) (d:List Bool) (hd:0 < SemiprimeBitArithmetic.bitValue d)
    (p fuel:Nat) (out:C.State Stack Label)
    (hr:run program fuel (initial (B.signedTape n) d (List.replicate p true))=some out):
    (∑k:Stack,(out.data k).length)+out.frames.length ≤100000000000000*(resource n d p+1)^4:=by
  have hh:=prefix_cells n d hd p fuel out hr
  have hp:resource n d p ≤(resource n d p+1)^4:=by
    have h:resource n d p+1 ≤(resource n d p+1)^4:=by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega:1 ≤resource n d p+1) (by decide:1 ≤4)
    omega
  unfold runBound at hh
  omega
/-- Genuine compiled finite-machine certificate from exactly the three actual input words. -/
noncomputable def recoveryInTime (n:SignedWord) (d:List Bool)
    (hd:0 < SemiprimeBitArithmetic.bitValue d) (p:Nat):
    StateTransition.EvalsToInTime machine.step
      (configuration (initial (B.signedTape n) d (List.replicate p true)))
      (some (configuration (done n d p))) (runBound n d p):=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .numerator) output (.local .start) program
  have h:=source_run_bounded n d hd p
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- All genuine compiled prefixes obey the same35-tape and actual return-cell cap. -/
theorem machine_prefix_cells (n:SignedWord) (d:List Bool) (hd:0 < SemiprimeBitArithmetic.bitValue d)
    (p fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel]
      (some (configuration (initial (B.signedTape n) d (List.replicate p true))))=some cfg):
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤100000000000000*(resource n d p+1)^4:=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .numerator) output (.local .start) program fuel
    (initial (B.signedTape n) d (List.replicate p true))
  have hh:=he.trans hr
  cases hout:run program fuel (initial (B.signedTape n) d (List.replicate p true)) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells_quartic n d hd p fuel out hout
/-- Every source instruction expands to at most four genuine fixed-machine statements. -/
theorem compile_depth (pc:Label):SemiprimeD1StackBytecode.statementDepth (machine.m pc) ≤4:=by
  change SemiprimeD1StackBytecode.statementDepth
    (SemiprimeD1StackCalls.compileInstruction (Label.local Control.start) (program pc)) ≤4
  exact SemiprimeD1StackCalls.compile_depth (Label.local Control.start) (program pc)
end RiemannGaussian.SemiprimeD1StackRecoveryFinishResources
