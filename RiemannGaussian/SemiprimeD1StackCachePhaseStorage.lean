/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseClock
/-! # All238 actual data roles and real returns at every compiled prefix
Both accepted and rejected bounds follow the SAME full literal source and its
own halt. Every retained heap/cache/child/output/shadow word is counted.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseStorage
open SemiprimeD1StackCachePhase SemiprimeD1StackCachePhaseExecution SemiprimeD1StackCachePhaseProjection
open SemiprimeD1StackCachePhaseInputBounds SemiprimeD1StackCachePhaseClock
open SemiprimeD1StackJetFoldWords (Modes modeTape)
local notation "ctl" => Label.local
/-- The initially empty fold/cache bank contains only its literal supplied child tape. -/
theorem fold_initial_length (children:List Bool) (k:Fold.Stack) :
    ((Fold.initial [] [] children).data k).length ≤ children.length :=by
  rw [SemiprimeD1StackJetFoldState.initial_data]
  by_cases hex:∃s,k=SemiprimeD1StackJetFoldState.address s
  · obtain ⟨s,rfl⟩:=hex
    rw [SemiprimeD1StackJetFoldState.data_get]
    cases s <;> first | exact Nat.le_refl _ | exact Nat.zero_le _
  · have hk:∀s,k≠SemiprimeD1StackJetFoldState.address s:=by simpa only [not_exists] using hex
    rw [SemiprimeD1StackJetFoldState.data_other _ _ hk]
    exact Nat.zero_le _
/-- Every actual initialized238-role word is paid by one of the four physical input tapes. -/
theorem initial_role_bound (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (modes:Modes) (k:Stack) :
    ((source banks i modes).data k).length ≤ inputSize banks i modes :=by
  rcases k with k|k
  · exact (SemiprimeD1StackFreshBankRestoreBounds.initial_length (heap banks) (counter banks) (reference banks i) k).trans
      (by change SemiprimeD1StackFreshBankRestoreBounds.inputSize banks i ≤ inputSize banks i modes
          unfold inputSize
          omega)
  · rcases k with k|k
    · exact (fold_initial_length (modeTape modes) k).trans (by unfold inputSize;omega)
    · rcases k with k|k <;> exact Nat.zero_le _
/-- Generic actual halt-to-prefix bound, before any original bank or phase expression is instantiated. -/
theorem prefix_of_halt (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (modes:Modes)
    (target:Stack→List Bool) (t:Nat)
    (ht:t ≤ polynomial banks i modes)
    (hstop:SemiprimeD1StackCalls.run program t (source banks i modes)=
      some (⟨none,none,none,target,[]⟩:C.State Stack Label))
    (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (source banks i modes)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 10^85*(inputSize banks i modes+1)^16 :=by
  have htime:fuel ≤ t:=by
    by_contra hn
    have he:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hh:SemiprimeD1StackCalls.run program 1 (⟨none,none,none,target,[]⟩:C.State Stack Label)=none:=rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputSize banks i modes)
    _ _ (initial_role_bound banks i modes) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length) ≤ 238*(inputSize banks i modes+fuel):=by
    calc
      _ ≤ ∑_k:Stack,(inputSize banks i modes+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have hp:inputSize banks i modes+1 ≤ (inputSize banks i modes+1)^16:=by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega:1 ≤ inputSize banks i modes+1) (by decide:1 ≤ 16)
  unfold polynomial at ht
  norm_num only at ht ⊢
  omega
/-- Transfer of the full physical-prefix bound to the actual compiled machine. -/
theorem machine_prefix_of_halt (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (modes:Modes)
    (target:Stack→List Bool) (t:Nat) (ht:t ≤ polynomial banks i modes)
    (hstop:SemiprimeD1StackCalls.run program t (source banks i modes)=
      some (⟨none,none,none,target,[]⟩:C.State Stack Label)) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (source banks i modes)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 10^85*(inputSize banks i modes+1)^16 :=by
  have he:=SemiprimeD1StackCalls.run_correct (restoreStack Restore.originalInput)
    (blockStack (Blocks.aux .output)) (ctl .start) program fuel (source banks i modes)
  have hh:=he.trans hr
  cases hout:SemiprimeD1StackCalls.run program fuel (source banks i modes) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hc:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_of_halt banks i modes target t ht hstop fuel out hout
/-- Accepted compiled prefixes count all238 roles and actual returns, with no cache/work projection. -/
theorem machine_prefix_cells (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (axes:List Nat)
    (hp:∀r∈axes,0<r) (p:List Bool) (q:Nat) (hq:0<q) (newP:List Bool) (modes:Modes)
    (hv:ValidCache banks[i.val] axes p q newP) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (source banks i modes)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 10^85*(inputSize banks i modes+1)^16 :=by
  obtain ⟨t,ht,he⟩:=source_run_bounded banks i axes hp p q hq newP modes hv
  exact machine_prefix_of_halt banks i modes (result banks i axes p q newP modes) t ht he fuel cfg hr
/-- Rejected compiled prefixes have the SAME complete238-role bound, retaining unused literal children. -/
theorem machine_rejected_prefix_cells (banks:List (Fresh.Stack→List Bool)) (i:Fin banks.length) (modes:Modes)
    (hg:banks[i.val] (Fresh.contextStack (Header.aux .valid))=[false]) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (source banks i modes)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 10^85*(inputSize banks i modes+1)^16 :=by
  obtain ⟨t,ht,he⟩:=rejected_run_bounded banks i modes hg
  exact machine_prefix_of_halt banks i modes (SemiprimeD1StackCachePhaseRejected.result banks i (modeTape modes)) t ht he fuel cfg hr
end RiemannGaussian.SemiprimeD1StackCachePhaseStorage
