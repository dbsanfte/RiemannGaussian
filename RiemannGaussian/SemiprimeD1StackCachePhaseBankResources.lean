/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankBounds
/-! # All246 physical tapes and genuine return cells
The fixed polynomial counts every retained source word, every stopped callee
cache and every physical parser/logger/cleanup/return prefix of this program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankResources
open SemiprimeD1StackCachePhaseBank SemiprimeD1StackCachePhaseBankEncoding
open SemiprimeD1StackCachePhaseBankInputBounds SemiprimeD1StackCachePhaseBankBounds
attribute [local irreducible] SemiprimeD1StackRootPhaseFreshRecordsEncoding.result
  SemiprimeD1StackRootPhaseParametersEncoding.phases
/-- Abstract four-word input length bound, before original graph substitution. -/
theorem initial_length (hp cn refs children:List Bool) (k:Stack):
    ((initial hp cn refs children).data k).length ≤hp.length+cn.length+refs.length+children.length:=by
  rcases k with k|k
  · change ((P.input hp cn [] []) k).length ≤_
    rw [SemiprimeD1StackCachePhaseBankBinding.input_base]
    dsimp only
    split_ifs <;> first | omega | exact Nat.zero_le _
  · cases k <;> first | exact Nat.zero_le _ | change refs.length ≤_;omega | change children.length ≤_;omega
/-- Every actual initialized word is paid by the four actual input tapes. -/
theorem source_length (bits:List Bool) (requests:List (Request bits)) (k:Stack):
    ((source bits requests).data k).length ≤resource bits requests:=
  initial_length _ _ _ _ k
/-- Successful halt bounds every actual prefix, including all real outer and recursive return cells. -/
theorem prefix_cells (bits:List Bool) (requests:List (Request bits)) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (source bits requests)=some out):
    (∑k:Stack,(out.data k).length)+out.frames.length ≤10^103*(capacity bits requests)^18:=by
  obtain ⟨t,ht,hstop⟩:=source_run_bounded bits requests
  have htime:fuel ≤t:=by
    by_contra hn
    have he:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hh:SemiprimeD1StackCalls.run program 1 (done bits requests)=none:=rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (resource bits requests)
    _ _ (source_length bits requests) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length) ≤246*(resource bits requests+fuel):=by
    calc
      _ ≤∑_k:Stack,(resource bits requests+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have hlin:resource bits requests ≤(capacity bits requests)^18:=by
    have hp:capacity bits requests ≤(capacity bits requests)^18:=by
      simpa only [pow_one] using Nat.pow_le_pow_right (by unfold capacity;omega:1 ≤capacity bits requests) (by decide:1 ≤18)
    exact (by unfold capacity;omega:resource bits requests ≤capacity bits requests).trans hp
  change t ≤10^100*(capacity bits requests)^18 at ht
  norm_num only at ht ⊢
  omega
/-- Genuine compiled-machine prefix bound for all246 data tapes and the actual return tape. -/
theorem machine_prefix_cells (bits:List Bool) (requests:List (Request bits)) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (source bits requests)))=some cfg):
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤10^103*(capacity bits requests)^18:=by
  have he:=SemiprimeD1StackCalls.run_correct heap output (.local .start) program fuel (source bits requests)
  have hh:=he.trans hr
  cases hout:SemiprimeD1StackCalls.run program fuel (source bits requests) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hc:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells bits requests fuel out hout
/-- Honest prepared four-word compiled endpoint with the SAME actual whole-source clock. -/
noncomputable def bankInTime (bits:List Bool) (requests:List (Request bits)):
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (source bits requests))
      (some (SemiprimeD1StackCalls.configuration (done bits requests))) (runBound bits requests):=by
  apply SemiprimeD1StackCalls.evalsCorrect heap output (.local .start) program
  let h:=source_run_bounded bits requests
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackCachePhaseBankResources
