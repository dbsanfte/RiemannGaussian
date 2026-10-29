/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketModeAcquireBounds
/-! # All44 actual words and real return cells at every compiled prefix
The source front door is the three actual prepared tapes, not original N alone.
The SAME whole program supplies its own source clock and storage certificates.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketModeAcquireResources
open SemiprimeD1StackPacketModeAcquire SemiprimeD1StackPacketModeAcquireEncoding
open SemiprimeD1StackPacketModeAcquireExecution SemiprimeD1StackPacketModeAcquireBounds
open SemiprimeD1StackCalls (run configuration)
/-- Every actual initialized word is paid by physical input bytes, with computed tile VALUE retained in the envelope. -/
theorem initial_length (packets:List (List Bool)) (i precision:Nat) (k:Stack):
    ((source packets i precision).data k).length ≤ inputSize packets i precision:=by
  have hp:precision ≤ inputSize packets i precision:=by
    change precision ≤ (SemiprimeD1TensorTapeCodec.vectorBits packets).length+i+2^(i+1)+precision+1
    exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  have hi:i ≤ inputSize packets i precision:=by
    change i ≤ (SemiprimeD1TensorTapeCodec.vectorBits packets).length+i+2^(i+1)+precision+1
    exact (((Nat.le_add_left _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
  have hb:(SemiprimeD1TensorTapeCodec.vectorBits packets).length ≤ inputSize packets i precision:=by
    change (SemiprimeD1TensorTapeCodec.vectorBits packets).length ≤ (SemiprimeD1TensorTapeCodec.vectorBits packets).length+i+2^(i+1)+precision+1
    exact (((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
  rcases k with k|k
  · have h:=SemiprimeD1StackWeightedModeCatalogueBounds.initial_length 0 0 precision k
    change ((M.initial [] [] (List.replicate precision true)).data k).length ≤ inputSize packets i precision
    exact h.trans (by simpa only [Nat.zero_add] using hp)
  · cases k <;> change _ ≤ inputSize packets i precision
    · exact hb
    · change (List.replicate i true).length ≤ inputSize packets i precision
      simpa only [List.length_replicate] using hi
    all_goals exact Nat.zero_le _
/-- Actual successful prefixes stop before this SAME source's genuine final halt. -/
theorem prefix_fuel (packets:List (List Bool)) (i precision fuel:Nat) (out:C.State Stack Label)
    (hr:run program fuel (source packets i precision)=some out):fuel ≤ runBound packets i precision:=by
  obtain ⟨q,hq,hfinal⟩:=source_run_bounded packets i precision
  have hh:run program 1 (done packets i precision)=none:=rfl
  have hf:fuel ≤ q:=by
    by_contra hn
    have he:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hfinal,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hh,Option.bind_none] at hr
    cases hr
  exact hf.trans hq
/-- All44 actual source/callee/parser/doubling words and every real return frame are counted. -/
theorem prefix_cells (packets:List (List Bool)) (i precision fuel:Nat) (out:C.State Stack Label)
    (hr:run program fuel (source packets i precision)=some out):
    (∑k:Stack,(out.data k).length)+out.frames.length ≤
      45*(inputSize packets i precision+runBound packets i precision):=by
  have ht:=prefix_fuel packets i precision fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputSize packets i precision)
    _ _ (initial_length packets i precision) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ _ hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length) ≤ 44*(inputSize packets i precision+fuel):=by
    calc
      _ ≤ ∑_k:Stack,(inputSize packets i precision+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  omega
/-- Genuine compiled execution certificate starts with precisely the three honest physical source inputs. -/
noncomputable def modesInTime (packets:List (List Bool)) (i precision:Nat):
    StateTransition.EvalsToInTime machine.step (configuration (source packets i precision))
      (some (configuration (done packets i precision))) (runBound packets i precision):=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .packets) output (.local .start) program
  have h:=source_run_bounded packets i precision
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Every genuine compiled prefix counts ALL44 data words and its actual finite-label return stack. -/
theorem machine_prefix_cells (packets:List (List Bool)) (i precision fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (configuration (source packets i precision)))=some cfg):
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      45*(inputSize packets i precision+runBound packets i precision):=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .packets) output (.local .start) program fuel (source packets i precision)
  have hh:=he.trans hr
  cases hout:run program fuel (source packets i precision) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells packets i precision fuel out hout
/-- Every actual source instruction compiles to fixed-depth finite statements. -/
theorem compile_depth (pc:Label):SemiprimeD1StackBytecode.statementDepth (machine.m pc) ≤ 4:=by
  change SemiprimeD1StackBytecode.statementDepth
    (SemiprimeD1StackCalls.compileInstruction (Label.local Control.start) (program pc)) ≤ 4
  exact SemiprimeD1StackCalls.compile_depth (Label.local Control.start) (program pc)
end RiemannGaussian.SemiprimeD1StackPacketModeAcquireResources
