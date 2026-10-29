/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexExecution
/-! # Uniform quadratic physical owner-index acquisition and all-prefix storage
The record tape and acquired unary count pay for all seventeen physical words,
every parsed tensor byte, the emitted index and every real return cell. The
native bound is attached to this actual complete fixed source, not another
semantic implementation or an uncharged graph/owner oracle.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexBounds
open SemiprimeD1StackNetworkOwnerIndex SemiprimeD1StackNetworkOwnerIndexLoop
open SemiprimeD1StackNetworkOwnerIndexExecution SemiprimeD1StackNetworkOwnerIndexFinish
open SemiprimeD1StackCalls (run configuration)
local notation "ctl" => Label.local
/-- Actual total record/count input bytes plus one; the count is paid in its actual unary representation. -/
def inputSize (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool) :Nat :=
  (inputTape owners suffix).length+owners.length+1
/-- Fixed whole-source quadratic clock before all physical original/current network inputs. -/
def polynomial (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool) :Nat :=10000*(inputSize owners suffix)^2
/-- Owner record bytes form a prefix of the actual physically supplied record tape. -/
theorem vertex_prefix_le (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool) :
    (vertexPrefix owners).length ≤(inputTape owners suffix).length :=by
  simp only [inputTape,List.length_append]
  omega
/-- Actual per-record primitive allowances sum to a fixed quadratic whole input-byte clock. -/
theorem timeBound_le (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool) :
    timeBound owners suffix ≤polynomial owners suffix :=by
  have hs: (owners.map (rowBudget owners.length)).sum ≤
      1000*(owners.length+2)*(inputTape owners suffix).length:=
    (sumBudget_le owners.length owners).trans
      (Nat.mul_le_mul_left (1000*(owners.length+2)) (vertex_prefix_le owners suffix))
  unfold timeBound prefixBudget polynomial inputSize
  nlinarith only [hs,Nat.zero_le ((inputTape owners suffix).length^2),Nat.zero_le (owners.length^2),
    Nat.zero_le (owners.length*(inputTape owners suffix).length)]
/-- Same actual complete source executes within its fixed quadratic physical-input cap. -/
theorem source_run_bounded (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool) :
    ∃q ≤polynomial owners suffix,run program q (source owners suffix)=some (done owners suffix) :=by
  obtain ⟨q,hq,hr⟩:=source_run owners suffix
  exact ⟨q,hq.trans (timeBound_le owners suffix),hr⟩
/-- Every actually initialized source word is paid by the actual two supplied tape lengths. -/
theorem source_initial_bound (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool) (k:Stack) :
    ((source owners suffix).data k).length ≤ inputSize owners suffix :=by
  have h:=initial_length (inputTape owners suffix) (List.replicate owners.length true) k
  simp only [List.length_replicate] at h
  unfold inputSize
  exact h.trans (Nat.le_succ _)
/-- A successful actual source prefix cannot pass this same fixed program's genuine final halt. -/
theorem prefix_fuel (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool)
    (fuel:Nat) (out:C.State Stack Label) (hr:run program fuel (source owners suffix)=some out) :
    fuel ≤polynomial owners suffix :=by
  obtain ⟨q,hq,he⟩:=source_run_bounded owners suffix
  have hh:run program 1 (done owners suffix)=none:=rfl
  have hf:fuel ≤q:=by
    by_contra hn
    have h:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hh,Option.bind_none] at hr
    cases hr
  exact hf.trans hq
/-- Abstract finite-bank sum avoids evaluating any current network or encoded record during elaboration. -/
theorem word_sum_le {K:Type} [Fintype K] (words:K→List Bool) (B:Nat)
    (h:∀k,(words k).length ≤B) :(∑k:K,(words k).length) ≤Fintype.card K*B :=by
  calc
    _ ≤∑_k:K,B:=Finset.sum_le_sum (fun k _=>h k)
    _= _:=by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
/-- Every reached actual prefix counts all seventeen data words and every real return-frame cell. -/
theorem prefix_cells (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool)
    (fuel:Nat) (out:C.State Stack Label) (hr:run program fuel (source owners suffix)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤200000*(inputSize owners suffix)^2 :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputSize owners suffix)
    (source owners suffix) out (source_initial_bound owners suffix) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel (source owners suffix) out hr
  change out.frames.length ≤0+fuel at hf
  have hs:=word_sum_le out.data (inputSize owners suffix+fuel) hd
  rw [stack_card] at hs
  have ht:=prefix_fuel owners suffix fuel out hr
  unfold polynomial at ht
  have hp:inputSize owners suffix ≤(inputSize owners suffix)^2:=Nat.le_pow (by decide:0<(2:Nat))
  omega
/-- Genuine prepared finite-machine source certificate charges the same whole quadratic physical clock. -/
noncomputable def machineBounded (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool) :
    StateTransition.EvalsToInTime machine.step (configuration (source owners suffix))
      (some (configuration (done owners suffix))) (polynomial owners suffix) :=by
  apply SemiprimeD1StackCalls.evalsCorrect Stack.vertices Stack.output (ctl .start) program
  let h:=source_run_bounded owners suffix
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Complete compiled prefix storage includes all seventeen actual role tapes and fixed-alphabet return symbols. -/
theorem machine_prefix_cells (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (configuration (source owners suffix)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤200000*(inputSize owners suffix)^2 :=by
  have he:=SemiprimeD1StackCalls.run_correct Stack.vertices Stack.output (ctl .start) program fuel (source owners suffix)
  have hh:=he.trans hr
  cases hout:run program fuel (source owners suffix) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells owners suffix fuel out hout
/-- Each actual source transition expands to at most four fundamental fixed-machine commands. -/
theorem compile_depth (pc:Label) :SemiprimeD1StackBytecode.statementDepth (machine.m pc) ≤4 :=
  SemiprimeD1StackCalls.compile_depth (ctl .start) (program pc)
end RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexBounds
