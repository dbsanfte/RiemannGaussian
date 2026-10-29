/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkRowsExecution
/-! # Own fixed polynomial source clock and all forty-eight tapes/return cells
Catalogue bytes are bounded from the actual included index execution. All
other costs are sums of the paid physical parser/copy/fibre/logger calls.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkRowsBounds
open SemiprimeD1StackNetworkRows SemiprimeD1StackNetworkRowsExecution
open SemiprimeD1StackNetworkRowsFactors SemiprimeD1StackNetworkRowsFinish
open SemiprimeD1StackCalls (run configuration)
local notation "ctl" => Label.local
/-- Total physical record/count input bytes plus one. -/
def inputSize (owners factors:List SemiprimeD1LeafCounter.Vertex) :Nat :=
  (inputTape owners factors).length+owners.length+1
/-- Fixed before all physical network tapes and acquired counts. -/
def polynomial (owners factors:List SemiprimeD1LeafCounter.Vertex) :Nat :=
  10000000000*(inputSize owners factors)^3
/-- The retained dictionary is paid by the SAMEactual complete index run. -/
theorem dictionary_length (owners factors:List SemiprimeD1LeafCounter.Vertex) :
    (dictionary owners factors).length ≤ 10001*(inputSize owners factors)^2 :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackNetworkOwnerIndexBounds.source_run_bounded owners
    (SemiprimeD1StackVertexProduct.records factors)
  have hd:=SemiprimeD1StackReturnLink.run_data_bound I.program q
    ((inputTape owners factors).length+owners.length)
    (SemiprimeD1StackNetworkOwnerIndexExecution.source owners (SemiprimeD1StackVertexProduct.records factors))
    (SemiprimeD1StackNetworkOwnerIndexExecution.done owners (SemiprimeD1StackVertexProduct.records factors))
    (by intro k
        simpa only [SemiprimeD1StackNetworkOwnerIndexExecution.source,inputTape,List.length_replicate] using
          SemiprimeD1StackNetworkOwnerIndexFinish.initial_length (inputTape owners factors)
            (List.replicate owners.length true) k) hr .output
  change (dictionary owners factors).length ≤ (inputTape owners factors).length+owners.length+q at hd
  change q ≤ 10000*(inputSize owners factors)^2 at hq
  have hs:inputSize owners factors ≤ (inputSize owners factors)^2:=Nat.le_pow (by decide:0<(2:Nat))
  unfold inputSize at hs ⊢ hq
  omega
/-- Actual complete factor suffix is a physically supplied tape suffix. -/
theorem suffix_length (owners factors:List SemiprimeD1LeafCounter.Vertex) :
    (SemiprimeD1StackVertexProduct.records factors).length ≤ (inputTape owners factors).length :=by
  simp only [inputTape,SemiprimeD1StackNetworkOwnerIndexExecution.inputTape,List.length_append]
  omega
/-- Actual factor-record prefix is paid by that whole physical suffix. -/
theorem factor_prefix_length (owners factors:List SemiprimeD1LeafCounter.Vertex) :
    (SemiprimeD1StackNetworkOwnerIndexLoop.vertexPrefix factors).length ≤ (inputTape owners factors).length :=by
  have h:SemiprimeD1StackVertexProduct.records factors=SemiprimeD1StackNetworkOwnerIndexLoop.vertexPrefix factors++[false]:=by
    simpa only [List.append_nil,SemiprimeD1StackVertexProduct.records] using
      SemiprimeD1StackNetworkOwnerIndexLoop.records_split factors []
  have hl:=congrArg List.length h
  simp only [List.length_append,List.length_cons,List.length_nil] at hl
  have hs:=suffix_length owners factors
  omega
/-- Own primitive prefix sum has a uniform cubic physical-input bound. -/
theorem prefixBudget_le (owners factors:List SemiprimeD1LeafCounter.Vertex) :
    prefixBudget owners factors ≤ 1000000000*(inputSize owners factors)^3 :=by
  let S:=inputSize owners factors
  have hS:1 ≤ S:=by dsimp [S,inputSize];omega
  have hN:owners.length+1 ≤ S:=by dsimp [S,inputSize];omega
  have hL:(inputTape owners factors).length ≤ S:=by dsimp [S,inputSize];omega
  have hI:=SemiprimeD1StackNetworkOwnerIndexBounds.timeBound_le owners (SemiprimeD1StackVertexProduct.records factors)
  change SemiprimeD1StackNetworkOwnerIndexExecution.timeBound owners (SemiprimeD1StackVertexProduct.records factors) ≤ 10000*S^2 at hI
  have hD:=dictionary_length owners factors
  change (dictionary owners factors).length ≤ 10001*S^2 at hD
  have hS2:S ≤ S^2:=Nat.le_pow (by decide:0<(2:Nat))
  have hsum:=factorsBudget_le owners.length (dictionary owners factors) factors
  have hsum':(factors.map (factorBudget owners.length (dictionary owners factors))).sum ≤
      10000*(owners.length+(dictionary owners factors).length+2)*(inputTape owners factors).length:=
    hsum.trans (Nat.mul_le_mul_left _ (factor_prefix_length owners factors))
  have hcoeff:owners.length+(dictionary owners factors).length+2 ≤ 10004*S^2:=by omega
  have hmul:=Nat.mul_le_mul hcoeff hL
  have hcost:(factors.map (factorBudget owners.length (dictionary owners factors))).sum ≤ 100040000*S^3:=by
    nlinarith only [hsum',hmul]
  have hsuf:=suffix_length owners factors
  have hp2:S^2 ≤ S^3:=by nlinarith only [Nat.mul_le_mul_left (S^2) hS]
  have hp1:S ≤ S^3:=hS2.trans hp2
  unfold prefixBudget
  change _ ≤ 1000000000*S^3
  omega
/-- Same whole actual source clock, without native clock transport. -/
theorem timeBound_le (owners factors:List SemiprimeD1LeafCounter.Vertex) :
    timeBound owners factors ≤ polynomial owners factors :=by
  have hp:=prefixBudget_le owners factors
  have hs:inputSize owners factors ≤ (inputSize owners factors)^3:=Nat.le_pow (by decide:0<(3:Nat))
  have h1:1 ≤ (inputSize owners factors)^3:=by
    have h:1 ≤ inputSize owners factors:=by unfold inputSize;omega
    omega
  unfold timeBound polynomial inputSize at *
  omega
/-- Every initialized physical word is charged to the two input words. -/
theorem source_initial_bound (owners factors:List SemiprimeD1LeafCounter.Vertex) (k:Stack) :
    ((source owners factors).data k).length ≤ inputSize owners factors :=by
  have h:=initial_length (inputTape owners factors) (List.replicate owners.length true) k
  simp only [List.length_replicate] at h
  unfold inputSize
  exact h.trans (Nat.le_succ _)
/-- Complete actual source has the same fixed polynomial cap. -/
theorem source_run_bounded (owners factors:List SemiprimeD1LeafCounter.Vertex) (route:Nat→List Bool)
    (hp:∀v∈factors,∀p∈v.ports,SemiprimeD1StackOwnerFibre.values (SemiprimeD1StackUnaryDivmod.unary p) (dictionaryRows owners)=[route p] ∧ (route p).length ≤ owners.length+1) :
    ∃q ≤ polynomial owners factors,run program q (source owners factors)=some (done owners factors route) :=by
  obtain ⟨q,hq,hr⟩:=source_run owners factors route hp
  exact ⟨q,hq.trans (timeBound_le owners factors),hr⟩
/-- No actual successful prefix can pass the same program's final halt. -/
theorem prefix_fuel (owners factors:List SemiprimeD1LeafCounter.Vertex) (route:Nat→List Bool)
    (hp:∀v∈factors,∀p∈v.ports,SemiprimeD1StackOwnerFibre.values (SemiprimeD1StackUnaryDivmod.unary p) (dictionaryRows owners)=[route p] ∧ (route p).length ≤ owners.length+1)
    (fuel:Nat) (out:C.State Stack Label) (hr:run program fuel (source owners factors)=some out) :
    fuel ≤ polynomial owners factors :=by
  obtain ⟨q,hq,he⟩:=source_run_bounded owners factors route hp
  have hh:run program 1 (done owners factors route)=none:=rfl
  have hf:fuel ≤ q:=by
    by_contra hn
    have h:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hh,Option.bind_none] at hr
    cases hr
  exact hf.trans hq
/-- All48actual tapes including the allocated query shadow and all real return cells. -/
theorem prefix_cells (owners factors:List SemiprimeD1LeafCounter.Vertex) (route:Nat→List Bool)
    (hp:∀v∈factors,∀p∈v.ports,SemiprimeD1StackOwnerFibre.values (SemiprimeD1StackUnaryDivmod.unary p) (dictionaryRows owners)=[route p] ∧ (route p).length ≤ owners.length+1)
    (fuel:Nat) (out:C.State Stack Label) (hr:run program fuel (source owners factors)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 1000000000000*(inputSize owners factors)^3 :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputSize owners factors)
    (source owners factors) out (source_initial_bound owners factors) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel (source owners factors) out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:=SemiprimeD1StackNetworkOwnerIndexBounds.word_sum_le out.data (inputSize owners factors+fuel) hd
  rw [stack_card] at hs
  have ht:=prefix_fuel owners factors route hp fuel out hr
  unfold polynomial at ht
  have hp3:inputSize owners factors ≤ (inputSize owners factors)^3:=Nat.le_pow (by decide:0<(3:Nat))
  omega
/-- Genuine fixed finite-machine certificate for this exact whole source. -/
noncomputable def rowsInTime (owners factors:List SemiprimeD1LeafCounter.Vertex) (route:Nat→List Bool)
    (hp:∀v∈factors,∀p∈v.ports,SemiprimeD1StackOwnerFibre.values (SemiprimeD1StackUnaryDivmod.unary p) (dictionaryRows owners)=[route p] ∧ (route p).length ≤ owners.length+1) :
    StateTransition.EvalsToInTime machine.step (configuration (source owners factors))
      (some (configuration (done owners factors route))) (polynomial owners factors) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (indexStack .vertices) (aux .output) (ctl .start) program
  let h:=source_run_bounded owners factors route hp
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Every reached compiled prefix counts every physical tape and return symbol. -/
theorem machine_prefix_cells (owners factors:List SemiprimeD1LeafCounter.Vertex) (route:Nat→List Bool)
    (hp:∀v∈factors,∀p∈v.ports,SemiprimeD1StackOwnerFibre.values (SemiprimeD1StackUnaryDivmod.unary p) (dictionaryRows owners)=[route p] ∧ (route p).length ≤ owners.length+1)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (configuration (source owners factors)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 1000000000000*(inputSize owners factors)^3 :=by
  have he:=SemiprimeD1StackCalls.run_correct (indexStack .vertices) (aux .output) (ctl .start) program fuel (source owners factors)
  have hh:=he.trans hr
  cases hout:run program fuel (source owners factors) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells owners factors route hp fuel out hout
/-- Literal source transitions compile with bounded fundamental command depth. -/
theorem compile_depth (pc:Label) :SemiprimeD1StackBytecode.statementDepth (machine.m pc) ≤ 4 :=
  SemiprimeD1StackCalls.compile_depth (ctl .start) (program pc)
/-- Ready entry reuses the actual acquired index cache and has the SAMEfixed polynomial cap. -/
theorem ready_run_bounded (owners factors:List SemiprimeD1LeafCounter.Vertex) (route:Nat→List Bool)
    (hp:∀v∈factors,∀p∈v.ports,SemiprimeD1StackOwnerFibre.values (SemiprimeD1StackUnaryDivmod.unary p) (dictionaryRows owners)=[route p] ∧ (route p).length ≤ owners.length+1) :
    ∃q ≤ polynomial owners factors,run program q (ready owners factors)=some (done owners factors route) :=by
  obtain ⟨q,hq,hr⟩:=ready_run owners factors route hp
  exact ⟨q,hq.trans (timeBound_le owners factors),hr⟩
/-- Every actual ready-cache word is paid by its real original index source. -/
theorem ready_initial_bound (owners factors:List SemiprimeD1LeafCounter.Vertex) (k:Stack) :
    ((ready owners factors).data k).length ≤ 10001*(inputSize owners factors)^2 :=by
  have h:=ready_length owners factors k
  have hi:=SemiprimeD1StackNetworkOwnerIndexBounds.timeBound_le owners (SemiprimeD1StackVertexProduct.records factors)
  change _ ≤ 10000*(inputSize owners factors)^2 at hi
  have hs:inputSize owners factors ≤ (inputSize owners factors)^2:=Nat.le_pow (by decide:0<(2:Nat))
  unfold inputSize at hs ⊢ hi
  omega
/-- All48words and real returns are counted also for the actual-cache ready entry. -/
theorem ready_prefix_cells (owners factors:List SemiprimeD1LeafCounter.Vertex) (route:Nat→List Bool)
    (hp:∀v∈factors,∀p∈v.ports,SemiprimeD1StackOwnerFibre.values (SemiprimeD1StackUnaryDivmod.unary p) (dictionaryRows owners)=[route p] ∧ (route p).length ≤ owners.length+1)
    (fuel:Nat) (out:C.State Stack Label) (hr:run program fuel (ready owners factors)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 1000000000000*(inputSize owners factors)^3 :=by
  obtain ⟨q,hq,he⟩:=ready_run_bounded owners factors route hp
  have ht:fuel ≤ q:=by
    by_contra hn
    have h:fuel=q+(1+(fuel-(q+1))):=by omega
    have hh:run program 1 (done owners factors route)=none:=rfl
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hh,Option.bind_none] at hr
    cases hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (10001*(inputSize owners factors)^2)
    (ready owners factors) out (ready_initial_bound owners factors) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel (ready owners factors) out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:=SemiprimeD1StackNetworkOwnerIndexBounds.word_sum_le out.data (10001*(inputSize owners factors)^2+fuel) hd
  rw [stack_card] at hs
  have hS:1 ≤ inputSize owners factors:=by unfold inputSize;omega
  have hp2:(inputSize owners factors)^2 ≤ (inputSize owners factors)^3:=
    Nat.pow_le_pow_right hS (by decide:2 ≤ (3:Nat))
  unfold polynomial at hq
  omega
/-- Genuine prepared compiled ready certificate reuses its acquired cache without an index call. -/
noncomputable def readyInTime (owners factors:List SemiprimeD1LeafCounter.Vertex) (route:Nat→List Bool)
    (hp:∀v∈factors,∀p∈v.ports,SemiprimeD1StackOwnerFibre.values (SemiprimeD1StackUnaryDivmod.unary p) (dictionaryRows owners)=[route p] ∧ (route p).length ≤ owners.length+1) :
    StateTransition.EvalsToInTime machine.step (configuration (ready owners factors))
      (some (configuration (done owners factors route))) (polynomial owners factors) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (indexStack .vertices) (aux .output) (ctl .start) program
  let h:=ready_run_bounded owners factors route hp
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Same compiled ready source accounts for all48data tapes and the actual return alphabet. -/
theorem ready_machine_prefix_cells (owners factors:List SemiprimeD1LeafCounter.Vertex) (route:Nat→List Bool)
    (hp:∀v∈factors,∀p∈v.ports,SemiprimeD1StackOwnerFibre.values (SemiprimeD1StackUnaryDivmod.unary p) (dictionaryRows owners)=[route p] ∧ (route p).length ≤ owners.length+1)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (configuration (ready owners factors)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 1000000000000*(inputSize owners factors)^3 :=by
  have he:=SemiprimeD1StackCalls.run_correct (indexStack .vertices) (aux .output) (ctl .start) program fuel (ready owners factors)
  have hh:=he.trans hr
  cases hout:run program fuel (ready owners factors) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact ready_prefix_cells owners factors route hp fuel out hout
end RiemannGaussian.SemiprimeD1StackNetworkRowsBounds
