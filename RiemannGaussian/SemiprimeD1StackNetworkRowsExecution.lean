/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkRowsLoop
import RiemannGaussian.SemiprimeD1StackNetworkRowsFinish
/-! # Whole actual two-input index→factor rows/tallies source with its OWNpaid clock
Original-network instance supplies all singleton/routing facts in proofs ONLY.
The literal program input has ONLYactual vertex-record and unary-leftcount words.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkRowsExecution
open SemiprimeD1StackNetworkRows SemiprimeD1StackNetworkRowsPrimitives SemiprimeD1StackNetworkRowsView
open SemiprimeD1StackNetworkRowsEncoding SemiprimeD1StackNetworkRowsFactors SemiprimeD1StackNetworkRowsLoop
open SemiprimeD1StackNetworkRowsFinish SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Actual full original record/count tape, owners before factors. -/
def inputTape (owners factors:List SemiprimeD1LeafCounter.Vertex) :List Bool :=
  SemiprimeD1StackNetworkOwnerIndexExecution.inputTape owners (SemiprimeD1StackVertexProduct.records factors)
/-- Actual17-role cache acquired ONCEby the actual included index source. -/
def indexResult (owners factors:List SemiprimeD1LeafCounter.Vertex) :I.Stack→List Bool :=
  SemiprimeD1StackNetworkOwnerIndexExecution.result owners (SemiprimeD1StackVertexProduct.records factors)
/-- Exact actual catalogue rows produced from the physical original left records. -/
def dictionaryRows (owners:List SemiprimeD1LeafCounter.Vertex) :List (List Bool×List Bool) :=
  SemiprimeD1StackNetworkOwnerIndexExecution.pairs owners
/-- Actual catalogue BYTES, retained physically and copied before each actual query. -/
def dictionary (owners factors:List SemiprimeD1LeafCounter.Vertex) :List Bool :=indexResult owners factors .output
/-- Literal two-input original source; no routing function/rows/table evaluator/countresult/clock is supplied. -/
def source (owners factors:List SemiprimeD1LeafCounter.Vertex) :C.State Stack Label :=
  initial (inputTape owners factors) (List.replicate owners.length true)
/-- Exact physically acquired reverse row history. Expected routing is proof notation ONLY. -/
def history (route:Nat→List Bool) (factors:List SemiprimeD1LeafCounter.Vertex) :List Bool :=
  (payload ((ownerRows route factors).map SemiprimeD1TensorTapeCodec.vectorBits)).reverse
/-- All48roles when actual factor-record EOF has been consumed and before the final actual row reverse. -/
def preData (owners factors:List SemiprimeD1LeafCounter.Vertex) (route:Nat→List Bool) :Stack→List Bool :=
  view (indexResult owners factors) [] [] [] (history route factors) (List.replicate factors.length true)
    (List.replicate (occurrences factors) true)
/-- Exact same-code final physical bank: all index caches, rows output, and actual F/M tallies retained. -/
def result (owners factors:List SemiprimeD1LeafCounter.Vertex) (route:Nat→List Bool) :Stack→List Bool :=
  Function.update (view (indexResult owners factors) [] [] [] [] (List.replicate factors.length true)
    (List.replicate (occurrences factors) true)) (aux .output) (rowsTape (ownerRows route factors))
/-- Actual clean halt; every unlisted work/fibre/query-shadow word is EMPTY. -/
def done (owners factors:List SemiprimeD1LeafCounter.Vertex) (route:Nat→List Bool) :C.State Stack Label :=
  ⟨none,none,none,result owners factors route,[]⟩
/-- Own prefix allowance sums ONLYactual index/copy/factor primitive execution caps and actual call/end overhead. -/
def prefixBudget (owners factors:List SemiprimeD1LeafCounter.Vertex) :Nat :=
  SemiprimeD1StackNetworkOwnerIndexExecution.timeBound owners (SemiprimeD1StackVertexProduct.records factors)+
  5*(SemiprimeD1StackVertexProduct.records factors).length+
  (factors.map (factorBudget owners.length (dictionary owners factors))).sum+6
/-- Own whole-source clock pays the actual prefix and its SAME-prefix-derived final history reverse/halt. -/
def timeBound (owners factors:List SemiprimeD1LeafCounter.Vertex) :Nat :=
  3*prefixBudget owners factors+2*((inputTape owners factors).length+owners.length)+7
/-- The actual cached catalogue has the exact literal old lookup-record ABI. -/
theorem dictionary_records (owners factors:List SemiprimeD1LeafCounter.Vertex) :
    dictionary owners factors=SemiprimeD1StackOwnerFibre.records (dictionaryRows owners) [] :=
  SemiprimeD1StackNetworkOwnerIndexExecution.output_records owners (SemiprimeD1StackVertexProduct.records factors)
/-- Real index acquisition then ONEreal preserving factor-suffix copy, with every17index cache retained. -/
theorem setup_trace (owners factors:List SemiprimeD1LeafCounter.Vertex) :
    ∃q≤ SemiprimeD1StackNetworkOwnerIndexExecution.timeBound owners (SemiprimeD1StackVertexProduct.records factors)+
      5*(SemiprimeD1StackVertexProduct.records factors).length+5,
      Runs program q (ctl .start) (source owners factors).data (ctl .factorLoop)
        (view (indexResult owners factors) (SemiprimeD1StackVertexProduct.records factors) [] [] [] [] []) :=by
  obtain ⟨q,hq,h0⟩:=index_call owners (SemiprimeD1StackVertexProduct.records factors)
  have he:Sum.elim (SemiprimeD1StackNetworkOwnerIndexExecution.result owners (SemiprimeD1StackVertexProduct.records factors)) (fun _=>[])=
      view (indexResult owners factors) [] [] [] [] [] []:=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · cases k <;> rfl
  rw [he] at h0
  have h1:=copy_call .factors .copyFactors .factorLoop rfl (view (indexResult owners factors) [] [] [] [] [] [])
    (SemiprimeD1StackVertexProduct.records factors) [] (SemiprimeD1StackNetworkOwnerIndexExecution.suffix_retained owners _) rfl rfl
  simp only [List.append_nil] at h1
  change Runs program (5*(SemiprimeD1StackVertexProduct.records factors).length+4) (ctl .copyFactors) _ (ctl .factorLoop)
    (Function.update (view (indexResult owners factors) [] [] [] [] [] []) (aux .reader) (SemiprimeD1StackVertexProduct.records factors)) at h1
  rw [view_reader] at h1
  exact ⟨q+(5*(SemiprimeD1StackVertexProduct.records factors).length+4),by omega,join h0 h1⟩
/-- Entire actual pre-output pipeline; every lookup singleton/width fact is a proof consequence of original network data later. -/
theorem pre_trace (owners factors:List SemiprimeD1LeafCounter.Vertex) (route:Nat→List Bool)
    (hp:∀v∈factors,∀p∈v.ports,SemiprimeD1StackOwnerFibre.values (SemiprimeD1StackUnaryDivmod.unary p) (dictionaryRows owners)=[route p] ∧ (route p).length≤ owners.length+1) :
    ∃q≤ prefixBudget owners factors,Runs program q (ctl .start) (source owners factors).data (ctl .finish) (preData owners factors route) :=by
  obtain ⟨b,hb,h0⟩:=setup_trace owners factors
  obtain ⟨c,hc,h1⟩:=factors_loop (indexResult owners factors) [] [] [] factors route (dictionaryRows owners) owners.length
    (dictionary_records owners factors) hp
  have hr:SemiprimeD1StackVertexProduct.records factors=SemiprimeD1StackNetworkOwnerIndexLoop.vertexPrefix factors++[false]:=by
    simpa only [List.append_nil,SemiprimeD1StackVertexProduct.records] using SemiprimeD1StackNetworkOwnerIndexLoop.records_split factors []
  rw [←hr] at h1
  simp only [List.append_nil] at h1
  refine ⟨b+c,?_,join h0 h1⟩
  unfold prefixBudget
  rw [dictionary_records]
  omega
/-- Whole actual source pays all final emitted bytes by the SAMEphysical prefix that created the history. -/
theorem source_trace (owners factors:List SemiprimeD1LeafCounter.Vertex) (route:Nat→List Bool)
    (hp:∀v∈factors,∀p∈v.ports,SemiprimeD1StackOwnerFibre.values (SemiprimeD1StackUnaryDivmod.unary p) (dictionaryRows owners)=[route p] ∧ (route p).length≤ owners.length+1) :
    ∃q,q+1≤ timeBound owners factors ∧ Runs program q (ctl .start) (source owners factors).data (ctl .done) (result owners factors route) :=by
  obtain ⟨q,hq,hpre⟩:=pre_trace owners factors route hp
  obtain ⟨temp,ht,hAt⟩:=hpre [] (source owners factors) ⟨rfl,rfl,rfl⟩
  have hh:=history_length (inputTape owners factors) (List.replicate owners.length true) q temp ht
  rw [hAt.2.1] at hh
  change (history route factors).length≤(inputTape owners factors).length+(List.replicate owners.length true).length+q at hh
  simp only [List.length_replicate] at hh
  have hf:=finish_trace (preData owners factors route) (history route factors) rfl rfl
  have he:Function.update (Function.update (preData owners factors route) (aux .history) []) (aux .output)
      ((history route factors).reverse++[false])=result owners factors route:=by
    unfold preData result
    rw [view_history]
    simp only [history,List.reverse_reverse,payload_vector,rowsTape]
  rw [he] at hf
  refine ⟨q+(2*(history route factors).length+4),?_,join hpre hf⟩
  unfold timeBound
  omega
/-- Actual two-input whole halt; routing and expected row lists occur ONLYin proof statements, never program/state operands. -/
theorem source_run (owners factors:List SemiprimeD1LeafCounter.Vertex) (route:Nat→List Bool)
    (hp:∀v∈factors,∀p∈v.ports,SemiprimeD1StackOwnerFibre.values (SemiprimeD1StackUnaryDivmod.unary p) (dictionaryRows owners)=[route p] ∧ (route p).length≤ owners.length+1) :
    ∃q≤ timeBound owners factors,SemiprimeD1StackCalls.run program q (source owners factors)=some (done owners factors route) :=by
  obtain ⟨q,hq,hr⟩:=source_trace owners factors route hp
  obtain ⟨finish,hf,hAt⟩:=hr [] (source owners factors) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result owners factors route) [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- Ready entry consumes the ACTUALLYacquired complete17-role cache; all31private words are empty. -/
def ready (owners factors:List SemiprimeD1LeafCounter.Vertex) :C.State Stack Label :=
  ⟨some (ctl .copyFactors),none,none,view (indexResult owners factors) [] [] [] [] [] [],[]⟩
/-- Ready-prefix allowance excludes the actual index execution that its caller already performed. -/
def readyPrefixBudget (owners factors:List SemiprimeD1LeafCounter.Vertex) :Nat :=
  5*(SemiprimeD1StackVertexProduct.records factors).length+
    (factors.map (factorBudget owners.length (dictionary owners factors))).sum+5
/-- Physical ready-cache word lengths follow from the actual original index acquisition. -/
theorem ready_length (owners factors:List SemiprimeD1LeafCounter.Vertex) (k:Stack) :
    ((ready owners factors).data k).length ≤ (inputTape owners factors).length+owners.length+
      SemiprimeD1StackNetworkOwnerIndexExecution.timeBound owners (SemiprimeD1StackVertexProduct.records factors) :=by
  rcases k with k|k
  · obtain ⟨q,hq,hr⟩:=SemiprimeD1StackNetworkOwnerIndexExecution.source_run owners (SemiprimeD1StackVertexProduct.records factors)
    have hd:=SemiprimeD1StackReturnLink.run_data_bound I.program q
      ((inputTape owners factors).length+owners.length) _ _
      (by intro j
          simpa only [SemiprimeD1StackNetworkOwnerIndexExecution.source,inputTape,List.length_replicate] using
            SemiprimeD1StackNetworkOwnerIndexFinish.initial_length (inputTape owners factors)
              (List.replicate owners.length true) j) hr k
    change (indexResult owners factors k).length ≤ _ at hd
    exact hd.trans (Nat.add_le_add_left hq _)
  · rcases k with k|k
    · exact Nat.zero_le _
    · cases k <;> exact Nat.zero_le _
/-- Real suffix copy and complete real factor loop start directly from the caller's acquired index cache. -/
theorem ready_pre_trace (owners factors:List SemiprimeD1LeafCounter.Vertex) (route:Nat→List Bool)
    (hp:∀v∈factors,∀p∈v.ports,SemiprimeD1StackOwnerFibre.values (SemiprimeD1StackUnaryDivmod.unary p) (dictionaryRows owners)=[route p] ∧ (route p).length≤ owners.length+1) :
    ∃q≤readyPrefixBudget owners factors,Runs program q (ctl .copyFactors) (ready owners factors).data
      (ctl .finish) (preData owners factors route) :=by
  have h0:=copy_call .factors .copyFactors .factorLoop rfl (ready owners factors).data
    (SemiprimeD1StackVertexProduct.records factors) []
    (SemiprimeD1StackNetworkOwnerIndexExecution.suffix_retained owners _) rfl rfl
  simp only [List.append_nil] at h0
  change Runs program _ _ _ _ (Function.update (view (indexResult owners factors) [] [] [] [] [] [])
    (aux .reader) (SemiprimeD1StackVertexProduct.records factors)) at h0
  rw [view_reader] at h0
  obtain ⟨q,hq,h1⟩:=factors_loop (indexResult owners factors) [] [] [] factors route (dictionaryRows owners) owners.length
    (dictionary_records owners factors) hp
  have hr:SemiprimeD1StackVertexProduct.records factors=SemiprimeD1StackNetworkOwnerIndexLoop.vertexPrefix factors++[false]:=by
    simpa only [List.append_nil,SemiprimeD1StackVertexProduct.records] using SemiprimeD1StackNetworkOwnerIndexLoop.records_split factors []
  rw [←hr] at h1
  simp only [List.append_nil] at h1
  refine ⟨(5*(SemiprimeD1StackVertexProduct.records factors).length+4)+q,?_,join h0 h1⟩
  unfold readyPrefixBudget
  rw [dictionary_records]
  omega
/-- Same literal program ready entry performs no index rerun and reaches the SAMEclean whole output bank. -/
theorem ready_run (owners factors:List SemiprimeD1LeafCounter.Vertex) (route:Nat→List Bool)
    (hp:∀v∈factors,∀p∈v.ports,SemiprimeD1StackOwnerFibre.values (SemiprimeD1StackUnaryDivmod.unary p) (dictionaryRows owners)=[route p] ∧ (route p).length≤ owners.length+1) :
    ∃q≤timeBound owners factors,SemiprimeD1StackCalls.run program q (ready owners factors)=some (done owners factors route) :=by
  obtain ⟨q,hq,hpre⟩:=ready_pre_trace owners factors route hp
  obtain ⟨temp,ht,hAt⟩:=hpre [] (ready owners factors) ⟨rfl,rfl,rfl⟩
  have hh:=SemiprimeD1StackReturnLink.run_data_bound program q
    ((inputTape owners factors).length+owners.length+
      SemiprimeD1StackNetworkOwnerIndexExecution.timeBound owners (SemiprimeD1StackVertexProduct.records factors))
    _ temp (ready_length owners factors) ht (aux .history)
  rw [hAt.2.1] at hh
  change (history route factors).length≤_ at hh
  have hf:=finish_trace (preData owners factors route) (history route factors) rfl rfl
  have he:Function.update (Function.update (preData owners factors route) (aux .history) []) (aux .output)
      ((history route factors).reverse++[false])=result owners factors route:=by
    unfold preData result
    rw [view_history]
    simp only [history,List.reverse_reverse,payload_vector,rowsTape]
  rw [he] at hf
  obtain ⟨finish,hfinish,hfinishAt⟩:=hf [] temp hAt
  have hhhalt:=halt_run program (ctl .done) rfl (result owners factors route) [] finish hfinishAt
  refine ⟨q+(2*(history route factors).length+4)+1,?_,?_⟩
  · unfold timeBound prefixBudget readyPrefixBudget at *
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,SemiprimeD1StackReturnLink.run_add,ht,Option.bind_some,
      hfinish,Option.bind_some]
    exact hhhalt
end RiemannGaussian.SemiprimeD1StackNetworkRowsExecution
