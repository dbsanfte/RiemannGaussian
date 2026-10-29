/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexLoop
import RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexFinish
/-! # Whole physical record-to-owner-index acquisition with its own charged clock
The final-history length is bounded by the SAME executed source prefix. Every
record copy, count traversal, ports/table parse, table cleanup, pair write,
binary counter update, final reverse and actual halt is included.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexExecution
open SemiprimeD1StackNetworkOwnerIndex SemiprimeD1StackNetworkOwnerIndexPrimitives
open SemiprimeD1StackNetworkOwnerIndexSetup SemiprimeD1StackNetworkOwnerIndexEncoding
open SemiprimeD1StackNetworkOwnerIndexLoop SemiprimeD1StackNetworkOwnerIndexFinish
open SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Physical initial record tape: owner records followed by the unconsumed actual factor suffix. -/
def inputTape (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool) :List Bool :=vertexPrefix owners++suffix
/-- Exact original chronological pair list; it is specification data, never a runtime getter. -/
def pairs (owners:List SemiprimeD1LeafCounter.Vertex) :List (List Bool×List Bool) :=ownerPairs owners.length 0 owners
/-- Exact actual source input has only the record tape and physically acquired unary owner count. -/
def source (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool) :C.State Stack Label :=
  initial (inputTape owners suffix) (List.replicate owners.length true)
/-- Actual reverse history produced by this source's paid pair writes. -/
def history (owners:List SemiprimeD1LeafCounter.Vertex) :List Bool :=(payload (pairs owners)).reverse
/-- All actual work is clear when the owner loop reaches the final reversal phase. -/
def preData (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool) :Stack→List Bool :=
  view (inputTape owners suffix) (List.replicate owners.length true) suffix [] []
    (ownerWord owners.length owners.length) (history owners)
/-- Exact physical final source store; original tapes and the entire factor suffix remain. -/
def result (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool) :Stack→List Bool :=
  Function.update (view (inputTape owners suffix) (List.replicate owners.length true) suffix [] []
    (ownerWord owners.length owners.length) []) .output (payload (pairs owners)++[false])
/-- Genuine clean halt after the actual two-input source and sole final reversal. -/
def done (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool) :C.State Stack Label :=
  ⟨none,none,none,result owners suffix,[]⟩
/-- Own prefix cap sums actual setup and per-record primitive execution caps only. -/
def prefixBudget (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool) :Nat :=
  5*(inputTape owners suffix).length+12*owners.length+14+(owners.map (rowBudget owners.length)).sum+1
/-- Whole actual clock pays its prefix plus its own trace-derived history reverse and halt. -/
def timeBound (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool) :Nat :=
  3*prefixBudget owners suffix+2*((inputTape owners suffix).length+owners.length)+7
/-- Entire actual setup/owner loop, with no output-size advice or native graph callback. -/
theorem pre_trace (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool) :
    ∃q ≤ prefixBudget owners suffix,Runs program q (ctl .start) (source owners suffix).data
      (ctl .finish) (preData owners suffix) :=by
  have h0:=setup_trace (inputTape owners suffix) owners.length
  rw [←ownerWord_zero owners.length] at h0
  obtain ⟨q,hq,h1⟩:=owners_loop (inputTape owners suffix) (List.replicate owners.length true) suffix []
    owners.length 0 owners (by omega)
  simp only [Nat.zero_add,List.append_nil] at h1
  refine ⟨(5*(inputTape owners suffix).length+12*owners.length+14)+q,?_,?_⟩
  · unfold prefixBudget
    omega
  · exact join h0 h1
/-- Whole same-program trace has paid for every output byte before its final real halt. -/
theorem source_trace (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool) :
    ∃q,q+1 ≤ timeBound owners suffix ∧ Runs program q (ctl .start) (source owners suffix).data
      (ctl .done) (result owners suffix) :=by
  obtain ⟨q,hq,hpre⟩:=pre_trace owners suffix
  obtain ⟨temp,ht,hAt⟩:=hpre [] (source owners suffix) ⟨rfl,rfl,rfl⟩
  have hh:=history_length (inputTape owners suffix) (List.replicate owners.length true) q temp ht
  rw [hAt.2.1] at hh
  change (history owners).length ≤(inputTape owners suffix).length+(List.replicate owners.length true).length+q at hh
  simp only [List.length_replicate] at hh
  have hf:=finish_trace (preData owners suffix) (history owners) rfl rfl
  have he:Function.update (Function.update (preData owners suffix) .history []) .output
      ((history owners).reverse++[false])=result owners suffix :=by
    unfold preData result
    rw [view_history]
    simp only [history,List.reverse_reverse]
  rw [he] at hf
  refine ⟨q+(2*(history owners).length+6),?_,join hpre hf⟩
  unfold timeBound
  omega
/-- Complete real source starts with physical record/count words ONLY and executes its actual final halt. -/
theorem source_run (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool) :
    ∃q ≤ timeBound owners suffix,SemiprimeD1StackCalls.run program q (source owners suffix)=some (done owners suffix) :=by
  obtain ⟨q,hq,hr⟩:=source_trace owners suffix
  obtain ⟨finish,hf,hAt⟩:=hr [] (source owners suffix) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result owners suffix) [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- Exact old generic lookup/fibre catalogue bytes, including the single false terminal. -/
theorem output_records (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool) :
    (done owners suffix).data .output=SemiprimeD1StackOwnerLookup.records (pairs owners) [] :=by
  change payload (pairs owners)++[false]=_
  exact (records_payload (pairs owners) []).symm
/-- Every original complete record bit survives acquisition literally. -/
theorem original_retained (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool) :
    (done owners suffix).data .vertices=inputTape owners suffix :=by
  change result owners suffix Stack.vertices=_
  unfold result
  rw [Function.update_of_ne (by decide:Stack.vertices≠.output)]
  rfl
/-- The acquired unary count survives, including isolated owners that emitted no port pairs. -/
theorem count_retained (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool) :
    (done owners suffix).data .leftCount=List.replicate owners.length true :=by
  change result owners suffix Stack.leftCount=_
  unfold result
  rw [Function.update_of_ne (by decide:Stack.leftCount≠.output)]
  rfl
/-- The factor-record suffix is still physically available for the next actual graph-row acquisition stage. -/
theorem suffix_retained (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool) :
    (done owners suffix).data .reader=suffix :=by
  change result owners suffix Stack.reader=_
  unfold result
  rw [Function.update_of_ne (by decide:Stack.reader≠.output)]
  rfl
/-- Genuine fixed finite-machine source certificate, charging this SAME literal program's own total clock. -/
noncomputable def ownerIndexInTime (owners:List SemiprimeD1LeafCounter.Vertex) (suffix:List Bool) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (source owners suffix))
      (some (SemiprimeD1StackCalls.configuration (done owners suffix))) (timeBound owners suffix) :=by
  apply SemiprimeD1StackCalls.evalsCorrect Stack.vertices Stack.output (ctl .start) program
  let h:=source_run owners suffix
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexExecution
