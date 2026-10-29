/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceOccurrencesExecution
/-! # Own quadratic acquisition bound from actual physical row/count bytes
The byte input pays counter width, all source copies, complete factor/owner
parses, binary-key normalizations, frames, final reverse and cleanup. Every
actual data tape and real return cell is counted at every reached prefix.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceOccurrencesBounds
open SemiprimeD1StackSourceOccurrences SemiprimeD1StackSourceOccurrencesExecution
open SemiprimeD1StackSourceOccurrencesEncoding SemiprimeD1StackSourceOccurrencesPrescan
open SemiprimeD1StackSourceOccurrencesFactors
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackCalls (run configuration)
local notation "ctl" => Label.local
/-- Actual source input bytes and actual retained unary n, plus one. -/
def inputSize (n:Nat) (rows:List (List (List Bool))) :Nat :=(inputTape rows).length+n+1
/-- Sum of actual physically parsed whole inner-row fields; proof notation only. -/
def rowMass (rows:List (List (List Bool))) :Nat :=(rows.map (fun row=>(vectorBits row).length)).sum
/-- Exact physical outer-vector length pays all actual row fields and every empty-row constructor. -/
theorem outer_length (rows:List (List (List Bool))) :
    (inputTape rows).length=2*rowMass rows+2*rows.length+1 :=by
  have h:=SemiprimeD1StackNetworkRowsEncoding.vector_length (rows.map vectorBits)
  simpa only [inputTape,SemiprimeD1StackNetworkRowsEncoding.rowsTape,rowMass,List.map_map,
    Function.comp_def,List.length_map] using h
/-- Exact paid complete-factor-prescan allowance from actual field bytes and physical factor count. -/
theorem prescanTime_eq (rows:List (List (List Bool))) :prescanTime rows=9*rowMass rows+12*rows.length+1 :=by
  induction rows with
  | nil=>rfl
  | cons row rows ih=>
    have hc:prescanTime (row::rows)=(9*(vectorBits row).length+12)+prescanTime rows:=by
      simp only [prescanTime,List.map_cons,List.sum_cons]
      omega
    rw [hc,ih]
    simp only [rowMass,List.map_cons,List.sum_cons,List.length_cons]
    ring
/-- Entire prescan is paid by its actual encoded input word, without an arity/count supplier. -/
theorem prescanTime_le (rows:List (List (List Bool))) :prescanTime rows≤12*(inputTape rows).length :=by
  have h:=outer_length rows
  rw [prescanTime_eq]
  omega
/-- Actual n-marker allocation and entire factor prescan have a fixed linear input-byte cap. -/
theorem acquisitionTime_le (n:Nat) (rows:List (List (List Bool))) :acquisitionTime n rows≤100*inputSize n rows :=by
  have h:=prescanTime_le rows
  unfold acquisitionTime inputSize
  omega
/-- Exact factor-loop row-sum allowance in actual allocated width and complete physical inner-row fields. -/
theorem factor_sum (n F:Nat) (rows:List (List (List Bool))) :
    (rows.map (factorBudget n F)).sum=10000*(n+F+2)*(rowMass rows+rows.length) :=by
  induction rows with
  | nil=>simp only [List.map_nil,List.sum_nil,rowMass,List.length_nil,Nat.zero_add,Nat.mul_zero]
  | cons row rows ih=>
    simp only [List.map_cons,List.sum_cons,factorBudget,ih,rowMass,List.length_cons]
    ring
/-- Complete actual factor loop is paid by actual source bytes and its physically allocated binary counter width. -/
theorem factorsBudget_le (n F:Nat) (rows:List (List (List Bool))) :
    factorsBudget n F rows≤10000*(n+F+2)*(inputTape rows).length+1 :=by
  have h:=outer_length rows
  have hs:rowMass rows+rows.length≤(inputTape rows).length:=by omega
  unfold factorsBudget
  rw [factor_sum]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hs) 1
/-- Own complete acquisition/initialization/row-loop prefix fits one fixed physical-input quadratic. -/
theorem prefixBudget_le (n:Nat) (rows:List (List (List Bool))) :prefixBudget n rows≤100000*(inputSize n rows)^2 :=by
  let S:=inputSize n rows
  have hs:1≤S:=by dsimp [S,inputSize];omega
  have hL:(inputTape rows).length≤S:=by dsimp [S,inputSize];omega
  have houter:=outer_length rows
  have hF:rows.length≤(inputTape rows).length:=by omega
  have hW:n+rows.length+2≤2*S:=by dsimp [S,inputSize];omega
  have hacq:=acquisitionTime_le n rows
  change acquisitionTime n rows≤100*S at hacq
  have hp:=Nat.pow_le_pow_left hW 2
  have hinit:100*(n+rows.length+2)^2≤400*S^2:=by nlinarith only [hp]
  have hf:=factorsBudget_le n rows.length rows
  have hm:=Nat.mul_le_mul hW hL
  have hfactor:factorsBudget n rows.length rows≤20000*S^2+1:=by nlinarith only [hf,hm]
  have hself:S≤S^2:=Nat.le_pow (by decide:0<(2:Nat))
  have h1:1≤S^2:=Nat.one_le_pow _ _ hs
  unfold prefixBudget
  change _≤100000*S^2
  omega
/-- One fixed bound before every physically acquired original row/count operand. -/
def polynomial (n:Nat) (rows:List (List (List Bool))) :Nat :=1000000*(inputSize n rows)^2
/-- Same actual whole program clock, with all final history bytes paid by its own actual prefix. -/
theorem timeBound_le (n:Nat) (rows:List (List (List Bool))) :timeBound n rows≤polynomial n rows :=by
  have hp:=prefixBudget_le n rows
  have houter:=outer_length rows
  have hF:rows.length≤(inputTape rows).length:=by omega
  have hW:n+rows.length+1≤ inputSize n rows:=by unfold inputSize;omega
  have hs:1≤ inputSize n rows:=by unfold inputSize;omega
  have hself:inputSize n rows≤(inputSize n rows)^2:=Nat.le_pow (by decide:0<(2:Nat))
  have h1:1≤(inputSize n rows)^2:=Nat.one_le_pow _ _ hs
  unfold timeBound polynomial inputSize at *
  omega
/-- Whole actual prepared source, including real halt, has its own fixed quadratic byte bound. -/
theorem source_run_bounded (n:Nat) (rows:List (List (List Bool))) :
    ∃q≤polynomial n rows,run program q (source n rows)=some (done n rows) :=by
  obtain ⟨q,hq,hr⟩:=source_run n rows
  exact ⟨q,hq.trans (timeBound_le n rows),hr⟩
/-- Every successful actual prefix stops before this SAMEprogram's already proved real halt. -/
theorem prefix_fuel (n:Nat) (rows:List (List (List Bool))) (fuel:Nat) (out:C.State Stack Label)
    (hr:run program fuel (source n rows)=some out) :fuel≤polynomial n rows :=by
  obtain ⟨q,hq,he⟩:=source_run_bounded n rows
  have hh:run program 1 (done n rows)=none:=rfl
  have hf:fuel≤q:=by
    by_contra hn
    have h:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hh,Option.bind_none] at hr
    cases hr
  exact hf.trans hq
/-- All21actual words and all actual real-return cells are charged at every successful source prefix. -/
theorem prefix_cells (n:Nat) (rows:List (List (List Bool))) (fuel:Nat) (out:C.State Stack Label)
    (hr:run program fuel (source n rows)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤100000000*(inputSize n rows)^2 :=by
  have hi:∀k,((source n rows).data k).length≤ inputSize n rows:=by
    intro k
    exact (initial_length n rows k).trans (by unfold inputSize;omega)
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputSize n rows) _ _ hi hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ _ hr
  change out.frames.length≤0+fuel at hf
  have hs:=SemiprimeD1StackNetworkOwnerIndexBounds.word_sum_le out.data (inputSize n rows+fuel) hd
  rw [stack_card] at hs
  have ht:=prefix_fuel n rows fuel out hr
  have hp:inputSize n rows≤(inputSize n rows)^2:=Nat.le_pow (by decide:0<(2:Nat))
  unfold polynomial at ht
  omega
/-- Genuine fixed finite-machine source certificate on ONLYthe actual prepared row/count words. -/
noncomputable def sourceInTime (n:Nat) (rows:List (List (List Bool))) :
    StateTransition.EvalsToInTime machine.step (configuration (source n rows))
      (some (configuration (done n rows))) (polynomial n rows) :=by
  apply SemiprimeD1StackCalls.evalsCorrect Stack.rows Stack.output (ctl .start) program
  have h:=source_run_bounded n rows
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Every actual compiled prefix includes all21data words and the full actual return stack. -/
theorem machine_prefix_cells (n:Nat) (rows:List (List (List Bool))) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (configuration (source n rows)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤100000000*(inputSize n rows)^2 :=by
  have he:=SemiprimeD1StackCalls.run_correct Stack.rows Stack.output (ctl .start) program fuel (source n rows)
  have hh:=he.trans hr
  cases hout:run program fuel (source n rows) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells n rows fuel out hout
/-- Actual transitions expand to a bounded number of genuine fixed-machine statements. -/
theorem compile_depth (pc:Label) :SemiprimeD1StackBytecode.statementDepth (machine.m pc)≤4 :=
  SemiprimeD1StackCalls.compile_depth (ctl .start) (program pc)
end RiemannGaussian.SemiprimeD1StackSourceOccurrencesBounds
