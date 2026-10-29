/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceOccurrencesPrescan
import RiemannGaussian.SemiprimeD1StackSourceOccurrencesFactors
/-! # Actual whole row/count acquisition of ordered compact occurrence keys
One real prescan derives F and counter width, actual n markers initialize the
binary factor namespace, and the same source emits every occurrence. The final
reverse is paid by the SAMEactual prefix that produced its history bytes.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceOccurrencesExecution
open SemiprimeD1StackSourceOccurrences SemiprimeD1StackSourceOccurrencesPrimitives
open SemiprimeD1StackSourceOccurrencesView SemiprimeD1StackSourceOccurrencesEncoding
open SemiprimeD1StackSourceOccurrencesPrescan SemiprimeD1StackSourceOccurrencesFactors
open SemiprimeD1StackSourceOccurrencesCounter SemiprimeD1StackProcedureTrace
open SemiprimeD1StackNetworkOwnerIndexEncoding (payload records_payload)
local notation "ctl" => Label.local
/-- The actual source starts with ONLYthe nested physical owner rows and actual acquired unary n. -/
def source (n:Nat) (rows:List (List (List Bool))) :C.State Stack Label :=
  initial (inputTape rows) (List.replicate n true)
/-- Exact full clean source bank before its final physical history reversal and counter cleanup. -/
def preData (n:Nat) (rows:List (List (List Bool))) :Stack→List Bool :=
  data (inputTape rows) (List.replicate n true) [] [] [] [] (counterWord n rows.length (n+rows.length)) [] []
    (payload (pairs n rows)).reverse (List.replicate rows.length true) (List.replicate (rows.map List.length).sum true)
/-- Exact actual final bank: both input tapes retained, canonical keys, actual F/M tallies, all other work empty. -/
def result (n:Nat) (rows:List (List (List Bool))) :Stack→List Bool :=
  Function.update (data (inputTape rows) (List.replicate n true) [] [] [] [] [] [] [] []
    (List.replicate rows.length true) (List.replicate (rows.map List.length).sum true)) .output (tape n rows)
/-- Actual clean halt of the same whole prepared two-input source. -/
def done (n:Nat) (rows:List (List (List Bool))) :C.State Stack Label :=⟨none,none,none,result n rows,[]⟩
/-- Own paid prefix allowance sums the real width/F acquisition, n initialization, row copy and whole actual factor loop. -/
def prefixBudget (n:Nat) (rows:List (List (List Bool))) :Nat :=
  acquisitionTime n rows+100*(n+rows.length+2)^2+5*(inputTape rows).length+4+factorsBudget n rows.length rows
/-- Same-program whole-source clock includes its prefix-derived final history length and all actual cleanup/halt steps. -/
def timeBound (n:Nat) (rows:List (List (List Bool))) :Nat :=
  3*prefixBudget n rows+2*((inputTape rows).length+n)+(n+rows.length+1)+6
/-- Actual source initialization is charged only to its two actual input words. -/
theorem initial_length (n:Nat) (rows:List (List (List Bool))) (k:Stack) :
    ((source n rows).data k).length≤(inputTape rows).length+n :=by
  cases k <;> simp [source,initial,input]
/-- The actual source reaches its pre-output boundary with every occurrence, factor and counter value acquired physically. -/
theorem pre_trace (n:Nat) (rows:List (List (List Bool))) :
    ∃q≤prefixBudget n rows,Runs program q (ctl .start) (source n rows).data (ctl .finishSeed) (preData n rows) :=by
  have h0:=source_prescan n rows
  obtain ⟨a,ha,h1⟩:=initialize_run (inputTape rows) n rows.length
  let bank:=data (inputTape rows) (List.replicate n true) [] [] [] [] (counterWord n rows.length n) [] [] []
    (List.replicate rows.length true) []
  have h2:=copy_call .rows .mainCopy .factorTag rfl bank (inputTape rows) [] rfl rfl rfl
  simp only [List.append_nil] at h2
  change Runs program (5*(inputTape rows).length+4) _ bank _ (Function.update bank .reader (inputTape rows)) at h2
  have he2:Function.update bank .reader (inputTape rows)=
      data (inputTape rows) (List.replicate n true) (inputTape rows) [] [] [] (counterWord n rows.length n) [] [] []
        (List.replicate rows.length true) []:=data_reader _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [he2] at h2
  obtain ⟨b,hb,h3⟩:=factors_loop (inputTape rows) (List.replicate n true) [] (List.replicate rows.length true) [] n rows.length 0 rows (by omega)
  simp only [Nat.add_zero,List.append_nil] at h3
  have h:=join (join (join h0 h1) h2) h3
  refine ⟨acquisitionTime n rows+a+(5*(inputTape rows).length+4)+b,?_,h⟩
  unfold prefixBudget
  omega
/-- Real final seed, sole full-history reverse and physical counter drain, without a supplied output length. -/
theorem finish_trace (before:Stack→List Bool) (hist counter:List Bool)
    (hh:before .history=hist) (hc:before .counter=counter) (ho:before .output=[]) :
    Runs program (2*hist.length+counter.length+5) (ctl .finishSeed) before (ctl .done)
      (Function.update (Function.update (Function.update before .history []) .output (hist.reverse++[false])) .counter []) :=by
  let b1:=Function.update before .output [false]
  let b2:=Function.update (Function.update b1 .history []) .output (hist.reverse++[false])
  have h0:=push_run .finishSeed (ctl .outputReverse) .output false before rfl
  rw [ho] at h0
  have h1:=reverse_call .output .outputReverse .clearCounter rfl b1 hist [false]
    (by simpa [b1,reverseStack,Function.update] using hh) (by simp [b1,reverseStack])
  have h2:=drain_loop .clearCounter (ctl .done) .counter rfl b2 counter
    (by simpa [b2,b1,Function.update] using hc)
  have h:=join (join h0 h1) h2
  have he:Function.update b2 .counter []=
      Function.update (Function.update (Function.update before .history []) .output (hist.reverse++[false])) .counter []:=by
    funext k;cases k <;> simp [b2,b1,Function.update]
  rw [he] at h
  convert h using 1; omega
/-- The final exact key bytes are the real source result after clearing its history and actual counter. -/
theorem finish_result (n:Nat) (rows:List (List (List Bool))) :
    Function.update (Function.update (Function.update (preData n rows) .history []) .output
      ((payload (pairs n rows)).reverse.reverse++[false])) .counter []=result n rows :=by
  have ht:tape n rows=payload (pairs n rows)++[false]:=by
    exact records_payload (pairs n rows) []
  funext k
  cases k <;> simp [preData,result,data,Function.update,List.reverse_reverse,ht]
/-- Whole actual source trace pays every final history byte by its SAMEsuccessful prefix run. -/
theorem source_trace (n:Nat) (rows:List (List (List Bool))) :
    ∃q,q+1≤timeBound n rows ∧ Runs program q (ctl .start) (source n rows).data (ctl .done) (result n rows) :=by
  obtain ⟨q,hq,hpre⟩:=pre_trace n rows
  obtain ⟨temp,ht,hAt⟩:=hpre [] (source n rows) ⟨rfl,rfl,rfl⟩
  have hh:=SemiprimeD1StackReturnLink.run_data_bound program q ((inputTape rows).length+n) _ _ (initial_length n rows) ht .history
  rw [hAt.2.1] at hh
  change (payload (pairs n rows)).reverse.length≤(inputTape rows).length+n+q at hh
  have hf:=finish_trace (preData n rows) (payload (pairs n rows)).reverse
    (counterWord n rows.length (n+rows.length)) rfl rfl rfl
  rw [finish_result] at hf
  refine ⟨q+(2*(payload (pairs n rows)).reverse.length+(counterWord n rows.length (n+rows.length)).length+5),?_,join hpre hf⟩
  have hc:=counter_length n rows.length (n+rows.length) (by omega)
  unfold timeBound
  omega
/-- Actual two-input physical source reaches its real clean halt with exact original-order occurrence keys. -/
theorem source_run (n:Nat) (rows:List (List (List Bool))) :
    ∃q≤timeBound n rows,SemiprimeD1StackCalls.run program q (source n rows)=some (done n rows) :=by
  obtain ⟨q,hq,hr⟩:=source_trace n rows
  obtain ⟨finish,hf,hAt⟩:=hr [] (source n rows) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result n rows) [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
end RiemannGaussian.SemiprimeD1StackSourceOccurrencesExecution
