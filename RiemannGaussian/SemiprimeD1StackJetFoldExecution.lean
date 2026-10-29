/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetFoldSum
import RiemannGaussian.SemiprimeD1StackJetFoldContext
/-! # Whole actual original-header and acquired-cache child-result fold source
The caller supplies physical child results, not a solver. The full entry runs
real context acquisition; the same program's prepared entry reuses that exact
actual acquired cache. Both include input copying, actual recursive arithmetic,
all cleanup/returns, and the genuine final halt.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackJetFoldExecution
open SemiprimeD1StackJetFold SemiprimeD1StackJetFoldState SemiprimeD1StackJetFoldWords
open SemiprimeD1StackJetFoldPrimitives SemiprimeD1StackJetFoldSpec SemiprimeD1StackJetFoldContext
open SemiprimeD1StackJetFoldSum SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Exact physical stopped words: original inputs/acquired context and the actually computed dense sum. -/
def result (axes:List Nat) (precision:List Bool) (modes:Modes):Stack→List Bool:=
  data (sumOut (acquiredHeader axes precision (modeTape modes)) (sumWords (context axes precision) modes) [])
/-- Genuine clean halt; all111allocated private/shadow roles and real returns have their literal reached state. -/
def done (axes:List Nat) (precision:List Bool) (modes:Modes):C.State Stack Label:=
  ⟨none,none,none,result axes precision modes,[]⟩
/-- Actual prepared-entry allowance: physical original-input copy, complete folds, real return and final halt. -/
def readyTimeBound (axes:List Nat) (precision:List Bool) (modes:Modes):Nat:=
  5*(modeTape modes).length+sumBudget (context axes precision)
    (acquiredHeader axes precision (modeTape modes)) modes+7
/-- Whole full-source allowance additionally pays the real original-header acquisition and its real return. -/
def timeBound (axes:List Nat) (precision:List Bool) (modes:Modes):Nat:=
  SemiprimeD1StackJetContextCorrectness.budget axes precision+1+readyTimeBound axes precision modes
/-- One actual prepared trace consumes only the already acquired physical cache and original child-result tape. -/
theorem ready_trace (axes:List Nat) (hp:∀q∈axes,0 < q) (precision:List Bool) (modes:Modes):
    ∃time,time+1 ≤readyTimeBound axes precision modes ∧ Runs program time (ctl .prepared)
      (ready axes precision (modeTape modes)).data (ctl .done) (result axes precision modes):=by
  let ctx:=context axes precision
  let h:=acquiredHeader axes precision (modeTape modes)
  let v:=bank h [] [] [] [] [] [] [] [] []
  obtain ⟨u,hu,hFold⟩:=sum_run ctx hp h (header_matches axes precision (modeTape modes)) modes []
  change u ≤ sumBudget (context axes precision) (acquiredHeader axes precision (modeTape modes)) modes at hu
  have h0:=copy_view .children .prepared .sumCall v rfl
  change Runs program (5*(modeTape modes).length+4) _ _ _
    (data (Function.update v .modes ((modeTape modes)++[]))) at h0
  rw [List.append_nil] at h0
  change Runs program (5*(modeTape modes).length+4) _ _ _ (data (sumNode h modes [])) at h0
  have h1:=recursive_call .sumCall .sumVisit .done _ _ u rfl hFold
  have h:=join h0 h1
  refine ⟨(5*(modeTape modes).length+4)+(u+2),?_,h⟩
  unfold readyTimeBound
  omega
/-- SAME program's actually acquired cache entry executes both folds and its true final halt. -/
theorem ready_run (axes:List Nat) (hp:∀q∈axes,0 < q) (precision:List Bool) (modes:Modes):
    ∃time ≤readyTimeBound axes precision modes,C.run program time (ready axes precision (modeTape modes))=
      some (done axes precision modes):=by
  obtain ⟨time,ht,hr⟩:=ready_trace axes hp precision modes
  obtain ⟨finish,hf,ha⟩:=hr [] (ready axes precision (modeTape modes)) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result axes precision modes) [] finish ha
  refine ⟨time+1,ht,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hh
/-- Whole original-header trace contains the actual context call before the same prepared arithmetic path. -/
theorem source_trace (axes:List Nat) (hp:∀q∈axes,0 < q) (precision:List Bool) (modes:Modes):
    ∃time,time+1 ≤timeBound axes precision modes ∧ Runs program time (ctl .start)
      (initial (SemiprimeD1TensorTapeCodec.vectorBits (axes.map SemiprimeD1StackUnaryDivmod.unary)) precision (modeTape modes)).data
      (ctl .done) (result axes precision modes):=by
  obtain ⟨c,hc,h0⟩:=context_call axes hp precision (modeTape modes)
  obtain ⟨t,ht,h1⟩:=ready_trace axes hp precision modes
  refine ⟨c+t,?_,join h0 h1⟩
  unfold timeBound
  omega
/-- Exact whole actual finite source, with only original headers and actual prepared child-result words supplied. -/
theorem source_run (axes:List Nat) (hp:∀q∈axes,0 < q) (precision:List Bool) (modes:Modes):
    ∃time ≤timeBound axes precision modes,C.run program time
      (initial (SemiprimeD1TensorTapeCodec.vectorBits (axes.map SemiprimeD1StackUnaryDivmod.unary)) precision (modeTape modes))=
        some (done axes precision modes):=by
  obtain ⟨time,ht,hr⟩:=source_trace axes hp precision modes
  obtain ⟨finish,hf,ha⟩:=hr []
    (initial (SemiprimeD1TensorTapeCodec.vectorBits (axes.map SemiprimeD1StackUnaryDivmod.unary)) precision (modeTape modes)) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result axes precision modes) [] finish ha
  refine ⟨time+1,ht,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hh
/-- Literal stopped coefficient word order, without canonicalizing or reassociating the child inputs. -/
theorem output_words (axes:List Nat) (precision:List Bool) (modes:Modes):
    (done axes precision modes).data output=jetTape (sumWords (context axes precision) modes):=
  data_get (sumOut (acquiredHeader axes precision (modeTape modes)) (sumWords (context axes precision) modes) []) .sum
/-- The actual complete source computes exactly the old native ordered products followed by its old ordered sum. -/
theorem output_native (axes:List Nat) (precision:List Bool)
    (runs:List (List SemiprimeD1JetAffineCoefficient.JetRun)):
    (done axes precision (runs.map (fun row=>row.map (fun r=>r.words)))).data output=
      jetTape (SemiprimeD1JetAffineCoefficient.sumRuns (context axes precision)
        (runs.map (SemiprimeD1RecursiveCounter.product (context axes precision)))).words:=by
  rw [output_words,sum_native]
end RiemannGaussian.SemiprimeD1StackJetFoldExecution
