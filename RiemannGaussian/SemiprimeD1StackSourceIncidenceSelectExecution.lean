/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectInitialize
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectLoop
/-! # Complete actual seven-input incidence selector and own whole-source clock
Only occurrence records, alphabet records, three binary powers and two acquired
unary count words enter the literal program. The theorem-side input description
below is never a runtime operand, callback or source-program parameter.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectExecution
open SemiprimeD1StackSourceIncidenceSelect SemiprimeD1StackSourceIncidenceSelectPrimitives
open SemiprimeD1StackSourceIncidenceSelectView SemiprimeD1StackSourceIncidenceSelectInitialize
open SemiprimeD1StackSourceIncidenceSelectLoop SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl" => Label.local
/-- Proof-only interpretation of the seven physical words actually acquired by the caller. -/
structure Inputs where
  /-- Actual ordered owner/factor occurrence keys. -/
  rows:List (List Bool×List Bool)
  /-- First actual candidate ID/colour row, including the valid zero-ID case. -/
  first:List Bool×List Bool
  /-- All remaining actual candidate records, in their original acquired order. -/
  entries:List (List Bool×List Bool)
  /-- Actual acquired binary square power. -/
  square:List Bool
  /-- Actual acquired binary cube power. -/
  cube:List Bool
  /-- Actual acquired binary fourth power. -/
  fourth:List Bool
  /-- The actual unary owner-marker input length. -/
  n:Nat
  /-- The actual unary factor-marker input length. -/
  F:Nat
/-- Actual physical catalogue bytes; no candidate count is supplied. -/
def catalogue (i:Inputs) :List Bool :=SemiprimeD1StackOwnerLookup.records (i.first::i.entries) []
/-- Actual physical occurrence stream bytes, retaining every repeated incidence. -/
def occurrenceTape (i:Inputs) :List Bool :=SemiprimeD1StackOwnerLookup.records i.rows []
/-- Whole fixed-program source has empty environment/work and exactly the seven acquired inputs. -/
def source (i:Inputs) :C.State Stack Label :=
  initial (occurrenceTape i) (catalogue i) i.square i.cube i.fourth (List.replicate i.n true) (List.replicate i.F true)
/-- Exact newest-first ID list specified by the actual closed source score and physical marker count. -/
def selectedIDs (i:Inputs) :List (List Bool) :=
  SemiprimeD1StackSourceIncidenceSelectScore.selected i.rows i.square i.cube i.fourth i.first.1 (i.entries.map Prod.fst)
    (List.replicate (i.n+i.F) true) []
/-- All63 stopped words: exact retained inputs, complete acquired environment, selected vector and cleared work. -/
def result (i:Inputs) :Stack→List Bool :=
  clean (selectedIDs i) [] (vectorBits (selectedIDs i)) (occurrenceTape i) i.square i.cube i.fourth
    (catalogue i) (List.replicate i.n true) (List.replicate i.F true) [] [] [] [] [] []
/-- Actual final halt has clear flags and no unresolved real source return cells. -/
def done (i:Inputs) :C.State Stack Label :=⟨none,none,none,result i,[]⟩
/-- Own complete primitive/call cap pays once-only real initialization/copies, whole actual loop and final halt. -/
def timeBound (i:Inputs) :Nat :=5*(i.n+i.F)+12+loopClock i.rows i.square i.cube i.fourth i.first i.entries (i.n+i.F) []+1
/-- The exact complete actual source trace reaches the generated selected prefix without any supplied environment or score. -/
theorem source_trace (i:Inputs) :
    ∃t,t+1 ≤ timeBound i ∧ Runs program t (ctl .start) (source i).data (ctl .done) (result i) :=by
  have h0:=prepare_run (occurrenceTape i) (catalogue i) i.square i.cube i.fourth i.n i.F
  obtain ⟨t,ht,h1⟩:=loop_run i.rows i.square i.cube i.fourth (List.replicate i.n true) (List.replicate i.F true)
    i.first i.entries (i.n+i.F) []
  exact ⟨_,by unfold timeBound;omega,join h0 h1⟩
/-- Whole source includes the true final halt; every real query/extension/copy/parser/compare return is already paid. -/
theorem source_run (i:Inputs) :
    ∃t ≤ timeBound i,SemiprimeD1StackCalls.run program t (source i)=some (done i) :=by
  obtain ⟨t,ht,hr⟩:=source_trace i
  obtain ⟨finish,hf,hAt⟩:=hr [] (source i) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result i) [] finish hAt
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- Genuine same-machine certificate has the actual prepared seven-word acquired bank as its initial configuration. -/
noncomputable def selectorInTime (i:Inputs) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (source i))
      (some (SemiprimeD1StackCalls.configuration (done i))) (timeBound i) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (queryStack (Q.aux .source)) selected (ctl .start) program
  let h:=source_run i
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectExecution
