/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetBlocksReady
/-! # Whole four-input block acquisition: real old context once, then real scan
Inputs are the unary-axis header, binary old precision, actual unary q and an
actual coefficient vector. The expected native blocks occur in proofs only.+-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackJetBlocksExecution
open SemiprimeD1StackJetBlocks SemiprimeD1StackJetBlocksPrimitives SemiprimeD1StackJetBlocksView
open SemiprimeD1StackJetBlocksEncoding SemiprimeD1StackJetBlocksReady SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
local notation "ctl" => Label.local
/-- Original physical four-input state, before the actual context supplier. -/
def source (axes:List Nat) (precision:List Bool) (q:Nat) (words:List (List Bool)) :C.State Stack Label :=
  initial (vectorBits (axes.map unary)) precision (List.replicate q true) (vectorBits words)
/-- The actual old-context supplier's exact acquired bank. -/
def contextResult (axes:List Nat) (precision:List Bool) :X.Stack→List Bool :=
  SemiprimeD1StackJetContextCorrectness.finalData axes precision
/-- Whole own source allowance includes the literal context source and its actual call/return. -/
def timeBound (axes:List Nat) (precision:List Bool) (q:Nat) (words:List (List Bool)) :Nat :=
  SemiprimeD1StackJetContextCorrectness.budget axes precision+1+readyBound axes.prod q words
/-- REALold context call; every new actual source/q/private word remains untouched. -/
theorem context_call (axes:List Nat) (hp:∀r∈axes,0<r) (precision coefficients blocks:List Bool) :
    ∃t≤SemiprimeD1StackJetContextCorrectness.budget axes precision+1,
      Runs program t (ctl .start) (input (vectorBits (axes.map unary)) precision blocks coefficients)
        (ctl .ready) (data (contextResult axes precision) coefficients blocks [] [] [] [] [] [] []) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackJetContextCorrectness.source_run axes hp precision
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program contextStack Label.context
    (fun _ _ h=>Sum.inl.inj h) X.program .start (fun _=>rfl) (ctl .start) (ctl .ready) rfl t
    (X.initial (vectorBits (axes.map unary)) precision)
    (⟨none,none,none,contextResult axes precision,[]⟩:C.State X.Stack X.Label)
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · cases k <;> rfl
/-- Entire context-acquiring source through all real cleanup, immediately before halt. -/
theorem source_trace (axes:List Nat) (hp:∀r∈axes,0<r) (precision:List Bool) (q:Nat)
    (words:List (List Bool)) :
    ∃t,t+1≤timeBound axes precision q words ∧ Runs program t (ctl .start) (source axes precision q words).data
      (ctl .done) (done (contextResult axes precision) axes.prod q words).data :=by
  obtain ⟨a,ha,h0⟩:=context_call axes hp precision (vectorBits words) (List.replicate q true)
  obtain ⟨b,hb,h1⟩:=ready_trace (contextResult axes precision) axes.prod q rfl words
  exact ⟨a+b,by unfold timeBound;omega,join h0 h1⟩
/-- Same fixed31-role program acquires context, emits exact ascending blocks and really halts. -/
theorem source_run (axes:List Nat) (hp:∀r∈axes,0<r) (precision:List Bool) (q:Nat)
    (words:List (List Bool)) :
    ∃t≤timeBound axes precision q words,SemiprimeD1StackCalls.run program t (source axes precision q words)=
      some (done (contextResult axes precision) axes.prod q words) :=by
  obtain ⟨t,ht,h⟩:=source_trace axes hp precision q words
  obtain ⟨out,ho,ha⟩:=h [] (source axes precision q words) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (done (contextResult axes precision) axes.prod q words).data [] out ha
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,ho,Option.bind_some];exact hh⟩
/-- Genuine compiled whole prepared four-input source, with its SAMEown source clock. -/
noncomputable def sourceInTime (axes:List Nat) (hp:∀r∈axes,0<r) (precision:List Bool) (q:Nat)
    (words:List (List Bool)) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (source axes precision q words))
      (some (SemiprimeD1StackCalls.configuration (done (contextResult axes precision) axes.prod q words)))
      (timeBound axes precision q words) :=by
  let h:=source_run axes hp precision q words
  let t:=Classical.choose h
  have ht:=Classical.choose_spec h
  apply SemiprimeD1StackCalls.evalsCorrect (aux .coefficients) (aux .output) (ctl .start) program
  exact ⟨⟨t,ht.2⟩,ht.1⟩
end RiemannGaussian.SemiprimeD1StackJetBlocksExecution
