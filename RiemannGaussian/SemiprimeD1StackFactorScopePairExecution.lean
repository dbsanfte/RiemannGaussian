/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFactorScopePairScan
/-! # Whole binary-N-only acquired scoped-port to factor/scope pair source -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackFactorScopePairExecution
open SemiprimeD1StackFactorScopePairs SemiprimeD1FactorScopePairEncoding
open SemiprimeD1StackFactorScopePairView SemiprimeD1StackFactorScopePairPrimitives SemiprimeD1StackFactorScopePairScan
open SemiprimeD1StackProcedureFragments (Runs)
/-- Mathematical reached nine-field list, produced from the actual two acquired source caches. -/
def rows (bits : List Bool) : List Record := List.zipWith joined
  (SemiprimeD1StackPortScopeSource.ports bits) (SemiprimeD1StackPortScopeSource.ids bits)
/-- Complete physically retained original scoped-port source state. -/
def base (bits : List Bool) : S.Stack→List Bool := SemiprimeD1StackPortScopeExecution.result bits
/-- Exact reached source store before the actual preserving reader copy. -/
def afterSource (bits : List Bool) : Stack→List Bool := clean (base bits) [] (fun _=>[]) []
/-- Exact reached reader copy; no reader table is a runtime source argument. -/
def ready (bits : List Bool) : Stack→List Bool := clean (base bits) (stream (rows bits) []) (fun _=>[]) []
/-- Exact final all-role physical store, retaining the acquired source. -/
def result (bits : List Bool) : Stack→List Bool :=
  data (base bits) [] (fun _=>[]) [] [] (SemiprimeD1StackOwnerFibre.records ((rows bits).map pair) []) []
/-- Actual final flags and all real return cells are empty. -/
def done (bits : List Bool) : C.State Stack Label :=⟨none,none,none,result bits,[]⟩
/-- Exact source output field, derived from its actual reached state. -/
theorem source_output (bits : List Bool) : afterSource bits sourceOutput=stream (rows bits) [] := by
  change SemiprimeD1StackPortScopeExecution.result bits (SemiprimeD1StackPortScopeRecords.aux .output)=_
  rw [SemiprimeD1StackPortScopeExecution.original_scope_records,rows,joined_stream]
  rfl
/-- One real nested original-N source call; no supplied graph, record list or count. -/
theorem source_call (bits : List Bool) (hb : bits≠[]) :
    ∃t≤10^111*(bits.length+1)^30,Runs program (t+1) (.local .main) (input bits) (.local .copy) (afterSource bits) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackPortScopeBounds.source_run_polynomial bits hb
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program sourceStack Label.source Sum.inl_injective
    S.program (.local .main) (fun _=>rfl) (.local .main) (.local .copy) rfl t (S.initial bits)
    (SemiprimeD1StackPortScopeExecution.done bits)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      cases k with
      | inl k=>exact (hk k rfl).elim
      | inr k=>rcases k with k|k <;> first | rfl | cases k <;> rfl
/-- The complete acquired scoped-port stream is copied once and retained. -/
theorem reader_copy (bits : List Bool) :
    Runs program (5*(stream (rows bits) []).length+4) (.local .copy) (afterSource bits) (.local .loop) (ready bits) := by
  have h:=copy_call (afterSource bits) rfl
  rw [source_output] at h
  change Runs program _ _ _ _ (Function.update (data (base bits) [] (fun _=>[]) [] [] [] [])
    (aux .reader) (stream (rows bits) []++[])) at h
  rw [List.append_nil,update_reader] at h
  exact h
/-- Same-code source/copy/scan allowance, retaining every real call and final halt. -/
def timeBound (bits : List Bool) : Nat :=
  10^111*(bits.length+1)^30+5*(stream (rows bits) []).length+totalTime (rows bits)+5
/-- Entire actual N-only source, with all nine-field parsing and output materialization. -/
theorem source_run (bits : List Bool) (hb : bits≠[]) :
    ∃t≤timeBound bits,C.run program t (initial bits)=some (done bits) := by
  obtain ⟨a,ha,h0⟩:=source_call bits hb
  have h1:=reader_copy bits
  have hl:=loop_run (rows bits) (base bits) []
  simp only [List.append_nil] at hl
  have h:=h0.trans (h1.trans (hl.trans (finish_run (base bits) (rows bits))))
  obtain ⟨finish,hr,hAt⟩:=h [] (initial bits) ⟨rfl,rfl,rfl⟩
  have he:=SemiprimeD1StackProcedureTrace.halt_run program (.local .done) rfl (result bits) [] finish hAt
  refine ⟨(a+1)+((5*(stream (rows bits) []).length+4)+
    (loopTime (rows bits)+(2*(raw (rows bits)).length+6)))+1,?_,?_⟩
  · unfold timeBound totalTime;omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,he]
    rfl
/-- Literal original input byte store, with every added physical role empty. -/
theorem input_eq (bits : List Bool) : input bits=fun k=>if k=originalInput then bits else [] := by
  funext k
  cases k with
  | inl k=>
    have hi:S.input bits k=(if k=S.originalInput then bits else []) := by
      cases k with
      | inl k=>
        simpa only [SemiprimeD1StackPortScopeRecords.input,SemiprimeD1StackPortScopeRecords.originalInput,
          SemiprimeD1StackPortScopeRecords.sourceStack,Sum.elim_inl,Sum.inl.injEq]
          using SemiprimeD1StackPortScopeExecution.source_input bits k
      | inr k=>rfl
    simpa only [input,Sum.elim_inl,originalInput,sourceStack,Sum.inl.injEq] using hi
  | inr k=>rfl
/-- Complete source is initialized with original binary N alone. -/
theorem initial_eq (bits : List Bool) : Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) := by
  have hs:initial bits=SemiprimeD1StackCalls.initial originalInput (.local .main) bits:=by
    unfold initial SemiprimeD1StackCalls.initial
    rw [input_eq]
  rw [hs]
  exact (SemiprimeD1StackCalls.initial_correct originalInput (aux .output) (.local .main) program bits).symm
/-- Actual source stream remains available to later original routing consumers. -/
theorem retained_source (bits : List Bool) (k : S.Stack) : result bits (sourceStack k)=base bits k := rfl
/-- Exact compatible pair grammar, preserving original factor-major row order. -/
theorem output_pairs (bits : List Bool) : result bits (aux .output)=
    SemiprimeD1StackOwnerFibre.records ((rows bits).map pair) [] := rfl
end RiemannGaussian.SemiprimeD1StackFactorScopePairExecution
