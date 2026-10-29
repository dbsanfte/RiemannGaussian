/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFactorScopeFibre
/-! # Actual complete and prepared factor-scope filter traces -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackFactorScopeFibreExecution
open SemiprimeD1StackFactorScopeFibre SemiprimeD1StackProcedureTrace
/-- One real complete pair-source call, preserving the actual current query word. -/
theorem source_call (bits key : List Bool) (hb : bits≠[]) :
    ∃t≤SemiprimeD1StackFactorScopePairBounds.runBound bits,
      Runs program (t+1) .main (initial bits key).data .copy (afterSource bits key) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackFactorScopePairBounds.source_run_polynomial bits hb
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program sourceStack Label.source Sum.inl_injective
    P.program (.local .main) (fun _=>rfl) .main .copy rfl t (P.initial bits) (P.done bits)
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
      | inr k=>rfl
/-- Whole retained pair catalogue is physically copied into the filter reader. -/
theorem copy_call (bits key : List Bool) :
    Runs program (5*(pairTape bits).length+4) .copy (afterSource bits key) .filter (afterCopy bits key) := by
  apply included_call program copyStack Label.copyCode copy_injective SemiprimeD1StackCopy.code 0
    (fun _=>rfl) .copy .filter rfl (5*(pairTape bits).length+3)
    (SemiprimeD1StackCopy.state 0 none (pairTape bits) [] [])
    (SemiprimeD1StackCopy.done (pairTape bits) (pairTape bits))
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words (pairTape bits) [] none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk
      cases k with
      | inl k=>rfl
      | inr k=>cases k with
        | inr k=>rfl
        | inl k=>
          cases k with
          | inl k=>cases k <;> rfl
          | inr k=>cases k with
            | reader=>exact (hk 1 rfl).elim
            | query | fieldScratch | valid | copyScratch | payload | output | frameBuffer | frameScratch | reversed=>rfl
/-- The exact generic source performs all numeric matches, parses, erasures and emits. -/
theorem fibre_call (bits key : List Bool) :
    Runs program (SemiprimeD1StackOwnerFibreExecution.totalTime key
      ((P.rows bits).map SemiprimeD1FactorScopePairEncoding.pair)+1)
      .filter (afterCopy bits key) .done (result bits key) := by
  apply SemiprimeD1StackProcedureInclusion.included_call program fibreStack Label.fibre
    (by intro a b h;exact Sum.inl_injective (Sum.inr_injective h)) F.program .loop
    (fun _=>rfl) .filter .done rfl _ (F.initial key (pairTape bits))
    (F.done key ((P.rows bits).map SemiprimeD1FactorScopePairEncoding.pair) [])
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackOwnerFibreExecution.source_run key _ []
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      cases k with
      | inl k=>rfl
      | inr k=>cases k with
        | inl k=>exact (hk k rfl).elim
        | inr k=>rfl
/-- Prepared trace retains the pair acquisition once across any number of factors. -/
def preparedTime (bits key : List Bool) : Nat :=5*(pairTape bits).length+
  SemiprimeD1StackOwnerFibreExecution.totalTime key ((P.rows bits).map SemiprimeD1FactorScopePairEncoding.pair)+5
/-- Concrete caller can include this trace from.copy after already acquiring the source. -/
theorem prepared_trace (bits key : List Bool) :
    Runs program (preparedTime bits key) .copy (afterSource bits key) .done (result bits key) := by
  have h:=runs_trans program _ _ _ _ _ _ _ _ (copy_call bits key) (fibre_call bits key)
  simpa only [preparedTime,show (5*(pairTape bits).length+4)+
    (SemiprimeD1StackOwnerFibreExecution.totalTime key ((P.rows bits).map SemiprimeD1FactorScopePairEncoding.pair)+1)=
      5*(pairTape bits).length+SemiprimeD1StackOwnerFibreExecution.totalTime key
        ((P.rows bits).map SemiprimeD1FactorScopePairEncoding.pair)+5 by omega] using h
/-- Actual prepared entry includes its final physical halt, clearing finite flags. -/
theorem prepared_run (bits key : List Bool) :
    C.run program (preparedTime bits key+1) ⟨some .copy,none,none,afterSource bits key,[]⟩=some (done bits key) := by
  obtain ⟨finish,hr,hAt⟩:=prepared_trace bits key []
    (⟨some .copy,none,none,afterSource bits key,[]⟩ : C.State Stack Label) ⟨rfl,rfl,rfl⟩
  have he:=halt_run program .done rfl (result bits key) [] finish hAt
  rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,he]
  rfl
/-- Complete source allowance keeps the same source clock and every new call. -/
def timeBound (bits key : List Bool) : Nat :=SemiprimeD1StackFactorScopePairBounds.runBound bits+preparedTime bits key+2
/-- Binary N plus an actually acquired factor key produce the exact scope-ID vector. -/
theorem source_run (bits key : List Bool) (hb : bits≠[]) :
    ∃t≤timeBound bits key,C.run program t (initial bits key)=some (done bits key) := by
  obtain ⟨a,ha,h0⟩:=source_call bits key hb
  have h:=runs_trans program _ _ _ _ _ _ _ _ h0 (prepared_trace bits key)
  obtain ⟨finish,hr,hAt⟩:=h [] (initial bits key) ⟨rfl,rfl,rfl⟩
  have he:=halt_run program .done rfl (result bits key) [] finish hAt
  refine ⟨((a+1)+preparedTime bits key)+1,by unfold timeBound;omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,he]
  rfl
/-- Original binary N and complete acquired pair catalogue remain literally retained. -/
theorem retained_source (bits key : List Bool) (k : P.Stack) : result bits key (sourceStack k)=P.result bits k := rfl
/-- Current actual physical factor key remains available to the caller. -/
theorem retained_query (bits key : List Bool) : result bits key query=key :=rfl
/-- Every original factor obtains precisely its old ordered occurrence scope, including empty scopes. -/
theorem original_output (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<SemiprimeBitArithmetic.bitValue bits)
    (f : Fin (SemiprimePublicAcquiredExecution.factorCount (SemiprimeBitArithmetic.bitValue bits))) :
    result bits (SemiprimeD1FactorScopePairOriginal.key f.val) output=
      SemiprimeD1TensorTapeCodec.vectorBits
        (((SemiprimeD1RootTensorTables.factorNode (SemiprimeBitArithmetic.bitValue bits) hN f).ports).map
          (SemiprimeD1StackOwnerFibreOriginal.scopeWord (SemiprimeBitArithmetic.bitValue bits))) := by
  change SemiprimeD1TensorTapeCodec.vectorBits (F.values _ _)=_
  rw [SemiprimeD1FactorScopePairOriginal.original_fibre bits hc hN f]
end RiemannGaussian.SemiprimeD1StackFactorScopeFibreExecution
