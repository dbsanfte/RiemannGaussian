/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootScopeBank
import RiemannGaussian.SemiprimeD1StackOrdinalBankLoop
import RiemannGaussian.SemiprimeD1StackProcedureInclusion
/-! # N-only scope acquisition and reusable already-counted ordinal stage -/
set_option autoImplicit false
set_option synthInstance.maxSize 131072
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
namespace RiemannGaussian.SemiprimeD1StackRootScopeBankExecution
open SemiprimeD1StackRootScopeBank
open SemiprimeD1StackProcedureTrace (Runs runs_trans)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeBitArithmetic (bitValue)

/-- Proof-side exact original edge records of the ACTUAL acquired tape. -/
def records (bits : List Bool) : List SemiprimeD1StackEdgeCount.Record :=
  (SemiprimePublicAcquiredExecution.edgeEnumeration (bitValue bits)).values.map SemiprimeD1StackEdgeCount.edgeFields
/-- Original Boolean wire count, never identified with D1 occurrence count. -/
def wireValue (bits : List Bool) : ℕ := (records bits).length
/-- Canonical D1 occurrence cardinality; runtime obtains this by TWO real pushes per edge. -/
def occurrenceCount (bits : List Bool) : ℕ := 2*wireValue bits
/-- Actual private count-cache data; the aliased bank role is unused/empty. -/
def countData (bits : List Bool) : D.Stack→List Bool :=
  SemiprimeD1StackEdgeCount.data [] [] (List.replicate (occurrenceCount bits) true) [] [] []
    (List.replicate (wireValue bits) true)
/-- Actual private ordinal data; the aliased tally role remains unused/empty. -/
def bankData (M : ℕ) : O.Stack→List Bool :=
  SemiprimeD1StackOrdinalBank.data [] [] [] [] (vectorBits (SemiprimeD1OrdinalBankSpec.words M)) [] [] [] []
/-- Exact final data preserve the WHOLE acquired original source and both real tallies. -/
def result (bits : List Bool) : Stack→List Bool :=
  data (SemiprimeD1StackEdgeCatalogueExecution.result bits) (countData bits) (bankData (occurrenceCount bits))
/-- Canonical stopped producer state. -/
def done (bits : List Bool) : SemiprimeD1StackCalls.State Stack Label := ⟨none,none,none,result bits,[]⟩
/-- Stage budget retaining actual source, six-field count and M-controlled loop. -/
def budget (bits : List Bool) : ℕ :=
  (1000000000000000000*(bits.length+1)^5+1)+
    (15*(SemiprimeD1StackEdgeCount.tape (records bits) []).length+7)+
    (1000*(occurrenceCount bits+1)^2+1)+1

/-- Actual reusable ready entry after source/count caches ALREADY exist. Its
only width/loop source is the physical count cache, with every foreign cache
preserved. It does not reexecute Edge13 or the six-field scan. -/
theorem buildIds_run (source : E.Stack→List Bool) (counts : D.Stack→List Bool) :
    ∃ m≤1000*((counts .count).length+1)^2+1,
      Runs program m (.inl .buildIds) (data source counts (fun _=>[])) (.inl .done)
        (data source counts (bankData (counts .count).length)) := by
  obtain ⟨m,hm,hr⟩:=SemiprimeD1StackOrdinalBankLoop.source_run (counts .count)
  refine ⟨m+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program ordinalStack ordinalLabel ordinalStack_injective
    O.program (.inl .start) (fun _=>rfl) (.inl .buildIds) (.inl .done) rfl m
    (SemiprimeD1StackOrdinalBank.initial (counts .count))
    (SemiprimeD1StackOrdinalBankLoop.done (counts .count))
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k
      rcases k with k|k <;> cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k
      rcases k with k|k <;> cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · rcases k with k|k
          · cases k with
            | word => rfl
            | scratch => rfl
            | next => rfl
            | history => rfl
            | output => exact False.elim (hk O.ids rfl)
          · cases k <;> rfl

/-- Actual closed N-only root scope producer. No M/E/cardinality/ID/width/cost
is supplied; canonical original bits only identify the original typed graph. -/
theorem source_run (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) :
    ∃ m≤budget bits,SemiprimeD1StackCalls.run program m (initial bits)=some (done bits) := by
  have hb : bits≠[] := by intro he; subst bits; simp [SemiprimeBitArithmetic.bitValue] at hN
  let source:=SemiprimeD1StackEdgeCatalogueExecution.result bits
  let cs:=countData bits
  have htape : source (E.aux .output)=SemiprimeD1StackEdgeCount.tape (records bits) [] := by
    dsimp only [records]
    rw [SemiprimeD1StackEdgeCount.original_tape]
    exact SemiprimeD1StackEdgeCatalogueExecution.original_edges bits hc hN
  obtain ⟨me,hme,he⟩:=SemiprimeD1StackEdgeCatalogueBounds.source_run_polynomial bits hb
  have h0 : Runs program (me+1) (.inl .start) (input bits) (.inl .countTape)
      (data source (fun _=>[]) (fun _=>[])) := by
    apply SemiprimeD1StackProcedureInclusion.included_call program edgeStack edgeLabel edgeStack_injective
      E.program (.inl .main) (fun _=>rfl) (.inl .start) (.inl .countTape) rfl me
      (SemiprimeD1StackEdgeCatalogue.initial bits) (SemiprimeD1StackEdgeCatalogueExecution.done bits)
    · rfl
    · rfl
    · rfl
    · rfl
    · exact he
    · constructor
      · intro k; rfl
      · intro k hk; rfl
    · constructor
      · intro k; rfl
      · intro k hk
        rcases k with k|k
        · exact False.elim (hk k rfl)
        · rfl
  have h1 : Runs program (SemiprimeD1StackEdgeCountLoop.totalTime (records bits)+1)
      (.inl .countTape) (data source (fun _=>[]) (fun _=>[])) (.inl .buildIds)
      (data source cs (fun _=>[])) := by
    apply SemiprimeD1StackProcedureInclusion.included_call program countStack countLabel countStack_injective
      D.program (.inl .start) (fun _=>rfl) (.inl .countTape) (.inl .buildIds) rfl _
      (SemiprimeD1StackEdgeCount.initial (SemiprimeD1StackEdgeCount.tape (records bits) []))
      (SemiprimeD1StackEdgeCount.done (SemiprimeD1StackEdgeCount.tape (records bits) []) (records bits).length)
    · rfl
    · rfl
    · rfl
    · rfl
    · exact SemiprimeD1StackEdgeCountLoop.source_run (records bits)
    · constructor
      · intro k
        cases k
        · exact htape
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
      · intro k hk; rfl
    · constructor
      · intro k
        cases k
        · exact htape
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
      · intro k hk
        rcases k with k|k
        · rfl
        · rcases k with k|k
          · cases k with
            | bank => rfl
            | reader => rfl
            | count => exact False.elim (hk .count rfl)
            | word => rfl
            | fieldScratch => rfl
            | valid => rfl
            | copyScratch => exact False.elim (hk .copyScratch rfl)
          · rfl
  obtain ⟨mb,hmb,h2⟩:=buildIds_run source cs
  have hmb' : mb≤1000*(occurrenceCount bits+1)^2+1 := by
    simpa [cs,countData,SemiprimeD1StackDigitCount.data] using hmb
  have hh:=runs_trans program _ _ _ _ _ _ _ _ h0 h1
  have hh:=runs_trans program _ _ _ _ _ _ _ _ hh h2
  obtain ⟨finish,hfinish,hAt⟩:=hh [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hd : data source cs (bankData (cs .count).length)=result bits := by
    simp [source,cs,countData,SemiprimeD1StackDigitCount.data,result]
  rw [hd] at hAt
  have hhalt:=SemiprimeD1StackProcedureTrace.halt_run program (.inl .done) rfl _ [] finish hAt
  refine ⟨(me+1)+(SemiprimeD1StackEdgeCountLoop.totalTime (records bits)+1)+mb+1,?_,?_⟩
  · have hcount:=SemiprimeD1StackEdgeCountLoop.totalTime_le (records bits)
    unfold budget
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hhalt]
    rfl

/-- Actual returned vector, byte-for-byte; no supplied word-bank answer. -/
theorem result_ids (bits : List Bool) : result bits ids=vectorBits (SemiprimeD1OrdinalBankSpec.words (occurrenceCount bits)) := rfl
/-- Both real acquired counts remain in their declared physical output roles. -/
theorem result_counts (bits : List Bool) :
    result bits count=List.replicate (occurrenceCount bits) true ∧
      result bits wireCount=List.replicate (wireValue bits) true := ⟨rfl,rfl⟩
/-- Entire upstream source/cache state is retained literally by actual later stages. -/
theorem result_source (bits : List Bool) (k : E.Stack) :
    result bits (edgeStack k)=SemiprimeD1StackEdgeCatalogueExecution.result bits k := rfl

end RiemannGaussian.SemiprimeD1StackRootScopeBankExecution
