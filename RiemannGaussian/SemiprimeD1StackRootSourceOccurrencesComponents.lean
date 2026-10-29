/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootSourceOccurrences
/-! # Two actual acquired row/count aliases feed the real compact-key source
All original graph/count/row/owner expressions are pure specifications of the
already executed source. No graph, count, routing or key answer is an operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootSourceOccurrencesComponents
open SemiprimeD1StackRootSourceOccurrences SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
namespace E
export SemiprimeD1StackSourceOccurrencesExecution (source done timeBound)
end E
namespace Enc
export SemiprimeD1StackSourceOccurrencesEncoding (inputTape originalRows original_input)
end Enc
namespace G
export SemiprimeD1StackRootOwnerIndexComponents (net)
end G
local notation "ctl" => (Sum.inl :Control→Label)
/-- Exact original acquired n, as a proof-side specification of the actual retained count word. -/
def rootn (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :Nat :=(G.net bits hN fixed).leftCount
/-- Actual original binary-owner row lists, never a source/runtime argument. -/
def rootrows (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :List (List (List Bool)) :=
  Enc.originalRows (G.net bits hN fixed)
/-- Exact actual occurrence source before any marker/counter/key acquisition. -/
def occurrenceSource (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :C.State Q.Stack Q.Label :=
  E.source (rootn bits hN fixed) (rootrows bits hN fixed)
/-- Exact actual completed occurrence bank, with both source words retained and every work word clear. -/
def occurrenceDone (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :C.State Q.Stack Q.Label :=
  E.done (rootn bits hN fixed) (rootrows bits hN fixed)
/-- Every old source word and every actual private occurrence word are physically present at the whole source halt. -/
def result (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :Stack→List Bool :=
  data (R.done bits hN fixed tail).data (occurrenceDone bits hN fixed).data
/-- Every mapped row/count/private occurrence operand has its exact source projection. -/
theorem data_occurrence (root:R.Stack→List Bool) (out:Q.Stack→List Bool)
    (hr:root R.output=out .rows) (hn:root A.leftCount=out .number) (k:Q.Stack) :
    data root out (occurrenceStack k)=out k :=by
  cases k
  · exact hr
  · exact hn
  all_goals rfl
/-- The actual root row output supplies the literal physically acquired key-source row input. -/
theorem root_output (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    (R.done bits hN fixed tail).data R.output=Enc.inputTape (rootrows bits hN fixed) :=by
  change _=Enc.inputTape (Enc.originalRows (G.net bits hN fixed))
  rw [Enc.original_input]
  exact SemiprimeD1StackRootNetworkRowsOriginal.output_original bits hc hN fixed tail
/-- Actual n is already acquired by the root, never supplied by an input-dependent getter. -/
theorem root_number (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    (R.done bits hN fixed tail).data A.leftCount=List.replicate (rootn bits hN fixed) true :=
  SemiprimeD1StackRootNetworkRowsOriginal.left_count bits hc hN fixed tail
/-- Either literal original-input source entry runs inside this same caller, with private key words empty. -/
theorem root_lift (entry:R.Label) (pc:Control)
    (hc:program (ctl pc)=.call (rootLabel entry) (ctl .occurrences))
    (before after:C.State R.Stack R.Label) (q:Nat)
    (he:before.pc=some entry) (hs:after.pc=none) (hb:before.frames=[]) (ha:after.frames=[])
    (hr:SemiprimeD1StackCalls.run R.program q before=some after) :
    Runs program (q+1) (ctl pc) (data before.data (fun _=>[])) (ctl .occurrences) (data after.data (fun _=>[])) :=by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program rootStack rootLabel Sum.inl_injective
    R.program entry (fun _=>rfl) (ctl pc) (ctl .occurrences) hc q before after _ _ he hb hs ha hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- The real occurrence acquisition is justified by the two ACTUALretained source words alone. -/
theorem occurrence_lift (root:R.Stack→List Bool) (n:Nat) (rows:List (List (List Bool)))
    (hr:root R.output=Enc.inputTape rows) (hn:root A.leftCount=List.replicate n true) :
    ∃q≤E.timeBound n rows,Runs program (q+1) (ctl .occurrences) (data root (fun _=>[])) (ctl .done)
      (data root (E.done n rows).data) :=by
  obtain ⟨q,hq,h0⟩:=SemiprimeD1StackSourceOccurrencesExecution.source_run n rows
  refine ⟨q,hq,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program occurrenceStack occurrenceLabel occurrence_injective
    Q.program (.local .start) (fun _=>rfl) (ctl .occurrences) (ctl .done) rfl q
    (E.source n rows) (E.done n rows) _ _ rfl rfl rfl rfl h0
  · constructor
    · intro k;cases k
      · exact hr
      · exact hn
      all_goals rfl
    · intro k _;rfl
  · constructor
    · intro k
      exact data_occurrence root (E.done n rows).data hr hn k
    · intro k hk
      rcases k with k|k
      · rfl
      · cases k
        · rfl
        · rfl
        · exact (hk .reader rfl).elim
        · exact (hk .row rfl).elim
        · exact (hk .word rfl).elim
        · exact (hk .todo rfl).elim
        · exact (hk .counter rfl).elim
        · exact (hk .next rfl).elim
        · exact (hk .incrementScratch rfl).elim
        · exact (hk .ownerKey rfl).elim
        · exact (hk .factorKey rfl).elim
        · exact (hk .fieldScratch rfl).elim
        · exact (hk .valid rfl).elim
        · exact (hk .copyScratch rfl).elim
        · exact (hk .normScratch rfl).elim
        · exact (hk .frameBuffer rfl).elim
        · exact (hk .frameScratch rfl).elim
        · exact (hk .history rfl).elim
        · exact (hk .output rfl).elim
        · exact (hk .factors rfl).elim
        · exact (hk .occurrences rfl).elim
/-- Whole original-prefix root result enters the real key source through its physically shared row/count words. -/
theorem occurrence_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    ∃q≤E.timeBound (rootn bits hN fixed) (rootrows bits hN fixed),
      Runs program (q+1) (ctl .occurrences) (data (R.done bits hN fixed tail).data (fun _=>[])) (ctl .done)
        (result bits hN fixed tail) :=by
  exact occurrence_lift _ _ _ (root_output bits hc hN fixed tail) (root_number bits hc hN fixed tail)
end RiemannGaussian.SemiprimeD1StackRootSourceOccurrencesComponents
