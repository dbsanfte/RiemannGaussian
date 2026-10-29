/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootSourceOccurrencesResources
/-! # Exact original-binary-N compact occurrence-key source
All row/count/key acquisition occurs on the actual path. One same-program clock
pays preprocessing, all copies/parsers/normalizers/counters/logs and real returns.
Fixed monomial witnesses precede the whole family of original canonical inputs.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootSourceOccurrencesOriginal
open SemiprimeD1StackRootSourceOccurrences SemiprimeD1StackRootSourceOccurrencesComponents
open SemiprimeD1StackRootSourceOccurrencesExecution
open SemiprimeBitArithmetic (bitValue)
namespace O
export SemiprimeD1StackSourceOccurrencesOriginal (originalPairsFrom output_original factor_count occurrence_count)
end O
/-- Generic actual final-source projection is proved before instantiating any original arithmetic graph. -/
theorem final_projection (root:R.Stack→List Bool) (n:Nat) (rows:List (List (List Bool)))
    (hr:root R.output=Enc.inputTape rows) (hn:root A.leftCount=List.replicate n true) (k:Q.Stack) :
    data root (E.done n rows).data (occurrenceStack k)=(E.done n rows).data k :=by
  exact data_occurrence root (E.done n rows).data hr hn k
/-- Every actual mapped occurrence role has its identical physical source result, including both shared inputs. -/
theorem occurrence_preserved (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) (k:Q.Stack) :
    (done bits hN fixed tail).data (occurrenceStack k)=(occurrenceDone bits hN fixed).data k :=by
  exact final_projection (R.done bits hN fixed tail).data (rootn bits hN fixed) (rootrows bits hN fixed)
    (root_output bits hc hN fixed tail) (root_number bits hc hN fixed tail) k
/-- Entire exact original factor-major/local-slot compact owner/factor-key stream is acquired from N alone. -/
theorem output_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    (done bits hN fixed tail).data output=SemiprimeD1StackOwnerLookup.records
      (O.originalPairsFrom (G.net bits hN fixed).leftCount 0 (G.net bits hN fixed).rows) [] :=by
  rw [show output=occurrenceStack .output from rfl,occurrence_preserved bits hc hN fixed tail]
  exact O.output_original (G.net bits hN fixed)
/-- Every original factor, including an empty one, is physically counted during the acquired row prescan. -/
theorem factor_count (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    (done bits hN fixed tail).data (occurrenceStack .factors)=List.replicate (G.net bits hN fixed).rows.length true :=by
  rw [occurrence_preserved bits hc hN fixed tail]
  exact O.factor_count (G.net bits hN fixed)
/-- Every original local occurrence pushes its own marker, retaining repeated owner values. -/
theorem occurrence_count (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    (done bits hN fixed tail).data (occurrenceStack .occurrences)=List.replicate (G.net bits hN fixed).rows.flatten.length true :=by
  rw [occurrence_preserved bits hc hN fixed tail]
  exact O.occurrence_count (G.net bits hN fixed)
/-- One actual original-N execution returns exact original occurrence keys, F and M under its own complete bound. -/
theorem source_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃q≤SemiprimeD1StackRootSourceOccurrencesBounds.runBound bits,
      SemiprimeD1StackCalls.run program q (initial bits)=some (done bits hN [] []) ∧
      (done bits hN [] []).data output=SemiprimeD1StackOwnerLookup.records
        (O.originalPairsFrom (G.net bits hN []).leftCount 0 (G.net bits hN []).rows) [] ∧
      (done bits hN [] []).data (occurrenceStack .factors)=List.replicate (G.net bits hN []).rows.length true ∧
      (done bits hN [] []).data (occurrenceStack .occurrences)=List.replicate (G.net bits hN []).rows.flatten.length true :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackRootSourceOccurrencesBounds.source_run_bounded bits hc hN
  exact ⟨q,hq,hr,output_original bits hc hN [] [],factor_count bits hc hN [] [],occurrence_count bits hc hN [] []⟩
/-- Fixed coefficient/degree precede ALLcanonicalN for this SAMEliteral complete occurrence source and clock. -/
theorem uniform_original :∃coef degree:Nat,∀(bits:List Bool)
    (_hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits),
    ∃q≤coef*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^degree*
      2^(114*SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength (bitValue bits))),
      SemiprimeD1StackCalls.run program q (initial bits)=some (done bits hN [] []) ∧
      (done bits hN [] []).data output=SemiprimeD1StackOwnerLookup.records
        (O.originalPairsFrom (G.net bits hN []).leftCount 0 (G.net bits hN []).rows) [] :=by
  obtain ⟨coef,degree,hs⟩:=SemiprimeD1StackRootSourceOccurrencesResources.source_run_monomial
  refine ⟨coef,degree,?_⟩
  intro bits hc hN
  obtain ⟨q,hq,hr⟩:=hs bits hc hN
  have hw:=SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc
  refine ⟨q,?_,hr,output_original bits hc hN [] []⟩
  simpa only [SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity,hw] using hq
/-- Genuine finite-machine certificate starts at true Turing.initList on binary N alone. -/
noncomputable def machineOriginal (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits hN [] [])))
      (SemiprimeD1StackRootSourceOccurrencesBounds.runBound bits) :=
  SemiprimeD1StackRootSourceOccurrencesResources.occurrencesInTime bits hc hN
end RiemannGaussian.SemiprimeD1StackRootSourceOccurrencesOriginal
