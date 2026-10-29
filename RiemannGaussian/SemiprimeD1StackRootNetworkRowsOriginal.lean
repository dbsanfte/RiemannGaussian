/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootNetworkRowsResources
/-! # Whole original binary N acquires exact original rows and n/F/M
One actual source and one actual clock acquire all data from N alone.
The caller-prefix entry covers every physical prescription/tail; all old
records, tables and the full owner index remain physically retained.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootNetworkRowsOriginal
open SemiprimeD1StackRootNetworkRows SemiprimeD1StackRootNetworkRowsComponents
open SemiprimeD1StackRootNetworkRowsExecution
open SemiprimeBitArithmetic (bitValue)
namespace Enc
export SemiprimeD1StackNetworkRowsEncoding (originalTape)
end Enc
namespace Original
export SemiprimeD1StackNetworkRowsOriginal (originalDone output_original left_count factor_count occurrence_count)
end Original
/-- Actual retained unary n output address, shared with the acquired original index. -/
def leftCount :Stack :=rowsStack (.inl .leftCount)
/-- Actual physically tallied F output address, including zero-port factors. -/
def factorCount :Stack :=rowsStack (SemiprimeD1StackNetworkRows.aux .factors)
/-- Actual physically tallied M output address, preserving every repeated owner occurrence. -/
def occurrenceCount :Stack :=rowsStack (SemiprimeD1StackNetworkRows.aux .occurrences)
/-- Every shared index and new row operand has the SAMEactual final row-source projection. -/
theorem rows_preserved (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) (k:Q.Stack) :
    (done bits hN fixed tail).data (rowsStack k)=(rowsDone bits hN fixed).data k :=by
  apply data_rows
  intro j
  exact SemiprimeD1StackRootOwnerIndexOriginal.index_preserved bits hc hN fixed tail j
/-- Exact literal old factor-major/local-slot owner rows, including empty factors and repeated owners. -/
theorem output_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    (done bits hN fixed tail).data output=Enc.originalTape (A.net bits hN fixed) :=by
  rw [show output=rowsStack (SemiprimeD1StackNetworkRows.aux .output) from rfl,rows_preserved bits hc hN fixed tail]
  exact Original.output_original (A.net bits hN fixed)
    (SemiprimeD1StackRootOwnerIndexOriginal.original_wellFormed bits hN fixed)
/-- Original n is acquired from N, never supplied as a runtime count answer. -/
theorem left_count (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    (done bits hN fixed tail).data leftCount=List.replicate (A.net bits hN fixed).leftCount true :=by
  rw [leftCount,rows_preserved bits hc hN fixed tail]
  exact Original.left_count (A.net bits hN fixed)
/-- Actual F counts every original factor, including every empty row. -/
theorem factor_count (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    (done bits hN fixed tail).data factorCount=List.replicate (A.net bits hN fixed).rows.length true :=by
  rw [factorCount,rows_preserved bits hc hN fixed tail]
  exact Original.factor_count (A.net bits hN fixed)
/-- Actual M counts every original local occurrence; equal owner values remain distinct occurrences. -/
theorem occurrence_count (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    (done bits hN fixed tail).data occurrenceCount=List.replicate (A.net bits hN fixed).rows.flatten.length true :=by
  rw [occurrenceCount,rows_preserved bits hc hN fixed tail]
  exact Original.occurrence_count (A.net bits hN fixed)
    (SemiprimeD1StackRootOwnerIndexOriginal.original_wellFormed bits hN fixed)
/-- A single original-N execution acquires the exact original rows and every physical n/F/M word. -/
theorem source_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃q≤SemiprimeD1StackRootNetworkRowsBounds.runBound bits,
      SemiprimeD1StackCalls.run program q (initial bits)=some (done bits hN [] []) ∧
      (done bits hN [] []).data output=Enc.originalTape (A.net bits hN []) ∧
      (done bits hN [] []).data leftCount=List.replicate (A.net bits hN []).leftCount true ∧
      (done bits hN [] []).data factorCount=List.replicate (A.net bits hN []).rows.length true ∧
      (done bits hN [] []).data occurrenceCount=List.replicate (A.net bits hN []).rows.flatten.length true :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackRootNetworkRowsBounds.source_run_bounded bits hc hN
  exact ⟨q,hq,hr,output_original bits hc hN [] [],left_count bits hc hN [] [],
    factor_count bits hc hN [] [],occurrence_count bits hc hN [] []⟩
/-- Fixed coefficient and degree precede ALL original canonical N, for this SAMEactual acquired-row source and clock. -/
theorem uniform_original :∃coef degree:Nat,∀(bits:List Bool)
    (_hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits),
    ∃q≤coef*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^degree*
      2^(57*SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength (bitValue bits))),
      SemiprimeD1StackCalls.run program q (initial bits)=some (done bits hN [] []) ∧
      (done bits hN [] []).data output=Enc.originalTape (A.net bits hN []) :=by
  obtain ⟨coef,degree,hs⟩:=SemiprimeD1StackRootNetworkRowsResources.source_run_monomial
  refine ⟨coef,degree,?_⟩
  intro bits hc hN
  obtain ⟨q,hq,hr⟩:=hs bits hc hN
  have hw:=SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc
  refine ⟨q,?_,hr,output_original bits hc hN [] []⟩
  simpa only [SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity,hw] using hq
/-- Exact original-N-only machine certificate starts at genuine Turing.initList. -/
noncomputable def machineOriginal (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits hN [] [])))
      (SemiprimeD1StackRootNetworkRowsBounds.runBound bits) :=
  SemiprimeD1StackRootNetworkRowsResources.networkRowsInTime bits hc hN
end RiemannGaussian.SemiprimeD1StackRootNetworkRowsOriginal
