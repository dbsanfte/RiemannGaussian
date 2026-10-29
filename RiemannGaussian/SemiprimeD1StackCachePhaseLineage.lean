/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseRootOriginal
/-! # Actual original producer, issued reference and complete consumer together
These are two actual source executions with both own clocks retained. Their
eventual original-input recursive controller and child acquisition remain
separate work; no pair of programs is mislabeled a completed factoring machine.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseLineage
open SemiprimeD1StackCachePhase
open SemiprimeD1StackCachePhaseRootOriginal (rootSource rootDone rootSize)
open SemiprimeD1StackJetFoldWords (Modes)
/-- The SAMEactual N-only producer issues the input bytes consumed by the full cache/fold/block source. -/
theorem producer_and_consumer (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0 < SemiprimeBitArithmetic.bitValue bits)
    (i:Fin (SemiprimeD1StackRootPhaseParametersEncoding.phases bits).length) (modes:Modes) :
    ∃producerSteps ≤ SemiprimeD1StackRootPhaseFreshRecordsExecution.runBound bits,
      ∃consumerSteps ≤ 10^80*(rootSize bits i modes+1)^16,
      SemiprimeD1StackCalls.run SemiprimeD1StackRootPhaseFreshRecords.program producerSteps
        (SemiprimeD1StackRootPhaseFreshRecords.initial bits)=
          some (SemiprimeD1StackRootPhaseFreshRecordsEncoding.done bits) ∧
      SemiprimeD1StackHeapReadBounds.History
        (SemiprimeD1StackFreshBankRestoreExecution.records (SemiprimeD1StackFreshBankRestoreOriginal.banks bits))
        (SemiprimeD1StackRootPhaseFreshRecordsEncoding.result bits SemiprimeD1StackRootPhaseFreshRecords.heap)
        (SemiprimeD1StackRootPhaseFreshRecordsEncoding.result bits (SemiprimeD1StackRootPhaseFreshRecords.aux .counter)) ∧
      SemiprimeD1StackHeapReadBounds.Issued
        (SemiprimeD1StackFreshBankRestoreExecution.records (SemiprimeD1StackFreshBankRestoreOriginal.banks bits))
        (SemiprimeD1StackFreshBankRestoreOriginal.reference bits i) ∧
      SemiprimeD1StackCalls.run program consumerSteps (rootSource bits i modes)=some (rootDone bits i modes) :=by
  obtain ⟨producerSteps,hp,hproducer,hhistory,_hrefs,hissued⟩:=
    SemiprimeD1StackFreshBankRestoreOriginal.producer_lineage bits hc hN
  obtain ⟨consumerSteps,hc,hconsumer⟩:=SemiprimeD1StackCachePhaseRootOriginal.root_source_run bits i modes
  exact ⟨producerSteps,hp,consumerSteps,hc,hproducer,hhistory,hissued i,hconsumer⟩
end RiemannGaussian.SemiprimeD1StackCachePhaseLineage
