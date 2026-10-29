/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankResources
import RiemannGaussian.SemiprimeD1StackCachePhaseBankOriginalRows
import RiemannGaussian.SemiprimeD1StackCachePhaseBankSemanticCaps
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateOriginal
/-! # Complete actual issued-phase bank and exact original coordinate-consumer bytes
The source consumes ONLY four actual words. Root345's actual chronological
reference vector determines every call; functions below name already supplied
child bytes in proofs, and are not runtime operands. Recursive child production
and a literal N-only producer/iterator join remain upstream OPEN.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankOriginal
open SemiprimeD1StackCachePhaseBank SemiprimeD1StackCachePhaseBankEncoding
open SemiprimeD1StackCachePhaseBankOriginalRows SemiprimeD1StackCachePhaseBankBounds
open SemiprimeD1StackCachePhaseBankInputBounds
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackJetFoldWords (Modes modeTape)
namespace F
export SemiprimeD1StackFreshBankRestoreOriginal (output_references producer_lineage banks reference root_issued)
end F
namespace Root
export SemiprimeD1StackRootPhaseFreshRecords (output program initial)
export SemiprimeD1StackRootPhaseFreshRecordsEncoding (done)
export SemiprimeD1StackRootPhaseFreshRecordsExecution (runBound)
end Root
attribute [local irreducible] SemiprimeD1StackRootPhaseFreshRecordsEncoding.result
  SemiprimeD1StackRootPhaseParametersEncoding.phases
/-- Every original chronological phase is visited exactly once, including rejected/empty phases.
Rows denote actual nested child words in proofs only; runtime sees their encoded vector. -/
def chronological (bits:List Bool)
    (rows:Fin (SemiprimeD1StackRootPhaseParametersEncoding.phases bits).length→Modes):List (Request bits):=
  List.ofFn (fun i=>(i,rows i))
/-- The loop input is the ENTIRE physically produced issued-reference output, not an advised permutation. -/
theorem references_original (bits:List Bool)
    (rows:Fin (SemiprimeD1StackRootPhaseParametersEncoding.phases bits).length→Modes):
    references bits (chronological bits rows)=R.result bits Root.output:=by
  rw [F.output_references]
  simp only [references,chronological,List.map_ofFn]
  rfl
/-- Actual per-phase recursive answer byte input, without a supplied cache answer. -/
def childInput (bits:List Bool)
    (rows:Fin (SemiprimeD1StackRootPhaseParametersEncoding.phases bits).length→Modes):List Bool:=
  vectorBits (List.ofFn (fun i=>modeTape (rows i)))
/-- Exact chronological children encoding, keeping rejected phase occurrences as well. -/
theorem children_original (bits:List Bool)
    (rows:Fin (SemiprimeD1StackRootPhaseParametersEncoding.phases bits).length→Modes):
    children (chronological bits rows)=childInput bits rows:=by
  simp only [children,chronological,childInput,List.map_ofFn]
  rfl
/-- The actual full iterator starts from the reached heap/counter/output-ref words and actual child bytes ONLY. -/
def prepared (bits:List Bool)
    (rows:Fin (SemiprimeD1StackRootPhaseParametersEncoding.phases bits).length→Modes):C.State Stack Label:=
  initial (R.result bits R.heap) (R.result bits (R.aux .counter)) (R.result bits Root.output) (childInput bits rows)
/-- Four literal word equalities establish the complete initial state before original arithmetic is instantiated. -/
theorem source_actual (bits:List Bool)
    (rows:Fin (SemiprimeD1StackRootPhaseParametersEncoding.phases bits).length→Modes):
    source bits (chronological bits rows)=prepared bits rows:=by
  unfold source prepared
  rw [references_original,children_original]
/-- Actual original phase count; no phase-count operand or termination oracle enters the program. -/
theorem chronological_count (bits:List Bool)
    (rows:Fin (SemiprimeD1StackRootPhaseParametersEncoding.phases bits).length→Modes):
    (chronological bits rows).length=(SemiprimeD1StackRootPhaseParametersEncoding.phases bits).length:=
  List.length_ofFn
/-- Whole actual iterator produces exact native ascending block bytes for EVERY original issued phase. -/
theorem source_original (bits:List Bool)
    (rows:Fin (SemiprimeD1StackRootPhaseParametersEncoding.phases bits).length→Modes):
    ∃t ≤runBound bits (chronological bits rows),
      SemiprimeD1StackCalls.run program t (prepared bits rows)=some (done bits (chronological bits rows)) ∧
      (done bits (chronological bits rows)).data output=Col.originalTape (phases bits (chronological bits rows)):=by
  obtain ⟨t,ht,hr⟩:=source_run_bounded bits (chronological bits rows)
  rw [source_actual] at hr
  exact ⟨t,ht,hr,original_tape bits (chronological bits rows)⟩
/-- Genuine original allocator lineage and SAME actual source clocks, without calling a pair of sources one machine. -/
theorem producer_and_bank (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<SemiprimeBitArithmetic.bitValue bits)
    (rows:Fin (SemiprimeD1StackRootPhaseParametersEncoding.phases bits).length→Modes):
    ∃p ≤Root.runBound bits,∃t ≤runBound bits (chronological bits rows),
      SemiprimeD1StackCalls.run Root.program p (Root.initial bits)=some (Root.done bits) ∧
      SemiprimeD1StackHeapReadBounds.History
        (SemiprimeD1StackFreshBankRestoreExecution.records (F.banks bits))
        (R.result bits R.heap) (R.result bits (R.aux .counter)) ∧
      (∀i:Fin (SemiprimeD1StackRootPhaseParametersEncoding.phases bits).length,
        SemiprimeD1StackHeapReadBounds.Issued
          (SemiprimeD1StackFreshBankRestoreExecution.records (F.banks bits)) (F.reference bits i)) ∧
      SemiprimeD1StackCalls.run program t (prepared bits rows)=some (done bits (chronological bits rows)) ∧
      (done bits (chronological bits rows)).data output=Col.originalTape (phases bits (chronological bits rows)):=by
  obtain ⟨p,hp,hr,hh,_href,hi⟩:=F.producer_lineage bits hc hN
  obtain ⟨t,ht,he,ho⟩:=source_original bits rows
  exact ⟨p,hp,t,ht,hr,hh,hi,he,ho⟩
/-- Exact old coordinate-cache bytes of the acquired ACTUAL phase blocks, including rejected rows and EOF defaults. -/
theorem coordinate_identity (bits:List Bool) (requests:List (Request bits)) (key:List Bool):
    SemiprimeD1StackRecoveryCoordinateEncoding.result (requests.map (blocks bits)) key=
      SemiprimeD1StackRecoveryEntriesEncoding.childTape
        (SemiprimeD1PhysicalRecursiveCounter.coordinateCache
          (SemiprimeD1RecursiveCounter.coordinate (phases bits requests) (SemiprimeBitArithmetic.bitValue key))):=by
  have h:=SemiprimeD1StackRecoveryCoordinateOriginalRows.result_original (phases bits requests) key
  have hv:SemiprimeD1StackRecoveryCoordinateOriginalRows.originalPhases (phases bits requests)=requests.map (blocks bits):=by
    unfold SemiprimeD1StackRecoveryCoordinateOriginalRows.originalPhases phases
    simp only [List.map_map,Function.comp_def]
    rfl
  rw [hv] at h
  exact h
/-- Uniform fixed coefficient/degree precede all prepared four-word source instances. -/
theorem uniform_source:∃coef degree:Nat,∀(bits:List Bool) (requests:List (Request bits)),
    ∃t ≤coef*(resource bits requests+2)^degree,
      SemiprimeD1StackCalls.run program t (source bits requests)=some (done bits requests):=by
  exact ⟨10^100,18,source_run_bounded⟩
end RiemannGaussian.SemiprimeD1StackCachePhaseBankOriginal
