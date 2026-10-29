/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsTopology
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsResources
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsReady
/-! # Whole original-N marked tables and exact original topology on one actual source
All factor/owner table bytes are acquired by this literal2011-role program.
The old routing/selection topology is unchanged. A weighted contraction
counter/caller and final readout join remain separate physical obligations.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsOriginal
open SemiprimeD1StackMarkedRootRecords SemiprimeD1StackMarkedRootRecordsExecution
open SemiprimeD1StackMarkedRootRecordsBounds SemiprimeD1StackMarkedRootRecordsNetwork
open SemiprimeBitArithmetic (bitValue)
/-- ALL1804 actual old source words survive exactly, including old factor/owner streams and input caches. -/
theorem root_preserved (bits : List Bool) (hN : 0 < bitValue bits) (k : R.Stack) :
    (done bits hN).data (root k)=SemiprimeD1StackRootNetworkRecordsExecution.result bits hN [] [] k := rfl
/-- ALL53 fresh actual descriptor-source words remain acquired and retained. -/
theorem catalogue_preserved (bits : List Bool) (hN : 0 < bitValue bits) (k : V.Stack) :
    (done bits hN).data (catalogue k)=SemiprimeD1StackVertexCatalogueExecution.result bits k := rfl
/-- The allocated private shared-N shadow remains EMPTY and counted at the final halt. -/
theorem shadow_empty (bits : List Bool) (hN : 0 < bitValue bits) :
    (done bits hN).data (tablePrivate tableNumber)=[] := rfl
/-- Every mutable144-role table/template/cache/helper word is physically cleared after logging. -/
theorem table_clear (bits : List Bool) (hN : 0 < bitValue bits) (k : T.Stack) (hk : k≠tableNumber) :
    (done bits hN).data (tableStack k)=[] := by
  have h := SemiprimeD1StackMarkedRootRecordsRowView.view_table (retained bits hN)
    (SemiprimeD1StackVertexCatalogueExecution.result bits) bits {} {status := [true],output := outputTape bits hN} rfl k
  change (done bits hN).data (tableStack k)=_ at h
  rw [h]
  simp only [SemiprimeD1StackMarkedRootRecordsTableView.tableWords,hk,ite_false]
  split_ifs <;> rfl
/-- All local work words are empty apart from the acquired output and actual TRUE success singleton. -/
theorem local_result (bits : List Bool) (hN : 0 < bitValue bits) (k : Aux) :
    (done bits hN).data (aux k)=if k=.output then outputTape bits hN else if k=.status then [true] else [] := by
  cases k <;> rfl
/-- Every original finite marked factor coefficient is an exact NATURAL integer before products. -/
theorem coefficient_integer (N : Nat) (hN : 0 < N) (v : SemiprimePublicAcquiredExecution.PublicVertex N)
    (input : Fin (SemiprimeMacroGraph.subdividedArity v) → Bool) :
    (SemiprimeD1TensorTables.valueAt (New.reference N hN v) input).map bitValue=
      [SemiprimeD1PackedMomentPrecision.coefficient N hN v input] := by
  rw [SemiprimeD1StackMarkedPublicInputTableOriginal.reference_entry]
  change [bitValue (SemiprimeSourceHistogramPortKeys.encodeKey _).bits]=_
  rw [SemiprimeSourceHistogramPortKeys.encodeKey_value]
/-- The exact original marked network is intrinsically Good at NEW2ell precision. -/
theorem canonical_original (N : Nat) (hN : 0 < N) :
    SemiprimeD1TensorNetwork.Good ⟨[],SemiprimeD1PackedMomentPrecision.precision N⟩ (network N hN) :=
  SemiprimeD1StackMarkedRootRecordsTopology.good N hN
/-- The exact original marked network retains the actual original routing invariant. -/
theorem wellFormed_original (N : Nat) (hN : 0 < N) :
    SemiprimeD1TensorNetwork.WellFormed (network N hN) :=
  SemiprimeD1StackMarkedRootRecordsTopology.wellFormed N hN
/-- SAME actual original-N source and ENTIRE owner-first marked output. -/
theorem source_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits) :
    ∃ t ≤ runBound bits, C.run program t (initial bits)=some (done bits hN) ∧
      (done bits hN).data (aux .output)=SemiprimeD1StackVertexProduct.records
        (SemiprimeD1TensorNetwork.vertices (network (bitValue bits) hN)) := by
  obtain ⟨t,ht,hr⟩ := source_run_bounded bits hc hN
  exact ⟨t,ht,hr,output_original bits hc hN⟩
/-- One fixed pair of constants precedes all original N and the same actual full source executions. -/
theorem uniform_original : ∃ A d : Nat, ∀ (bits : List Bool)
    (_hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits),
    ∃ t ≤ A*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^d*
      2^(58*SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength (bitValue bits))),
      C.run program t (initial bits)=some (done bits hN) ∧
      (done bits hN).data (aux .output)=SemiprimeD1StackVertexProduct.records
        (SemiprimeD1TensorNetwork.vertices (network (bitValue bits) hN)) := by
  obtain ⟨A,d,h⟩ := SemiprimeD1StackMarkedRootRecordsResources.source_run_monomial
  refine ⟨A,d,?_⟩
  intro bits hc hN
  obtain ⟨t,ht,hr⟩ := h bits hc hN
  have hw := SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc
  refine ⟨t,?_,hr,output_original bits hc hN⟩
  simpa only [scopeCap,hw] using ht
/-- The honest SAME acquired-root-cache entry produces exactly the same whole marked network without root replay. -/
theorem ready_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits) :
    ∃ t ≤ readyBound bits hN, C.run program t (ready bits hN)=some (done bits hN) ∧
      (done bits hN).data (aux .output)=SemiprimeD1StackVertexProduct.records
        (SemiprimeD1TensorNetwork.vertices (network (bitValue bits) hN)) := by
  obtain ⟨t,ht,hr⟩ := ready_run bits hc hN
  exact ⟨t,ht,hr,output_original bits hc hN⟩
/-- Genuine Turing.initList machine certificate with the SAME own source budget. -/
noncomputable def machineOriginal (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits hN))) (runBound bits) :=
  SemiprimeD1StackMarkedRootRecordsResources.machineSource bits hc hN
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsOriginal
