/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootInputResources
/-! # Actual marked original root input with original2ell context and all caches
One fixed program starts from original binary N alone and acquires the NEW
weighted records and actual precision header, retaining every original packet,
placement, width and shadow. Physical contraction/current-node recursion and
factor recovery remain separate joins; old table-bearing data stays old data.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedRootInputOriginal
open scoped BigOperators
open SemiprimeD1StackPackedRootInput SemiprimeD1StackPackedRootInputEncoding
open SemiprimeD1StackPackedRootInputBounds SemiprimeD1StackPackedRootInputResources
open SemiprimeBitArithmetic (bitValue)
/-- Actual NEW complete owner-first marked network, with every local table and port unchanged in order. -/
theorem output_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    (done bits hN).data output=SemiprimeD1StackVertexProduct.records
      (SemiprimeD1TensorNetwork.vertices (SemiprimeD1StackMarkedRootRecordsNetwork.network (bitValue bits) hN)) :=
  SemiprimeD1StackMarkedRootRecordsNetwork.output_original bits hc hN
/-- Actual new context inputs retain the empty-axis terminator and physically computed binary precision. -/
theorem context_inputs (bits : List Bool) (hN : 0<bitValue bits) :
    (done bits hN).data (contextStack (J.context SemiprimeD1StackJetContext.axesCache))=[false] ∧
      (done bits hN).data (contextStack (J.context SemiprimeD1StackJetContext.precisionBits))=
        SemiprimeD1StackPackedRootMetadataEncoding.precisionWord bits.length :=
  SemiprimeD1StackPackedRootContextOriginal.context_inputs bits
/-- Mathematical decoder of the actual acquired header, never a runtime supplier. -/
def acquiredContext (bits : List Bool) (hN : 0<bitValue bits) : SemiprimeD1JetAxes.Context :=
  ⟨[],bitValue ((done bits hN).data (contextStack (J.context SemiprimeD1StackJetContext.precisionBits)))⟩
/-- The same actual original N determines the new precision internally. -/
theorem context_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    acquiredContext bits hN=⟨[],SemiprimeD1PackedMomentPrecision.precision (bitValue bits)⟩ :=
  SemiprimeD1StackPackedRootContextOriginal.context_original bits hc
/-- The rank remains the actual one TRUE marker at the root. -/
theorem rank_original (bits : List Bool) (hN : 0<bitValue bits) : (done bits hN).data rank=[true] :=
  SemiprimeD1StackPackedRootContextOriginal.rank_word bits
/-- Actual context width is TRUE2ell; the rational FALSE template remains a separate physical word. -/
theorem width_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    (done bits hN).data width=List.replicate (SemiprimeD1PackedMomentPrecision.precision (bitValue bits)) true :=
  SemiprimeD1StackPackedRootContextOriginal.width_original bits hc
/-- The rational-grid width is retained from its actual a/M source, independently of tensor precision. -/
theorem rational_width_original (bits : List Bool) (hN : 0<bitValue bits) :
    (done bits hN).data rationalWidth=List.replicate
      (SemiprimeD1RecoveryNodeBits.width (SemiprimeD1StackRecoveryWidthOriginal.originalA bits)
        (SemiprimeD1StackRecoveryWidthOriginal.originalM bits)) false :=
  SemiprimeD1StackRootPacketInventoryExecution.template_retained bits hN
/-- Original binary N remains physically present after all actual calls. -/
theorem retained_N (bits : List Bool) (hN : 0<bitValue bits) : (done bits hN).data originalInput=bits :=
  SemiprimeD1PackedRootRetained.retained_N bits hN
/-- Every actual original cache word is retained literally; no old coefficient is reinterpreted. -/
theorem all_root_retained (bits : List Bool) (hN : 0<bitValue bits) (k : R.Stack) :
    (done bits hN).data (rootStack k)=(SemiprimeD1StackRootPacketInventoryEncoding.done bits hN).data k := rfl
/-- SAME complete fixed source acquires marked rows and the actual matching context from N alone. -/
theorem source_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    ∃t ≤ runBound bits,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits hN) ∧
      (done bits hN).data output=SemiprimeD1StackVertexProduct.records
        (SemiprimeD1TensorNetwork.vertices (SemiprimeD1StackMarkedRootRecordsNetwork.network (bitValue bits) hN)) ∧
      acquiredContext bits hN=⟨[],SemiprimeD1PackedMomentPrecision.precision (bitValue bits)⟩ ∧
      (done bits hN).data originalInput=bits := by
  obtain ⟨t,ht,hr⟩:=source_run_bounded bits hc hN
  exact ⟨t,ht,hr,output_original bits hc hN,context_original bits hc hN,retained_N bits hN⟩
/-- One fixed coefficient and degree precede EVERY canonical positive input and the SAME complete source. -/
theorem uniform_original : ∃A d : ℕ,∀(bits : List Bool)
    (_hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits),
    ∃t ≤ A*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^d*
      2^(114000*SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength (bitValue bits))),
      SemiprimeD1StackCalls.run program t (initial bits)=some (done bits hN) ∧
      (done bits hN).data output=SemiprimeD1StackVertexProduct.records
        (SemiprimeD1TensorNetwork.vertices (SemiprimeD1StackMarkedRootRecordsNetwork.network (bitValue bits) hN)) ∧
      acquiredContext bits hN=⟨[],SemiprimeD1PackedMomentPrecision.precision (bitValue bits)⟩ := by
  obtain ⟨a,d,ha⟩:=runBound_monomial
  refine ⟨a,d,?_⟩
  intro bits hc hN
  obtain ⟨t,ht,hr,ho,hctx,_⟩:=source_original bits hc hN
  have hb:=ht.trans (ha bits)
  rw [SemiprimeD1CanonicalInput.compact_length bits hc] at hb
  exact ⟨t,hb,hr,ho,hctx⟩
/-- Genuine Turing.initList certificate for the SAME full original-input source. -/
noncomputable def machineOriginal (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits hN))) (runBound bits) :=
  SemiprimeD1StackPackedRootInputStorage.machineSource bits hc hN
/-- All2505 data allocations and real return cells satisfy one whole-family bound at EVERY prefix. -/
theorem uniform_prefix_cells : ∃A d : ℕ,∀(bits : List Bool)
    (_hc : SemiprimeSourceCompactBits.Compact bits) (_hN : 0<bitValue bits) (fuel : ℕ) (cfg : machine.Cfg),
    (fun q => q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg→
      (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
        A*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^d*
          2^(114000*SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength (bitValue bits))) := by
  obtain ⟨a,d,ha⟩:=cells_cap_monomial
  refine ⟨a,d,?_⟩
  intro bits hc hN fuel cfg hr
  have h:=(SemiprimeD1StackPackedRootInputStorage.machine_prefix_cells bits hc hN fuel cfg hr).trans (ha bits)
  rw [SemiprimeD1CanonicalInput.compact_length bits hc] at h
  exact h
end RiemannGaussian.SemiprimeD1StackPackedRootInputOriginal
