/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFullFactorCatalogueResources
/-! # Closed original-N full factor records, same own clock and all prefix storage
All original arithmetic and Boolean factor vertices are acquired in their old
order. This source component does not assert the full recursive factoring goal.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackFullFactorCatalogueClosed
open SemiprimeD1StackFullFactorCatalogue SemiprimeD1StackFullFactorCatalogueExecution
open SemiprimeD1StackFullFactorCatalogueOriginal SemiprimeD1StackFullFactorCatalogueBounds
open SemiprimeBitArithmetic (bitValue)
/-- SAME complete actual N-only source trace and exact old records for ALL original factors. -/
theorem source_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t ≤ runBound bits,C.run program t (initial bits)=some (done bits) ∧
      (done bits).data output=SemiprimeD1StackVertexProduct.records
        (factorVertices (bitValue bits) hN (SemiprimeD1BooleanFactorCatalogueIndices.indices (bitValue bits))):=by
  obtain ⟨t,ht,hr⟩:=source_run_bounded bits hc hN
  exact ⟨t,ht,hr,final_output bits hc hN⟩
/-- One coefficient and degree, fixed before N, bound the same exact original source trace. -/
theorem uniform_original :∃A d:Nat,∀(bits:List Bool)
    (_hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits),
    ∃t ≤ A*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^d*
      2^(19*SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength (bitValue bits))),
      C.run program t (initial bits)=some (done bits) ∧
      (done bits).data output=SemiprimeD1StackVertexProduct.records
        (factorVertices (bitValue bits) hN (SemiprimeD1BooleanFactorCatalogueIndices.indices (bitValue bits))):=by
  obtain ⟨A,d,ha⟩:=SemiprimeD1StackFullFactorCatalogueResources.source_run_monomial
  refine ⟨A,d,?_⟩
  intro bits hc hN
  obtain ⟨t,ht,hr⟩:=ha bits hc hN
  have hw:=SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc
  refine ⟨t,?_,hr,final_output bits hc hN⟩
  simpa only [SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity,hw] using ht
/-- Actual complete finite-machine acquisition from original canonical binary N alone. -/
noncomputable def machineOriginal (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (runBound bits):=
  SemiprimeD1StackFullFactorCatalogueResources.machineBounded bits hc hN
/-- All1454 real Boolean data roles and all actual return cells are charged at every compiled prefix. -/
theorem original_prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 1455*(bits.length+runBound bits):=
  SemiprimeD1StackFullFactorCatalogueResources.machine_prefix_cells bits hc hN fuel cfg hr
end RiemannGaussian.SemiprimeD1StackFullFactorCatalogueClosed
