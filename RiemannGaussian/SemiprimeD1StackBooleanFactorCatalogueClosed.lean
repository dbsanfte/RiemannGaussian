/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueBounds
import RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueOriginal
/-! # Closed original-N Boolean factor records, own clock and complete storage
This component acquires all ten original Boolean vertex families. It does not
assert acquisition of arithmetic rows or the whole recursive factoring query.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueClosed
open SemiprimeD1StackBooleanFactorCatalogue SemiprimeD1StackBooleanFactorCatalogueExecution
open SemiprimeD1StackBooleanFactorCatalogueOriginal
open SemiprimeBitArithmetic (bitValue)
/-- Same actual source run and exact original records, under a uniform clock
in original binary N bitlength. Every acquisition and output instruction is included. -/
theorem source_original (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t ≤ 10^170*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^40,
      C.run program t (initial bits)=some (done bits) ∧
      (done bits).data output=SemiprimeD1StackVertexProduct.records
        (booleanVertices (bitValue bits) hN (SemiprimeD1BooleanFactorCatalogueIndices.indices (bitValue bits))) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackBooleanFactorCatalogueBounds.source_run_polynomial bits hc hN
  have hw:=SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc
  refine ⟨t,?_,hr,final_output bits hc hN⟩
  simpa only [SemiprimeD1StackBooleanFactorCatalogueBounds.runBound,hw] using ht
/-- Genuine finite-machine certificate from canonical binary N ONLY with the
same complete polynomial clock; no supplier or retained-report clock is transported. -/
noncomputable def machineOriginal (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits)))
      (10^170*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^40) := by
  have h:=SemiprimeD1StackBooleanFactorCatalogueBounds.machineBounded bits hc hN
  have hw:=SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc
  simpa only [SemiprimeD1StackBooleanFactorCatalogueBounds.runBound,hw] using h
/-- Every one of218 physical Boolean roles and every real return cell is
bounded at every compiled original-input prefix by the same own clock. -/
theorem original_prefix_cells (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel : Nat) (cfg : machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      219*(SemiprimeMacroParameters.bitLength (bitValue bits)+
        10^170*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^40) := by
  have h:=SemiprimeD1StackBooleanFactorCatalogueBounds.polynomial_machine_prefix_cells bits hc hN fuel cfg hr
  have hw:=SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc
  simpa only [SemiprimeD1StackBooleanFactorCatalogueBounds.runBound,hw] using h
/-- Each actual compiled transition uses at most four fundamental commands;
all control/data/return alphabets are fixed finite types before original N. -/
theorem compile_depth (pc : Label) : SemiprimeD1StackBytecode.statementDepth (machine.m pc) ≤ 4 :=
  SemiprimeD1StackCalls.compile_depth (.local .main : Label) (program pc)
end RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueClosed
