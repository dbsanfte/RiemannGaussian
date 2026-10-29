/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootParametersBounds

/-! # Every original root scheduling operand from the one actual binary input
There is no prepared count, log, square root, level, exponent or leaf answer.
The same executed program acquires all of them and retains the entire source.
This does not yet execute the original recursive phases or factor recovery.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackRootParametersOriginal
open SemiprimeD1StackRootParameters SemiprimeD1StackRootParametersExecution
open SemiprimeD1StackRootParametersBounds
open SemiprimeBitArithmetic (bitValue)
namespace MO
export SemiprimeD1StackRootControllerMetadataOriginal
  (input_preserved edges_original lambda_original levels_original exponent_original minimum_original)
end MO
namespace LO
export SemiprimeD1StackRootScaleLeafOriginal (scale_original_word root_original_word leaf_original_word)
end LO
namespace O
export SemiprimeD1StackRootScheduleOriginal (originalLambda)
end O
/-- Every one of the98 already acquired original source/metadata roles is retained literally. -/
theorem metadata_preserved (bits:List Bool) (k:M.Stack) : result bits (metadataStack k)=M.result bits k := rfl
/-- The same original binary N is retained through the entire acquisition. -/
theorem input_preserved (bits:List Bool) : result bits originalInput=bits := MO.input_preserved bits
/-- The actual occurrence count is the original root edge count for every fixed prefix. -/
theorem edges_original (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :
    result bits edges=List.replicate (SemiprimeD1TensorNetwork.edgeCount
      (SemiprimeD1RootStateResources.root (bitValue bits) hN fixed)) true := by
  unfold edges
  exact (metadata_preserved bits M.edges).trans (MO.edges_original bits hN fixed)
/-- Exact original logarithm, computed before threshold acquisition and retained afterward. -/
theorem lambda_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    result bits lambda=List.replicate (O.originalLambda (bitValue bits)) true := MO.lambda_original bits hc
/-- Actual original root dyadic level counter. -/
theorem levels_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    result bits levels=List.replicate (SemiprimeD1Schedule.levels (O.originalLambda (bitValue bits)) 0) true :=
  MO.levels_original bits hc
/-- Actual original root cumulative exponent. -/
theorem exponent_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    result bits exponent=List.replicate (SemiprimeD1Schedule.exponent (O.originalLambda (bitValue bits)) 0) true :=
  MO.exponent_original bits hc
/-- Exact physically acquired original minimum-level guard. -/
theorem minimum_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    result bits minimum=List.replicate (SemiprimeD1PrecisionEnvelope.minimumLevels
      (O.originalLambda (bitValue bits))) true := MO.minimum_original bits hc
/-- Twenty actual doublings acquire the original scale, with no supplied scale value. -/
theorem scale_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    result bits scale=List.replicate (SemiprimeD1PublicPackingReady.scale
      (SemiprimeMacroParameters.bitLength (bitValue bits))) true := by
  change result bits (leafStack (L.aux .scale))=_
  rw [result_projection]
  exact LO.scale_original_word bits hc
/-- The actual odd-block subtraction computes the exact original floor square root. -/
theorem squareRoot_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    result bits squareRoot=List.replicate (Nat.sqrt (O.originalLambda (bitValue bits))) true := by
  change result bits (leafStack (L.aux .root))=_
  rw [result_projection]
  exact LO.root_original_word bits hc
/-- The same actual program acquires the precise original leaf guard by real division. -/
theorem leaf_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    result bits leaf=List.replicate (SemiprimeD1Schedule.leafSize
      (SemiprimeD1PublicPackingReady.scale (SemiprimeMacroParameters.bitLength (bitValue bits)))
      (O.originalLambda (bitValue bits))) true := by
  change result bits (leafStack (L.aux .leaf))=_
  rw [result_projection]
  exact LO.leaf_original_word bits hc
/-- One full actual original-input run and every original root-guard operand hold together. -/
theorem source_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t≤10^51*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^10,
      SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) ∧
      (∀fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool),
        result bits edges=List.replicate (SemiprimeD1TensorNetwork.edgeCount
          (SemiprimeD1RootStateResources.root (bitValue bits) hN fixed)) true) ∧
      result bits levels=List.replicate (SemiprimeD1Schedule.levels (O.originalLambda (bitValue bits)) 0) true ∧
      result bits exponent=List.replicate (SemiprimeD1Schedule.exponent (O.originalLambda (bitValue bits)) 0) true ∧
      result bits minimum=List.replicate (SemiprimeD1PrecisionEnvelope.minimumLevels (O.originalLambda (bitValue bits))) true ∧
      result bits leaf=List.replicate (SemiprimeD1Schedule.leafSize
        (SemiprimeD1PublicPackingReady.scale (SemiprimeMacroParameters.bitLength (bitValue bits)))
        (O.originalLambda (bitValue bits))) true ∧ result bits originalInput=bits := by
  obtain ⟨t,ht,hr⟩:=source_run_polynomial bits hc hN
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  refine ⟨t,?_,hr,edges_original bits hN,levels_original bits hc,exponent_original bits hc,
    minimum_original bits hc,leaf_original bits hc,input_preserved bits⟩
  simpa only [hw] using ht
/-- Genuine original-N machine execution with the same complete polynomial bound. -/
noncomputable def originalInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits)))
      (10^51*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^10) := by
  have h:=acquireInTime bits hc hN
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  simpa only [hw] using h
/-- Every original-input prefix includes all108 data roles and all actual return cells. -/
theorem original_prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      10^54*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^10 := by
  have h:=(machine_prefix_cells bits hc hN fuel cfg hr).trans (polynomial_space bits)
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  simpa only [hw] using h
end RiemannGaussian.SemiprimeD1StackRootParametersOriginal
