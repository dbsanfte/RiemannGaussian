/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootRecursiveControlBounds

/-! # Exact original root branch and child schedule from binary N alone
One actual finite program acquires the root operands and executes the guard
and conditional successor. The original root network is covered for every
fixed prefix. Recursive phases and factor recovery remain caller obligations.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackRootRecursiveControlOriginal
open SemiprimeD1StackRootRecursiveControl SemiprimeD1StackRootRecursiveControlEncoding
open SemiprimeD1StackRootRecursiveControlExecution SemiprimeD1StackRootRecursiveControlBounds
open SemiprimeBitArithmetic (bitValue)
namespace GO
export SemiprimeD1StackRecursiveScheduleOriginal
  (verdict_original child_levels_original child_exponent_original)
end GO
/-- Every one of the108 acquired original source roles is retained literally. -/
theorem source_preserved (bits:List Bool) (k:P.Stack) : result bits (sourceStack k)=P.result bits k := rfl
/-- The same original binary N survives both calls and the conditional branch. -/
theorem input_preserved (bits:List Bool) : result bits originalInput=bits :=
  SemiprimeD1StackRootParametersOriginal.input_preserved bits
/-- Actual physical root verdict agrees with the original recursive counter. -/
theorem verdict_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    result bits output=[SemiprimeD1RecursiveCounter.activeTest
      (scaleValue bits) (lambdaValue bits) 0 (edgeValue bits)] := by
  exact (result_projection bits hc (.inl .output)).trans
    (GO.verdict_original (scaleValue bits) (lambdaValue bits) 0 (edgeValue bits))
/-- The actual conditional child valuation count is computed, or remains empty. -/
theorem child_levels_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    result bits nextLevels=(if SemiprimeD1RecursiveCounter.activeTest
      (scaleValue bits) (lambdaValue bits) 0 (edgeValue bits) then
        List.replicate (SemiprimeD1Schedule.levels (lambdaValue bits) 1) true else []) := by
  exact (result_projection bits hc (.inr .nextLevels)).trans
    (GO.child_levels_original (scaleValue bits) (lambdaValue bits) 0 (edgeValue bits))
/-- The actual conditional child cumulative exponent is computed, or remains empty. -/
theorem child_exponent_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    result bits nextExponent=(if SemiprimeD1RecursiveCounter.activeTest
      (scaleValue bits) (lambdaValue bits) 0 (edgeValue bits) then
        List.replicate (SemiprimeD1Schedule.exponent (lambdaValue bits) 1) true else []) := by
  exact (result_projection bits hc (.inr .nextExponent)).trans
    (GO.child_exponent_original (scaleValue bits) (lambdaValue bits) 0 (edgeValue bits))
/-- The acquired M equals the original incidence count at every prescribed fixed prefix. -/
theorem edgeValue_original (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :
    edgeValue bits=SemiprimeD1TensorNetwork.edgeCount
      (SemiprimeD1RootStateResources.root (bitValue bits) hN fixed) :=
  SemiprimeD1StackRootScopeBankOriginal.occurrence_count bits hN fixed
/-- Every original prescribed root prefix has exactly the acquired physical branch bit. -/
theorem verdict_all_prefixes (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :
    result bits output=[SemiprimeD1RecursiveCounter.activeTest (scaleValue bits) (lambdaValue bits) 0
      (SemiprimeD1TensorNetwork.edgeCount (SemiprimeD1RootStateResources.root (bitValue bits) hN fixed))] := by
  exact (verdict_original bits hc).trans (congrArg
    (fun M=>[SemiprimeD1RecursiveCounter.activeTest (scaleValue bits) (lambdaValue bits) 0 M])
      (edgeValue_original bits hN fixed))
/-- Conditional child levels agree for every original prescribed root prefix. -/
theorem child_levels_all_prefixes (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :
    result bits nextLevels=(if SemiprimeD1RecursiveCounter.activeTest (scaleValue bits) (lambdaValue bits) 0
      (SemiprimeD1TensorNetwork.edgeCount (SemiprimeD1RootStateResources.root (bitValue bits) hN fixed)) then
        List.replicate (SemiprimeD1Schedule.levels (lambdaValue bits) 1) true else []) := by
  exact (child_levels_original bits hc).trans (congrArg
    (fun M=>if SemiprimeD1RecursiveCounter.activeTest (scaleValue bits) (lambdaValue bits) 0 M then
      List.replicate (SemiprimeD1Schedule.levels (lambdaValue bits) 1) true else [])
      (edgeValue_original bits hN fixed))
/-- Conditional child exponents agree for every original prescribed root prefix. -/
theorem child_exponent_all_prefixes (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :
    result bits nextExponent=(if SemiprimeD1RecursiveCounter.activeTest (scaleValue bits) (lambdaValue bits) 0
      (SemiprimeD1TensorNetwork.edgeCount (SemiprimeD1RootStateResources.root (bitValue bits) hN fixed)) then
        List.replicate (SemiprimeD1Schedule.exponent (lambdaValue bits) 1) true else []) := by
  exact (child_exponent_original bits hc).trans (congrArg
    (fun M=>if SemiprimeD1RecursiveCounter.activeTest (scaleValue bits) (lambdaValue bits) 0 M then
      List.replicate (SemiprimeD1Schedule.exponent (lambdaValue bits) 1) true else [])
      (edgeValue_original bits hN fixed))
/-- One actual original-input run contains acquisition, branch, conditional schedule and real halt. -/
theorem source_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t≤10^55*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^10,
      SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) ∧
      (∀fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool),
        result bits output=[SemiprimeD1RecursiveCounter.activeTest (scaleValue bits) (lambdaValue bits) 0
          (SemiprimeD1TensorNetwork.edgeCount (SemiprimeD1RootStateResources.root (bitValue bits) hN fixed))]) ∧
      result bits nextLevels=(if SemiprimeD1RecursiveCounter.activeTest
        (scaleValue bits) (lambdaValue bits) 0 (edgeValue bits) then
          List.replicate (SemiprimeD1Schedule.levels (lambdaValue bits) 1) true else []) ∧
      result bits nextExponent=(if SemiprimeD1RecursiveCounter.activeTest
        (scaleValue bits) (lambdaValue bits) 0 (edgeValue bits) then
          List.replicate (SemiprimeD1Schedule.exponent (lambdaValue bits) 1) true else []) ∧
      result bits originalInput=bits := by
  obtain ⟨t,ht,hr⟩:=source_run_polynomial bits hc hN
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  refine ⟨t,?_,hr,verdict_all_prefixes bits hc hN,child_levels_original bits hc,
    child_exponent_original bits hc,input_preserved bits⟩
  simpa only [hw] using ht
/-- Genuine finite-machine certificate with the same complete original-input polynomial clock. -/
noncomputable def originalInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits)))
      (10^55*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^10) := by
  have h:=controlInTime bits hc hN
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  simpa only [hw] using h
/-- Every original-input prefix includes all119 data roles and all actual return cells. -/
theorem original_prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      10^58*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^10 := by
  have h:=(machine_prefix_cells bits hc hN fuel cfg hr).trans (polynomial_space bits hc hN)
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  simpa only [hw] using h
end RiemannGaussian.SemiprimeD1StackRootRecursiveControlOriginal
