/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootSelectionAcquireCalls
import RiemannGaussian.SemiprimeD1StackRootSelectionAcquireInput
import RiemannGaussian.SemiprimeD1StackRootSelectionAcquireRate
/-! # Exact original-N interpretation of the physically acquired source banks
All graphs, dimensions and stopped states below describe physical runs.
The actual source accepts only binary N and computes every derived byte.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootSelectionAcquireEncoding
open SemiprimeD1StackRootSelectionAcquire SemiprimeD1StackRootSelectionAcquireInput
open SemiprimeBitArithmetic (bitValue)
namespace E
export SemiprimeD1StackSourceSelectionAcquireEncoding (source done)
export SemiprimeD1StackSourceSelectionAcquireBounds (polynomial)
end E
/-- Original typed root is a proof interpretation of the actually acquired records/rows. -/
def net (bits:List Bool) (hN:0 < bitValue bits) :SemiprimeD1TensorNetwork.Network :=
  SemiprimeD1StackRootOwnerIndexComponents.net bits hN []
/-- Exact original root dimension; no dimension is supplied to runtime control. -/
def dimension (bits:List Bool) :Nat :=SemiprimeD1StackRootSelectionAcquireRate.originalDimension (bitValue bits)
/-- Actual whole original row source halt, including every retained record/cache word. -/
def rootDone (bits:List Bool) (hN:0 < bitValue bits) :C.State R.Stack R.Label :=
  SemiprimeD1StackRootNetworkRowsExecution.done bits hN [] []
/-- Actual original parameter-source halt, including all108 words. -/
def parameterDone (bits:List Bool) :C.State P.Stack P.Label :=SemiprimeD1StackRootParametersExecution.done bits
/-- Entire actual selected-key source halt from those acquired original operands. -/
def acquisitionDone (bits:List Bool) (hN:0 < bitValue bits) :C.State Q.Stack Q.Label :=
  E.done (net bits hN) (dimension bits)
/-- All2114 actual words are physically retained at the whole original-input halt. -/
def result (bits:List Bool) (hN:0 < bitValue bits) :Stack→List Bool :=
  data (rootDone bits hN).data (parameterDone bits).data (acquisitionDone bits hN).data
/-- Exact full halt has clear flags and no outstanding actual component return. -/
def done (bits:List Bool) (hN:0 < bitValue bits) :C.State Stack Label :=⟨none,none,none,result bits hN,[]⟩
/-- Own whole clock includes all three actual sources, four copies, three calls and halt. -/
def timeBound (bits:List Bool) (hN:0 < bitValue bits) :Nat :=
  5*bits.length+10^51*(bits.length+1)^10+SemiprimeD1StackRootNetworkRowsBounds.runBound bits+
    acquisitionCopyTime (rootDone bits hN).data (parameterDone bits).data+
    E.polynomial (net bits hN) (dimension bits)+8
/-- The three actual stopped-producer words form the exact original acquired selection entry. -/
theorem acquisitionReady_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0 < bitValue bits) :
    acquisitionReady (rootDone bits hN).data (parameterDone bits).data=(E.source (net bits hN) (dimension bits)).data :=by
  rw [acquisitionReady_input]
  change SemiprimeD1StackSourceSelectionAcquire.input
    ((rootDone bits hN).data R.output) ((rootDone bits hN).data R.leftCount)
      ((parameterDone bits).data P.exponent)=_
  have hr:(rootDone bits hN).data R.output=SemiprimeD1StackNetworkRowsEncoding.originalTape (net bits hN):=
    SemiprimeD1StackRootNetworkRowsOriginal.output_original bits hc hN [] []
  have hn:(rootDone bits hN).data R.leftCount=List.replicate (net bits hN).leftCount true:=
    SemiprimeD1StackRootNetworkRowsOriginal.left_count bits hc hN [] []
  have ha:(parameterDone bits).data P.exponent=List.replicate (dimension bits) true:=
    SemiprimeD1StackRootParametersOriginal.exponent_original bits hc
  rw [hr,hn,ha]
  rw [←SemiprimeD1StackSourceOccurrencesEncoding.original_input]
  rfl
end RiemannGaussian.SemiprimeD1StackRootSelectionAcquireEncoding
