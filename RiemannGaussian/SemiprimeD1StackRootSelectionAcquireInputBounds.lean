/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootSelectionAcquireEncoding
/-! # Every selection operand is paid by the actual original-input producers
The row/count/dimension word bounds come from the SAME actual producer runs.
The complete alphabet cardinality is bounded by the exact original schedule.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootSelectionAcquireInputBounds
open SemiprimeD1StackRootSelectionAcquire SemiprimeD1StackRootSelectionAcquireEncoding
open SemiprimeBitArithmetic (bitValue)
namespace B
export SemiprimeD1StackSourceSelectionAcquireBounds (inputSize polynomial)
end B
/-- Actual complete parameter-source allowance in only the original binary input length. -/
def parameterBound (bits:List Bool) :Nat :=10^51*(bits.length+1)^10
/-- Only paid original-input bytes and actual whole-source clock allowances form this envelope. -/
def envelope (bits:List Bool) :Nat :=
  bits.length+SemiprimeD1StackRootNetworkRowsBounds.runBound bits+parameterBound bits+1
/-- The physical envelope is nonzero and pays each actual producer allowance. -/
theorem envelope_parts (bits:List Bool) :
    1 ≤envelope bits ∧ bits.length ≤envelope bits ∧
      SemiprimeD1StackRootNetworkRowsBounds.runBound bits ≤envelope bits ∧ parameterBound bits ≤envelope bits :=by
  unfold envelope
  omega
/-- Each actual row-source result word is paid by its SAME actual source trace. -/
theorem root_word_bound (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0 < bitValue bits) (k:R.Stack) :((rootDone bits hN).data k).length ≤envelope bits :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackRootNetworkRowsBounds.source_run_bounded bits hc hN
  have h:=SemiprimeD1StackReturnLink.run_data_bound R.program t bits.length _ _
    (SemiprimeD1StackRootNetworkRowsResources.initial_length bits) hr k
  change ((rootDone bits hN).data k).length ≤bits.length+t at h
  unfold envelope
  omega
/-- Each actual parameter result word is paid by its SAME actual source trace. -/
theorem parameter_word_bound (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0 < bitValue bits) (k:P.Stack) :((parameterDone bits).data k).length ≤envelope bits :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackRootParametersBounds.source_run_polynomial bits hc hN
  have h:=SemiprimeD1StackReturnLink.run_data_bound P.program t bits.length _ _
    (SemiprimeD1StackRootParametersBounds.initial_role_bound bits) hr k
  change ((parameterDone bits).data k).length ≤bits.length+t at h
  unfold envelope parameterBound
  omega
/-- The actual original root alphabet cardinality is paid by the fixed original-input parameter allowance. -/
theorem alphabet_bound (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    64^(dimension bits) ≤parameterBound bits :=by
  have h:=SemiprimeD1StackRootSelectionAcquireRate.alphabet_le (bitValue bits)
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  rw [←hw] at h
  have hp:(bits.length+1)^6 ≤(bits.length+1)^10:=Nat.pow_le_pow_right (by omega) (by decide)
  change 64^(dimension bits) ≤10^42*(bits.length+1)^6 at h
  exact h.trans (Nat.mul_le_mul (by norm_num: (10^42:Nat) ≤10^51) hp)
/-- All row/count/dimension bytes and every genuinely enumerated alphabet entry are paid. -/
theorem selection_input_bound (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0 < bitValue bits) :B.inputSize (net bits hN) (dimension bits) ≤5*envelope bits :=by
  have hrows:(SemiprimeD1StackSourceOccurrencesEncoding.inputTape
      (SemiprimeD1StackSourceOccurrencesEncoding.originalRows (net bits hN))).length ≤envelope bits:=by
    have hr:(rootDone bits hN).data R.output=
        SemiprimeD1StackSourceOccurrencesEncoding.inputTape
          (SemiprimeD1StackSourceOccurrencesEncoding.originalRows (net bits hN)):=
      (SemiprimeD1StackRootNetworkRowsOriginal.output_original bits hc hN [] []).trans
        (SemiprimeD1StackSourceOccurrencesEncoding.original_input (net bits hN)).symm
    rw [←hr]
    exact root_word_bound bits hc hN R.output
  have hn:=root_word_bound bits hc hN R.leftCount
  have hnw:(rootDone bits hN).data R.leftCount=List.replicate (net bits hN).leftCount true:=
    SemiprimeD1StackRootNetworkRowsOriginal.left_count bits hc hN [] []
  rw [hnw,List.length_replicate] at hn
  have ha:=parameter_word_bound bits hc hN P.exponent
  have haw:(parameterDone bits).data P.exponent=List.replicate (dimension bits) true:=
    SemiprimeD1StackRootParametersOriginal.exponent_original bits hc
  rw [haw,List.length_replicate] at ha
  change dimension bits ≤envelope bits at ha
  have hl:64^(dimension bits) ≤envelope bits:=(alphabet_bound bits hc).trans (envelope_parts bits).2.2.2
  have hpos:1 ≤envelope bits:=(envelope_parts bits).1
  change (SemiprimeD1StackSourceOccurrencesEncoding.inputTape
    (SemiprimeD1StackSourceOccurrencesEncoding.originalRows (net bits hN))).length+
      (net bits hN).leftCount+dimension bits+64^(dimension bits)+1 ≤5*envelope bits
  omega
/-- The actual three-copy handoff has only the already paid producer-word lengths as costs. -/
theorem acquisition_copy_bound (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0 < bitValue bits) :
    SemiprimeD1StackRootSelectionAcquireInput.acquisitionCopyTime (rootDone bits hN).data (parameterDone bits).data ≤
      27*envelope bits :=by
  have h0:=root_word_bound bits hc hN R.output
  have h1:=root_word_bound bits hc hN R.leftCount
  have h2:=parameter_word_bound bits hc hN P.exponent
  have hpos:1 ≤envelope bits:=(envelope_parts bits).1
  unfold SemiprimeD1StackRootSelectionAcquireInput.acquisitionCopyTime
  omega
end RiemannGaussian.SemiprimeD1StackRootSelectionAcquireInputBounds
