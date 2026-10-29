/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseGridBounds
/-! # Exact chronological original phase indices from the actual N-only source
This catalogue acquires the original binary t words. Executing phase bodies,
recursive child networks and coefficient recovery remains later caller work.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseGridOriginal
open SemiprimeD1StackRootPhaseGrid SemiprimeD1StackRootPhaseGridEncoding
open SemiprimeD1StackRootPhaseGridExecution SemiprimeD1StackRootPhaseGridBounds
open SemiprimeBitArithmetic (bitValue)
open SemiprimeD1StackAssignmentOrder (assignments)
/-- Every actually emitted active vector record is exactly the chronological wrapped word. -/
theorem grid_parsed (a:Nat) :
    (SemiprimeD1TensorTapeCodec.parseVector (grid a)).words=
      assignments (2^(a+1)) (List.replicate (a+1) false) :=by
  have h:=(SemiprimeD1TensorTapeCodec.parseVector_correct
    (assignments (2^(a+1)) (List.replicate (a+1) false)) []).1
  simpa only [grid,List.append_nil] using h
/-- Actual chronological binary values are EXACTLY the ascending original t range. -/
theorem grid_values (a:Nat) :
    ((SemiprimeD1TensorTapeCodec.parseVector (grid a)).words).map bitValue=List.range (2^(a+1)) :=by
  rw [grid_parsed,SemiprimeD1StackAssignmentOrder.assignments_values _ _
    (by rw [SemiprimeD1StackAssignmentOrder.zero_remaining])]
  rw [SemiprimeD1OrdinalBankSpec.zero_value,←List.range_eq_range']
/-- The actual binary catalogue has exactly the original wire-kernel grid size. -/
theorem grid_count (a:Nat) :
    (SemiprimeD1TensorTapeCodec.parseVector (grid a)).words.length=SemiprimeD1WireKernelOriginal.size a :=by
  rw [grid_parsed,SemiprimeD1StackAssignmentOrder.assignments_length]
  rfl
/-- Every actual phase word has the acquired a+1 fixed binary width. -/
theorem grid_word_width (a:Nat) (word:List Bool)
    (h:word∈(SemiprimeD1TensorTapeCodec.parseVector (grid a)).words) : word.length=a+1 :=by
  rw [grid_parsed] at h
  exact (SemiprimeD1StackAssignmentOrder.assignments_width _ _ word h).trans List.length_replicate
/-- Every original phase value occurs once, with no duplicates or permutation. -/
theorem grid_nodup (a:Nat) : (SemiprimeD1TensorTapeCodec.parseVector (grid a)).words.Nodup :=by
  rw [grid_parsed]
  exact SemiprimeD1StackAssignmentOrder.zero_nodup (a+1)
/-- Exact original exponent is the parent packet exponent, never the child exponent. -/
theorem exponent_original (bits:List Bool) : exponentValue bits=SemiprimeD1Schedule.exponent
    (SemiprimeD1PackingReady.logarithm (SemiprimeD1PublicPackingReady.scale
      (SemiprimeMacroParameters.bitLength (bitValue bits)))) 0 :=rfl
/-- The physically selected phase catalogue is empty on inactive calls. -/
theorem output_original (bits:List Bool) : result bits output=
    if active bits then grid (exponentValue bits) else [] :=rfl
/-- Inactive calls perform no phase enumeration and return no vector delimiter or word. -/
theorem output_inactive (bits:List Bool) (h:active bits=false) : result bits output=[] :=by
  rw [output_original,h]
  rfl
/-- Active calls return the entire actual binary phase vector in ascending value order. -/
theorem output_active_values (bits:List Bool) (h:active bits=true) :
    ((SemiprimeD1TensorTapeCodec.parseVector (result bits output)).words).map bitValue=
      List.range (SemiprimeD1WireKernelOriginal.size (exponentValue bits)) :=by
  rw [output_original,h]
  exact grid_values (exponentValue bits)
/-- All four enumerator work words are physically empty at the final halt on both branches. -/
theorem enum_work_clear (bits:List Bool) (k:A.Stack) (hk:k≠.output) : result bits (enumStack k)=[] :=by
  cases k with
  | word|scratch|next|history=>rfl
  | output=>exact (hk rfl).elim
/-- Both actual count/copy work words are physically empty at the final halt. -/
theorem aux_clear (bits:List Bool) (i:Fin 2) : result bits (aux i)=[] :=by fin_cases i <;> rfl
/-- This N-only catalogue uses the same physically acquired original root guard
for every fixed prefix; M remains2E, the actual incidence/occurrence domain. -/
theorem active_all_prefixes (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :
    active bits=SemiprimeD1RecursiveCounter.activeTest
      (SemiprimeD1StackRootRecursiveControlEncoding.scaleValue bits)
      (SemiprimeD1StackRootRecursiveControlEncoding.lambdaValue bits) 0
      (SemiprimeD1TensorNetwork.edgeCount (SemiprimeD1RootStateResources.root (bitValue bits) hN fixed)) :=by
  unfold active
  rw [SemiprimeD1StackRootRecursiveControlOriginal.edgeValue_original bits hN fixed]
/-- Complete actual original-N source run, exact conditional output, every119
retained root cell, and literal original binary N under one fixed own clock. -/
theorem source_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t≤10^60*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^10,
      SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) ∧
      result bits output=(if active bits then grid (exponentValue bits) else []) ∧
      (∀k:R.Stack,result bits (rootStack k)=R.result bits k) ∧ result bits originalInput=bits :=by
  obtain ⟨t,ht,hr⟩:=source_run_polynomial bits hc hN
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  refine ⟨t,?_,hr,output_original bits,root_preserved bits,input_preserved bits⟩
  simpa only [hw] using ht
/-- Genuine original-input finite-machine certificate retains the same complete own clock. -/
noncomputable def originalInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits)))
      (10^60*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^10) :=by
  have h:=gridInTime bits hc hN
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  simpa only [hw] using h
/-- Every actual original-input prefix pays all126 Boolean roles and real return cells. -/
theorem original_prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      10^63*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^10 :=by
  have h:=(machine_prefix_cells bits hc hN fuel cfg hr).trans (polynomial_space bits hc hN)
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  simpa only [hw] using h
end RiemannGaussian.SemiprimeD1StackRootPhaseGridOriginal
