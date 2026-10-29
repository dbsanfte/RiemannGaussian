/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootControllerMetadataBounds

/-! # Exact original root metadata from N alone, with one own polynomial clock
The same acquired occurrence count applies to every original fixed prefix,
including repeated and conflicting prescribed values. Its E wire count stays
separate. All original schedule outputs are physically acquired too; s and
the square-root leaf threshold remain the next acquisition obligation.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackRootControllerMetadataOriginal
open SemiprimeD1StackRootControllerMetadata SemiprimeD1StackRootControllerMetadataExecution
open SemiprimeD1StackRootControllerMetadataBounds
open SemiprimeBitArithmetic (bitValue)
namespace O
export SemiprimeD1StackRootScheduleOriginal (originalLambda)
end O
/-- Every original graph/source/cache cell is retained byte for byte. -/
theorem source_preserved (bits:List Bool) (k:S.Stack) : result bits (sourceStack k)=S.result bits k := rfl
/-- Exact schedule projection, including the original N role shared with the source. -/
theorem schedule_projection (bits:List Bool) (k:R.Stack) : result bits (scheduleStack k)=R.result bits k :=
  payload_schedule (S.result bits) (R.result bits)
    ((source_retained_N bits).trans (SemiprimeD1StackRootScheduleOriginal.input_preserved bits).symm) k
/-- N remains the same binary word; no second initial N payload is introduced. -/
theorem input_preserved (bits:List Bool) : result bits originalInput=bits := source_retained_N bits
/-- The unused private shared-input shadow really stays empty and is still counted. -/
theorem shadow_empty (bits:List Bool) : result bits (.inr (R.boot .input))=[] := by rfl
/-- Actual M word is the original root network edge cardinality, for EVERY fixed prefix. -/
theorem edges_original (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :
    result bits edges=List.replicate (SemiprimeD1TensorNetwork.edgeCount
      (SemiprimeD1RootStateResources.root (bitValue bits) hN fixed)) true := by
  change S.result bits S.count=_
  rw [(SemiprimeD1StackRootScopeBankExecution.result_counts bits).1,
    SemiprimeD1StackRootScopeBankOriginal.occurrence_count bits hN fixed]
/-- The separate E word counts original Boolean wires, never occurrence ordinals. -/
theorem wires_original (bits:List Bool) :
    result bits wires=List.replicate (SemiprimePublicAcquiredExecution.wireCount (bitValue bits)) true := by
  change S.result bits S.wireCount=_
  rw [(SemiprimeD1StackRootScopeBankExecution.result_counts bits).2,
    SemiprimeD1StackRootScopeBankOriginal.wire_count bits]
/-- The two real counters satisfy M=2E; no equality of their identifier domains is asserted. -/
theorem count_lengths (bits:List Bool) : (result bits edges).length=2*(result bits wires).length := by
  change (S.result bits S.count).length=2*(S.result bits S.wireCount).length
  rw [(SemiprimeD1StackRootScopeBankExecution.result_counts bits).1,
    (SemiprimeD1StackRootScopeBankExecution.result_counts bits).2]
  simp only [List.length_replicate,SemiprimeD1StackRootScopeBankExecution.occurrenceCount]
/-- Actual original logarithm from N, without a supplied log or width operand. -/
theorem lambda_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    result bits lambda=List.replicate (O.originalLambda (bitValue bits)) true := by
  change result bits (scheduleStack (R.aux .lambda))=_
  rw [schedule_projection]
  exact SemiprimeD1StackRootScheduleOriginal.lambda_original_word bits hc
/-- Actual original root dyadic level counter. -/
theorem levels_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    result bits levels=List.replicate (SemiprimeD1Schedule.levels (O.originalLambda (bitValue bits)) 0) true := by
  change result bits (scheduleStack (R.aux .levels))=_
  rw [schedule_projection]
  exact SemiprimeD1StackRootScheduleOriginal.levels_original_word bits hc
/-- Actual original root cumulative exponent counter. -/
theorem exponent_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    result bits exponent=List.replicate (SemiprimeD1Schedule.exponent (O.originalLambda (bitValue bits)) 0) true := by
  change result bits (scheduleStack (R.aux .exponent))=_
  rw [schedule_projection]
  exact SemiprimeD1StackRootScheduleOriginal.exponent_original_word bits hc
/-- Actual original minimum-level guard, with both its logarithm and marker writes paid. -/
theorem minimum_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    result bits minimum=List.replicate (SemiprimeD1PrecisionEnvelope.minimumLevels
      (O.originalLambda (bitValue bits))) true := by
  change result bits (scheduleStack (R.aux .minimum))=_
  rw [schedule_projection]
  exact SemiprimeD1StackRootScheduleOriginal.minimum_original_word bits hc
/-- Actual canonical original-input width is retained for scale acquisition. -/
theorem width_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) :
    result bits (scheduleStack (R.boot .width))=List.replicate
      (SemiprimeMacroParameters.bitLength (bitValue bits)) true := by
  rw [schedule_projection]
  exact SemiprimeD1StackRootScheduleOriginal.retained_width bits hc
/-- One actual run and all original output correspondences hold simultaneously for every N. -/
theorem source_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t≤10^50*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^10,
      SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) ∧
      (∀fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool),
        result bits edges=List.replicate (SemiprimeD1TensorNetwork.edgeCount
          (SemiprimeD1RootStateResources.root (bitValue bits) hN fixed)) true) ∧
      result bits lambda=List.replicate (O.originalLambda (bitValue bits)) true ∧
      result bits levels=List.replicate (SemiprimeD1Schedule.levels (O.originalLambda (bitValue bits)) 0) true ∧
      result bits exponent=List.replicate (SemiprimeD1Schedule.exponent (O.originalLambda (bitValue bits)) 0) true ∧
      result bits minimum=List.replicate (SemiprimeD1PrecisionEnvelope.minimumLevels
        (O.originalLambda (bitValue bits))) true ∧ result bits originalInput=bits := by
  obtain ⟨t,ht,hr⟩:=source_run_polynomial bits hc hN
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  refine ⟨t,?_,hr,edges_original bits hN,lambda_original bits hc,levels_original bits hc,
    exponent_original bits hc,minimum_original bits hc,input_preserved bits⟩
  simpa only [hw] using ht
/-- Genuine N-only finite-machine acquisition under that same whole original-bitlength clock. -/
noncomputable def originalInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits)))
      (10^50*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^10) := by
  have h:=acquireInTime bits hc hN
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  simpa only [hw] using h
/-- Every original-N prefix pays ALL98 roles, shared-input shadow and actual return cells. -/
theorem original_prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      10^53*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^10 := by
  have h:=(machine_prefix_cells bits hc hN fuel cfg hr).trans (polynomial_space bits)
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  simpa only [hw] using h
end RiemannGaussian.SemiprimeD1StackRootControllerMetadataOriginal
