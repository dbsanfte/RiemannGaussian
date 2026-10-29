/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootMetadataStorage
import RiemannGaussian.SemiprimeD1PackedMomentPrecision
import RiemannGaussian.SemiprimeD1CanonicalInput
/-! # Original-N-only packed metadata with its own quadratic bit costs
No root-context cache is silently replaced: the larger binary precision and
template are actual NEW outputs, awaiting the generic counter caller join.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPackedRootMetadataOriginal
open SemiprimeD1StackPackedRootMetadata SemiprimeD1StackPackedRootMetadataEncoding
open SemiprimeD1StackPackedRootMetadataExecution SemiprimeD1StackPackedRootMetadataStorage
open SemiprimeBitArithmetic SemiprimeSourceCompactBits
/-- Original binary N remains literally unchanged, including its supplied padding. -/
theorem retained_N (bits : List Bool) : (done bits).data (boot .input)=bits := rfl
/-- The ENTIRE real bootstrap cache is retained by the complete source. -/
theorem retained_bootstrap (bits : List Bool) (k : B.Stack) :
    (done bits).data (boot k)=(B.done bits).store k := rfl
/-- All allocated adder words, including the unused left shadow, are empty at halt. -/
theorem adder_empty (bits : List Bool) (k : A.Stack) : (done bits).data (adderAllocation k)=[] := rfl
/-- Actual binary2ell, actual binaryB and actual2ell-cell template come from
the original canonical word's physically acquired length. -/
theorem metadata_original (bits : List Bool) (hc : Compact bits) :
    bitValue ((done bits).data (aux .precision))=SemiprimeD1PackedMomentPrecision.precision (bitValue bits) ∧
    bitValue ((done bits).data (aux .base))=2^SemiprimeMacroParameters.bitLength (bitValue bits) ∧
    (done bits).data (aux .template)=List.replicate (SemiprimeD1PackedMomentPrecision.precision (bitValue bits)) false := by
  have h := SemiprimeD1CanonicalInput.compact_length bits hc
  constructor
  · change bitValue (precisionWord bits.length)=2*SemiprimeMacroParameters.bitLength (bitValue bits)
    rw [precision_value,h]
  constructor
  · change bitValue (baseWord bits.length)=2^SemiprimeMacroParameters.bitLength (bitValue bits)
    rw [base_value,h]
  · change List.replicate (2*bits.length) false=List.replicate (2*SemiprimeMacroParameters.bitLength (bitValue bits)) false
    rw [h]
/-- Whole source plus original-value meaning in ONE actual bounded execution. -/
theorem source_original (bits : List Bool) (hc : Compact bits) :
    ∃t ≤ 1000*(bits.length+1)^2,
      SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) ∧
      bitValue ((done bits).data (aux .precision))=SemiprimeD1PackedMomentPrecision.precision (bitValue bits) ∧
      bitValue ((done bits).data (aux .base))=2^SemiprimeMacroParameters.bitLength (bitValue bits) ∧
      (done bits).data (aux .template)=List.replicate (SemiprimeD1PackedMomentPrecision.precision (bitValue bits)) false := by
  obtain ⟨t,ht,hr⟩ := source_run_bounded bits
  exact ⟨t,ht,hr,metadata_original bits hc⟩
/-- Genuine compiled original-N source certificate with its OWN quadratic clock. -/
noncomputable def machineOriginal (bits : List Bool) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (1000*(bits.length+1)^2) := by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect (boot .input) (aux .precision) (.local .start) program
  let h := source_run_bounded bits
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- All actual13 data words and genuine return cells remain within the same
fixed quadratic at every original-input machine prefix. -/
theorem original_prefix_cells (bits : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hp : (fun q => q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 100000*(bits.length+1)^2 :=
  machine_prefix_cells bits fuel cfg hp
end RiemannGaussian.SemiprimeD1StackPackedRootMetadataOriginal
