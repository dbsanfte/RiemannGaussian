/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootContextStorage
/-! # Original-input root context for the proved packed first-moment scalar
The entire real root context cache is acquired, including TRUE precision
markers and rank one. The weighted network/counter caller remains a separate
join; no old literal precision-two bank is silently changed or reinterpreted.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackPackedRootContextOriginal
open scoped BigOperators
open SemiprimeD1StackPackedRootContext SemiprimeD1StackPackedRootContextEncoding
open SemiprimeD1StackPackedRootContextExecution SemiprimeD1StackPackedRootContextStorage
open SemiprimeBitArithmetic SemiprimeSourceCompactBits
/-- ALL13 previously acquired metadata words are retained, including N/base/FALSE template. -/
theorem metadata_retained (bits : List Bool) (k : M.Stack) : (done bits).data (metadata k)=M.result bits k := rfl
/-- Original N is physically retained through both source calls. -/
theorem retained_N (bits : List Bool) : (done bits).data originalInput=bits := rfl
/-- The actual acquired context has the literal empty-axis header and the
ACTUALLY copied precision word, with no typed-context input advice. -/
theorem context_inputs (bits : List Bool) :
    (done bits).data (context J.axesCache)=[false] ∧
      (done bits).data (context J.precisionBits)=M.precisionWord bits.length := ⟨rfl,rfl⟩
/-- Actual acquired rank is the one TRUE marker, including at empty input. -/
theorem rank_word (bits : List Bool) : (done bits).data rank=[true] := rfl
/-- TRUE context markers come from the REAL binary-to-unary acquisition;
the retained FALSE fit-template plays no role in this identity. -/
theorem width_word (bits : List Bool) :
    (done bits).data width=List.replicate (2*bits.length) true := by
  change SemiprimeD1StackUnaryCounterExecution.markers (bitValue (M.precisionWord bits.length))=_
  rw [SemiprimeD1StackPackedRootMetadataEncoding.precision_value]
  rfl
/-- Mathematical decoder of the ACTUAL stopped context inputs; it is not an
instruction, evaluator or native operand of the finite program. -/
def acquiredContext (bits : List Bool) : SemiprimeD1JetAxes.Context :=
  ⟨[],bitValue ((done bits).data (context J.precisionBits))⟩
/-- Canonical original N discharges the exact packed precision internally. -/
theorem context_original (bits : List Bool) (hc : Compact bits) :
    acquiredContext bits=⟨[],SemiprimeD1PackedMomentPrecision.precision (bitValue bits)⟩ := by
  unfold acquiredContext
  rw [(context_inputs bits).2,SemiprimeD1StackPackedRootMetadataEncoding.precision_value,
    SemiprimeD1CanonicalInput.compact_length bits hc]
  rfl
/-- The physically acquired TRUE width has the exact original packed precision VALUE. -/
theorem width_original (bits : List Bool) (hc : Compact bits) :
    (done bits).data width=List.replicate (SemiprimeD1PackedMomentPrecision.precision (bitValue bits)) true := by
  rw [width_word,SemiprimeD1CanonicalInput.compact_length bits hc]
  rfl
/-- ACTUAL acquired precision obeys the existing numeric root path budget;
it is not the old literal precision-two special case. -/
theorem actual_precision_guard (bits : List Bool) (hc : Compact bits) (lam : ℕ) :
    bitValue ((done bits).data (context J.precisionBits)) ≤
      SemiprimeD1PrecisionEnvelope.pathCap
        (SemiprimeD1PublicPackingReady.scale (SemiprimeMacroParameters.bitLength (bitValue bits))) lam 0 0 := by
  have hp := congrArg SemiprimeD1JetAxes.Context.precision (context_original bits hc)
  change bitValue ((done bits).data (context J.precisionBits))=SemiprimeD1PackedMomentPrecision.precision (bitValue bits) at hp
  rw [hp]
  exact SemiprimeD1PackedMomentPrecision.root_precision_guard (bitValue bits) lam
/-- Original-N-only exact packed context, within its OWN fixed quadratic clock.
All rank/precision/width/axes data are outputs of real code, not inputs. -/
theorem source_original (bits : List Bool) (hc : Compact bits) :
    ∃t ≤ 2000*(bits.length+1)^2,
      SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) ∧
      (done bits).data originalInput=bits ∧
      acquiredContext bits=⟨[],SemiprimeD1PackedMomentPrecision.precision (bitValue bits)⟩ ∧
      (done bits).data rank=[true] ∧
      (done bits).data width=List.replicate (SemiprimeD1PackedMomentPrecision.precision (bitValue bits)) true := by
  obtain ⟨t,ht,hr⟩ := source_run_bounded bits
  exact ⟨t,ht,hr,retained_N bits,context_original bits hc,rank_word bits,width_original bits hc⟩
/-- Genuine compiled original-N context acquisition with the SAME own quadratic. -/
noncomputable def machineOriginal (bits : List Bool) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (2000*(bits.length+1)^2) := by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect originalInput rank (.inl .start) program
  let h := source_run_bounded bits
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Every compiled N-only prefix pays all28 words, shadows and real returns. -/
theorem original_prefix_cells (bits : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hp : (fun q => q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 1000000*(bits.length+1)^2 :=
  machine_prefix_cells bits fuel cfg hp
end RiemannGaussian.SemiprimeD1StackPackedRootContextOriginal
